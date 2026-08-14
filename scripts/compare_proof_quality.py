#!/usr/bin/env python3
"""Compare Lean proof-engineering metrics across two FormalQualBench checkouts.

The script is intentionally descriptive rather than prescriptive: it records
objective source/blueprint metrics, but does not collapse them into a single
"quality score" or automatically declare a winner.

Default comparison set:
  DeBruijnErdos
  JordanDerangementTheorem
  ParisHarringtonPrinciple
  ColorfulCaratheodoryTheorem
  BanachStoneTheorem
  VonNeumannDoubleCommutantTheorem

Typical use (run from the FormalQualBench checkout, with the OpenGauss checkout
as a sibling directory):

  python3 scripts/compare_proof_quality.py

Explicit paths:

  python3 scripts/compare_proof_quality.py \
    --repo-a /path/to/FormalQualBench \
    --repo-b /path/to/FormalQualBench-opengauss

The script writes CSV, JSON, and Markdown reports to ./proof_evaluation by
default. Pass --skip-axioms to avoid invoking Lean for `#print axioms` checks.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import tempfile
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


DEFAULT_THEOREMS = [
    "DeBruijnErdos",
    "JordanDerangementTheorem",
    "ParisHarringtonPrinciple",
    "ColorfulCaratheodoryTheorem",
    "BanachStoneTheorem",
    "VonNeumannDoubleCommutantTheorem",
]

BLUEPRINT_FILES = {
    "DeBruijnErdos": "debruijn_erdos.tex",
    "JordanDerangementTheorem": "jordan_derangement.tex",
    "ParisHarringtonPrinciple": "paris_harrington.tex",
    "ColorfulCaratheodoryTheorem": "colorful_caratheodory.tex",
    "BanachStoneTheorem": "banach_stone.tex",
    "VonNeumannDoubleCommutantTheorem": "von_neumann_double_commutant.tex",
}

TACTICS = [
    "simp",
    "simp_rw",
    "aesop",
    "omega",
    "linarith",
    "nlinarith",
    "ring",
    "ring_nf",
    "norm_num",
    "native_decide",
    "decide",
]

DECL_KINDS = r"def|abbrev|lemma|theorem|proposition|corollary|structure|class|inductive"
DECL_RE = re.compile(
    rf"(?m)^\s*(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:{DECL_KINDS})\s+([A-Za-z0-9_'.]+)"
)
IMPORT_RE = re.compile(r"(?m)^\s*import\s+([^\s]+)\s*$")
HEARTBEAT_RE = re.compile(r"set_option\s+maxHeartbeats\s+(\d+)")
LEAN_RE = re.compile(r"\\lean\{([^}]*)\}")
ENV_RE = re.compile(
    r"\\begin\{(?:definition|lemma|proposition|theorem|corollary)\}(.*?)"
    r"\\end\{(?:definition|lemma|proposition|theorem|corollary)\}",
    re.DOTALL,
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
USES_RE = re.compile(r"\\uses\{([^}]+)\}")


@dataclass
class Metrics:
    repo: str
    theorem: str
    source_path: str
    blueprint_path: str
    source_loc: int
    code_loc: int
    main_proof_loc: int
    direct_imports: int
    import_modules: list[str]
    top_level_declarations: int
    top_level_declaration_names: list[str]
    blueprint_declarations: int
    blueprint_declaration_names: list[str]
    blueprint_edges: int
    blueprint_max_depth: int
    sorry_tokens: int
    main_theorem_sorryax: str
    max_heartbeats_overrides: list[int]
    tactic_counts: dict[str, int]


def strip_comments(text: str) -> str:
    """Remove Lean line comments and nested block comments, preserving newlines."""
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
            continue
        ch = text[i]
        if depth > 0:
            out.append("\n" if ch == "\n" else " ")
        else:
            out.append(ch)
        i += 1
    return "".join(out)


def count_nonblank_lines(text: str) -> int:
    return sum(1 for line in text.splitlines() if line.strip())


def main_proof_loc(code: str) -> int:
    """Count nonblank lines in the proof body of `MainTheorem`.

    This is a source-level approximation. It starts after the first `:= by`
    (or `=> by`) belonging to MainTheorem and ends at the next namespace `end`
    or EOF. In these benchmark files MainTheorem is conventionally the final
    declaration, which makes the measure stable and easy to reproduce.
    """
    m = re.search(r"\btheorem\s+MainTheorem\b", code)
    if not m:
        return 0
    tail = code[m.end() :]
    p = re.search(r"(?::=|=>)\s*by\b", tail)
    if not p:
        return 0
    body = tail[p.end() :]
    end = re.search(r"(?m)^\s*end(?:\s+[A-Za-z0-9_'.]+)?\s*$", body)
    if end:
        body = body[: end.start()]
    return count_nonblank_lines(body)


def tactic_counts(code: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for tactic in TACTICS:
        counts[tactic] = len(re.findall(rf"(?<![A-Za-z0-9_']){re.escape(tactic)}(?![A-Za-z0-9_'])", code))
    return counts


def parse_blueprint(tex: str) -> tuple[list[str], int, int]:
    declarations: list[str] = []
    for match in LEAN_RE.finditer(tex):
        declarations.extend(x.strip() for x in match.group(1).split(",") if x.strip())
    declarations = sorted(set(declarations))

    graph: dict[str, set[str]] = {}
    edges = 0
    for env in ENV_RE.finditer(tex):
        body = env.group(1)
        label_match = LABEL_RE.search(body)
        if not label_match:
            continue
        label = label_match.group(1)
        graph.setdefault(label, set())
        for use_match in USES_RE.finditer(body):
            for dep in use_match.group(1).split(","):
                dep = dep.strip()
                if dep:
                    graph[label].add(dep)
                    edges += 1

    memo: dict[str, int] = {}
    visiting: set[str] = set()

    def depth(node: str) -> int:
        if node in memo:
            return memo[node]
        if node in visiting:
            # A malformed cyclic blueprint should not crash the evaluator.
            return 0
        visiting.add(node)
        deps = graph.get(node, set())
        value = 0 if not deps else 1 + max(depth(dep) for dep in deps)
        visiting.remove(node)
        memo[node] = value
        return value

    max_depth = max((depth(node) for node in graph), default=0)
    return declarations, edges, max_depth


def check_axioms(repo: Path, theorem: str) -> str:
    """Return `clean`, `sorryAx`, or `unavailable` for MainTheorem."""
    module = f"FormalQualBench.{theorem}.Main"
    decl = f"{theorem}.MainTheorem"
    source = f"import {module}\n#print axioms {decl}\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8") as fh:
        fh.write(source)
        tmp = Path(fh.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            cwd=repo,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=300,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return "unavailable"
    finally:
        tmp.unlink(missing_ok=True)

    if proc.returncode != 0:
        return "unavailable"
    return "sorryAx" if re.search(r"\bsorryAx\b", proc.stdout) else "clean"


def collect_metrics(repo: Path, repo_label: str, theorem: str, do_axioms: bool) -> Metrics:
    source = repo / "FormalQualBench" / theorem / "Main.lean"
    if not source.exists():
        raise FileNotFoundError(f"Missing Lean source: {source}")

    blueprint_name = BLUEPRINT_FILES.get(theorem)
    if blueprint_name is None:
        raise KeyError(f"No blueprint filename registered for {theorem}")
    blueprint = repo / "blueprint" / "src" / "theorems" / blueprint_name
    if not blueprint.exists():
        raise FileNotFoundError(f"Missing blueprint source: {blueprint}")

    raw = source.read_text(encoding="utf-8")
    code = strip_comments(raw)
    tex = blueprint.read_text(encoding="utf-8")

    decl_names = DECL_RE.findall(code)
    bp_decls, bp_edges, bp_depth = parse_blueprint(tex)
    imports = IMPORT_RE.findall(code)
    heartbeats = [int(x) for x in HEARTBEAT_RE.findall(code)]

    # Match source-level `sorry` only; `sorryAx` is checked transitively below.
    sorry_count = len(re.findall(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])", code))

    return Metrics(
        repo=repo_label,
        theorem=theorem,
        source_path=str(source),
        blueprint_path=str(blueprint),
        source_loc=count_nonblank_lines(raw),
        code_loc=count_nonblank_lines(code),
        main_proof_loc=main_proof_loc(code),
        direct_imports=len(imports),
        import_modules=imports,
        top_level_declarations=len(decl_names),
        top_level_declaration_names=decl_names,
        blueprint_declarations=len(bp_decls),
        blueprint_declaration_names=bp_decls,
        blueprint_edges=bp_edges,
        blueprint_max_depth=bp_depth,
        sorry_tokens=sorry_count,
        main_theorem_sorryax=check_axioms(repo, theorem) if do_axioms else "skipped",
        max_heartbeats_overrides=heartbeats,
        tactic_counts=tactic_counts(code),
    )


def flatten(m: Metrics) -> dict[str, object]:
    d = asdict(m)
    d["import_modules"] = "; ".join(m.import_modules)
    d["top_level_declaration_names"] = "; ".join(m.top_level_declaration_names)
    d["blueprint_declaration_names"] = "; ".join(m.blueprint_declaration_names)
    d["max_heartbeats_overrides"] = "; ".join(str(x) for x in m.max_heartbeats_overrides)
    tactics = d.pop("tactic_counts")
    for tactic in TACTICS:
        d[f"tactic_{tactic}"] = tactics[tactic]
    return d


def markdown_table(metrics: Iterable[Metrics]) -> str:
    rows = list(metrics)
    lines = [
        "# Paired Lean proof-engineering evaluation",
        "",
        "Correctness/completeness should be treated as a gate. The table below contains descriptive metrics only; lower or higher values are not automatically better.",
        "",
        "| Theorem | Repo | Code LOC | Main proof LOC | Imports | Top-level decls | Blueprint decls | BP edges | BP depth | source `sorry` | Main `sorryAx` | maxHeartbeats |",
        "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---|---|",
    ]
    for m in rows:
        hb = ", ".join(map(str, m.max_heartbeats_overrides)) or "—"
        lines.append(
            f"| {m.theorem} | {m.repo} | {m.code_loc} | {m.main_proof_loc} | "
            f"{m.direct_imports} | {m.top_level_declarations} | {m.blueprint_declarations} | "
            f"{m.blueprint_edges} | {m.blueprint_max_depth} | {m.sorry_tokens} | "
            f"{m.main_theorem_sorryax} | {hb} |"
        )

    lines.extend([
        "",
        "## Tactic-token counts",
        "",
        "These are lexical counts in comment-stripped Lean source, not semantic tactic invocations.",
        "",
        "| Theorem | Repo | " + " | ".join(TACTICS) + " |",
        "|---|---|" + "|".join(["---:"] * len(TACTICS)) + "|",
    ])
    for m in rows:
        lines.append(
            f"| {m.theorem} | {m.repo} | "
            + " | ".join(str(m.tactic_counts[t]) for t in TACTICS)
            + " |"
        )

    lines.extend([
        "",
        "## Interpretation notes",
        "",
        "- `Code LOC` removes Lean line/block comments and blank lines.",
        "- `Main proof LOC` is the nonblank source span after `MainTheorem := by` until the final namespace `end`.",
        "- `Top-level decls` counts source-level definitions/theorems/lemmas/structures/etc. in `Main.lean`.",
        "- `Blueprint decls` counts unique names appearing in `\\lean{...}` in the theorem blueprint.",
        "- `BP depth` is the maximum number of `\\uses` dependency edges on a path. A standalone theorem has depth 0.",
        "- `Main sorryAx` is obtained from Lean's `#print axioms`; `clean` means no transitive `sorryAx` was reported. `unavailable` means the Lean check could not be run successfully.",
        "- Import count is only the number of direct `import` statements in the file, not the transitive dependency closure.",
        "- These metrics should be paired with human judgments of mathematical faithfulness, abstraction quality, generality, reuse, readability, and maintainability.",
    ])
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-a", type=Path, default=Path("."), help="first repository checkout")
    parser.add_argument(
        "--repo-b",
        type=Path,
        default=Path("../FormalQualBench-opengauss"),
        help="second repository checkout",
    )
    parser.add_argument("--label-a", default="FormalQualBench")
    parser.add_argument("--label-b", default="FormalQualBench-opengauss")
    parser.add_argument("--theorems", nargs="*", default=DEFAULT_THEOREMS)
    parser.add_argument("--out-dir", type=Path, default=Path("proof_evaluation"))
    parser.add_argument(
        "--skip-axioms",
        action="store_true",
        help="skip Lean #print axioms checks (faster; records 'skipped')",
    )
    args = parser.parse_args()

    repo_a = args.repo_a.resolve()
    repo_b = args.repo_b.resolve()
    out_dir = args.out_dir.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    all_metrics: list[Metrics] = []
    for theorem in args.theorems:
        all_metrics.append(collect_metrics(repo_a, args.label_a, theorem, not args.skip_axioms))
        all_metrics.append(collect_metrics(repo_b, args.label_b, theorem, not args.skip_axioms))

    flat = [flatten(m) for m in all_metrics]
    csv_path = out_dir / "proof_comparison.csv"
    json_path = out_dir / "proof_comparison.json"
    md_path = out_dir / "proof_comparison.md"

    with csv_path.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(flat[0].keys()))
        writer.writeheader()
        writer.writerows(flat)

    json_path.write_text(json.dumps([asdict(m) for m in all_metrics], indent=2) + "\n", encoding="utf-8")
    md_path.write_text(markdown_table(all_metrics), encoding="utf-8")

    print(markdown_table(all_metrics))
    print(f"Wrote {csv_path}")
    print(f"Wrote {json_path}")
    print(f"Wrote {md_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
