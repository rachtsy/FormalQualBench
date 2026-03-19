# FormalQualBench

`FormalQualBench` is a Lean 4 + Mathlib benchmark focused on **math PhD qualifying exam-level theorem
statements**. Our benchmark enables practitioners to rapidly iterate on and evaluate agent design decisions in practical formalization workflows. 

The core artifact is a large collection of small Lean modules containing:
- the necessary definitions to state a result, and
- a single main theorem statement with a `by sorry` placeholder (no proofs).

We expect this benchmark to approach saturation within a few months as frontier autoformalization systems improve.

## Catalog

See `PROBLEMS.md` for the curated research problem list.

## Layout

- Each problem lives at `FormalQualBench/<ProblemName>/Main.lean`.
- The library entrypoint is `FormalQualBench.lean` (via `FormalQualBench/Basic.lean`).

## Build

Run `lake build`.

## Comparator

All proofs should be checked with [leanprover/comparator](https://github.com/leanprover/comparator) + [landrun](https://github.com/Zouuup/landrun).

Minimal setup instructions:

```bash
# Setup (once)
git clone --depth=1 -b v4.28.0 https://github.com/leanprover/comparator.git
cd comparator && lake build comparator @lean4export && cd ..
curl -LsSf https://github.com/Zouuup/landrun/releases/download/v0.1.14/landrun-linux-amd64 \
  -o /usr/local/bin/landrun && chmod +x /usr/local/bin/landrun
```

Write your proof in `Solution.lean`, copy the original stub to `Challenge.lean`, then:

```bash
export PATH="comparator/.lake/packages/lean4export/.lake/build/bin:$PATH"
lake env comparator/.lake/build/bin/comparator config.json  # exit 0 = valid
```

`config.json`:
```json
{"challenge_module":"Challenge","solution_module":"Solution",
 "theorem_names":["DeBruijnErdos.MainTheorem"],
 "permitted_axioms":["propext","Quot.sound","Classical.choice"],
 "enable_nanoda":false}
```
