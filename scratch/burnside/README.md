# Burnside prime-degree — rescued scratch files

Working files written by the autoprove agent to `/tmp` on the compute node
during two runs. `/tmp` is node-local and not backed up, so these were copied
into the repo before the node's allocation ended. They are **drafts**, kept for
provenance; nothing here is imported by any `lean_lib` target and none of it is
built by `lake build`.

## 2026-08-06 run (job 60098, fugu-ultra-v1.1)

Drafts of the files the agent itself committed in `e9ea4c5`
(`build Burnside prime-degree auxiliary core`, +439 lines). Kept because they
show the iteration, but they are near-identical to what was committed:

| scratch file | committed as | differing lines |
|---|---|---|
| `BurnsideGroupScratch.lean` | `Auxiliary/TauOrbitEquiv.lean` | 0 |
| `BurnsideMuellerScratch.lean` | `Auxiliary/AffinePermOfDifferenceSetPreserving.lean` | 4 |
| `BurnsideDifferenceScratch.lean` | `Auxiliary/DifferenceSetData.lean` | 7 |

## 2026-07-30 run (ended by a usage cap)

479-line Aristotle-route attempts, each still carrying 1 `sorry`. This route was
never committed to the theorem directory, so unlike the 08-06 set these are the
only surviving copies.

`BurnsideAristotleCheck.lean`, `BurnsideDriveFresh.lean` and
`BurnsidePrimeDegreeTheorem_aristotle.lean` are byte-identical to each other
(md5 `4fa636329cce05628a0983dd87a8b9f2`); all three are kept so the filenames the
agent used are preserved. `BurnsideAristotleWork.lean` differs.

None of these files is known to compile.
