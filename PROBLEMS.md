# FormalQualBench: curated research theorem list

This catalog is intentionally **research-level** (no IMO/Putnam/etc.). It mainly focuses on
theorem statements for *proven* results in the literature that are not currently available as a
finished Lean/Mathlib theorem, with the benchmark surface intended to stay on mathematically
established results rather than unsolved conjectures.

Each checked item corresponds to a single Lean stub at `FormalQualBench/<Name>/Main.lean`
containing only the necessary definitions/imports + a main statement with a `by sorry` proof.

## Curation signals

- Mathlib `proof_wanted` declarations (known results with missing proofs in Lean)
- Famous results whose statements can be expressed using existing Mathlib definitions (even if the proof is far out of reach)

## Current problems

### Topology / geometry

- [x] Borsuk–Ulam theorem (`FormalQualBench/BorsukUlamTheorem/Main.lean`)

### Topology / geometric functional analysis

- [x] Banach–Stone theorem (`FormalQualBench/BanachStoneTheorem/Main.lean`)

### Logic / model theory

- [x] Quantifier elimination for dense linear orders without endpoints (DLO) (`FormalQualBench/DLOQuantifierElimination/Main.lean`)

### Logic / Ramsey theory

- [x] Paris-Harrington principle (strengthened finite Ramsey theorem) (`FormalQualBench/ParisHarringtonPrinciple/Main.lean`)

### Number theory

- [x] Maynard-Tao bounded prime gaps theorem (`FormalQualBench/MaynardTaoBoundedPrimeGaps/Main.lean`)
- [x] Helfgott's ternary Goldbach theorem (`FormalQualBench/TernaryGoldbachTheorem/Main.lean`)

### Algebra / group theory

- [x] Jordan theorem: primitive groups containing a prime cycle contain `Aₙ` (`FormalQualBench/JordanCycleTheorem/Main.lean`)
- [x] Jordan derangement theorem for finite transitive permutation groups (`FormalQualBench/JordanDerangementTheorem/Main.lean`)
- [x] Burnside theorem for permutation groups of prime degree (`FormalQualBench/BurnsidePrimeDegreeTheorem/Main.lean`)

### Algebra / commutative algebra

- [x] Quillen–Suslin theorem (Serre’s conjecture) (`FormalQualBench/QuillenSuslinTheorem/Main.lean`)

### Algebra / real algebraic geometry

- [x] Artin’s solution to Hilbert’s 17th problem (`FormalQualBench/Hilbert17thProblem/Main.lean`)

### Analysis / complex analysis

- [x] Gleason-Kahane-Zelazko theorem (`FormalQualBench/GleasonKahaneZelazkoTheorem/Main.lean`)
- [x] Runge’s theorem (polynomial approximation on compact sets) (`FormalQualBench/RungeTheorem/Main.lean`)

### Additive combinatorics / analytic number theory

- [x] Tao's solution of the Erdős discrepancy problem (`FormalQualBench/ErdosDiscrepancyProblem/Main.lean`)
- [x] Green-Tao theorem on arithmetic progressions in the primes (`FormalQualBench/GreenTaoTheorem/Main.lean`)

### Analysis / operator algebras

- [x] von Neumann double commutant theorem (`FormalQualBench/VonNeumannDoubleCommutantTheorem/Main.lean`)

### Topological groups / harmonic analysis

- [x] Pontryagin duality via the canonical evaluation map (`FormalQualBench/PontryaginDuality/Main.lean`)

### Combinatorics / graph theory

- [x] De Bruijn–Erdős theorem (compactness for graph coloring) (`FormalQualBench/DeBruijnErdos/Main.lean`)

### Combinatorial / convex geometry

- [x] Colorful Carathéodory theorem (`FormalQualBench/ColorfulCaratheodoryTheorem/Main.lean`)

### Harmonic analysis / geometric measure theory

- [x] Three-dimensional Kakeya theorem (`FormalQualBench/KakeyaTheorem3D/Main.lean`)

### Analysis / fixed point theory

- [x] Schauder fixed point theorem (`FormalQualBench/SchauderFixedPointTheorem/Main.lean`)

### Arithmetic dynamics / recurrence sequences

- [x] Skolem-Mahler-Lech theorem (`FormalQualBench/SkolemMahlerLechTheorem/Main.lean`)

### Dynamical systems / arithmetic

- [x] Almost-bounded values for the Collatz map (`FormalQualBench/CollatzMapAlmostBoundedValues/Main.lean`)
