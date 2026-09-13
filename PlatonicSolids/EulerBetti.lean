/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
Paper §2.1 / §3.1. Betti arithmetic of χ(S²) and χ(S³).

The algebraic Euler–Poincaré identities are `euler_poincare` and
`euler_poincare3` in `PlatonicSolids/EulerPoincare.lean`. The numbers
`b₀ = 1`, `b₁ = 0`, `b₂ = 1` for the standard simplicial `S²` are
`homology_sphere2`; the numbers `b₀ = 1`, `b₁ = 0`, `b₂ = 0`,
`b₃ = 1` for the standard simplicial `S³` are `homology_sphere3`.
Singular `H₀` of `Metric.sphere` in dimension `n ≥ 1` and the full
calculation of `H_*(S⁰)` are in `PlatonicSolids/SingularHomology.lean`.
These lemmas record the resulting `χ(S²) = 2` and `χ(S³) = 0`.
-/

/-- χ(S²) = b₀ - b₁ + b₂ = 1 - 0 + 1. -/
lemma eulerChar_sphere2_betti : (1 : ℤ) - 0 + 1 = 2 := by norm_num

/-- χ(S³) = b₀ - b₁ + b₂ - b₃ = 1 - 0 + 0 - 1. -/
lemma eulerChar_sphere3_betti : (1 : ℤ) - 0 + 0 - 1 = 0 := by norm_num
