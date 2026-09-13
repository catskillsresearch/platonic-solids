/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
Paper §2.1 / §3.1. Betti arithmetic of χ(S²) and χ(S³).

The algebraic Euler–Poincaré identity (cell ranks equal Betti ranks)
is `euler_poincare` in `PlatonicSolids/EulerPoincare.lean`. These
lemmas record the numerical values of `χ(S²)` and `χ(S³)` that the
paper uses: Mathlib does not yet compute singular homology of spheres,
so those Betti numbers remain an input to `euler_formula_of_sphere2`.
The 3D vanishing `χ(S³) = 0` is why topology supplies no 4D bound.
-/

/-- χ(S²) = b₀ - b₁ + b₂ = 1 - 0 + 1. -/
lemma eulerChar_sphere2_betti : (1 : ℤ) - 0 + 1 = 2 := by norm_num

/-- χ(S³) = b₀ - b₁ + b₂ - b₃ = 1 - 0 + 0 - 1. -/
lemma eulerChar_sphere3_betti : (1 : ℤ) - 0 + 0 - 1 = 0 := by norm_num
