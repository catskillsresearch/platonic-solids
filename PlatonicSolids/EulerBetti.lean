/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
Paper §2.1 / §3.1. Betti arithmetic of χ(S²) and χ(S³).

Mathlib does not identify a convex polyhedron with a CW structure on
`Metric.sphere`, so Euler–Poincaré (`V - E + F = 2`) remains an input to
`platonic_solids_3d`. These lemmas record the homology calculation the
paper uses to justify that input, and the vanishing that blocks a 4D bound.
-/

/-- χ(S²) = b₀ - b₁ + b₂ = 1 - 0 + 1. -/
lemma eulerChar_sphere2_betti : (1 : ℤ) - 0 + 1 = 2 := by norm_num

/-- χ(S³) = b₀ - b₁ + b₂ - b₃ = 1 - 0 + 0 - 1. -/
lemma eulerChar_sphere3_betti : (1 : ℤ) - 0 + 0 - 1 = 0 := by norm_num
