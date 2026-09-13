/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
Paper §3.2. The Schläfli Gram matrix of `{p, q, r}` and the scalar
`Δ(p, q, r)` that will equal its determinant.
-/

open scoped Matrix
open Real Matrix

/-- Canonical bilinear form of the rank-4 Schläfli Coxeter system `{p, q, r}`. -/
noncomputable def schlafliGram (p q r : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, -cos (π / p), 0, 0;
     -cos (π / p), 1, -cos (π / q), 0;
     0, -cos (π / q), 1, -cos (π / r);
     0, 0, -cos (π / r), 1]

/-- `Δ(p, q, r) = sin²(π/p) sin²(π/r) - cos²(π/q)`. -/
noncomputable def schlafliDet (p q r : ℕ) : ℝ :=
  sin (π / p) ^ 2 * sin (π / r) ^ 2 - cos (π / q) ^ 2

lemma schlafliGram_isHermitian (p q r : ℕ) : (schlafliGram p q r).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [schlafliGram, conjTranspose]
