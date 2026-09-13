/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import PlatonicSolids.GramMatrix

/-!
Paper §3.4. The determinant of the rank-4 Schläfli Gram matrix is
`Δ = sin²(π/p) sin²(π/r) - cos²(π/q)`.
-/

open scoped Matrix
open Real Matrix

private lemma sum_fin4 (f : Fin 4 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp
  abel

/-- Determinant of the tridiagonal Gram pattern. -/
lemma det_band (a b c : ℝ) :
    (!![1, a, 0, 0;
        a, 1, b, 0;
        0, b, 1, c;
        0, 0, c, 1] : Matrix (Fin 4) (Fin 4) ℝ).det =
      (1 - a ^ 2) * (1 - c ^ 2) - b ^ 2 := by
  rw [det_succ_row_zero, sum_fin4]
  simp [det_fin_three, Fin.succAbove]
  ring

lemma schlafliGram_det (p q r : ℕ) :
    (schlafliGram p q r).det = schlafliDet p q r := by
  unfold schlafliGram schlafliDet
  rw [det_band]
  have hp : 1 - (-cos (π / p)) ^ 2 = sin (π / p) ^ 2 := by linarith [sin_sq_add_cos_sq (π / p)]
  have hr : 1 - (-cos (π / r)) ^ 2 = sin (π / r) ^ 2 := by linarith [sin_sq_add_cos_sq (π / r)]
  rw [hp, hr]
  ring

lemma leadingMinor_four (p q r : ℕ) :
    (schlafliGram p q r).det = schlafliDet p q r :=
  schlafliGram_det p q r
