/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import PlatonicSolids.GramMatrix

/-!
Paper §3.3–3.4. Leading principal minors `D₁`, `D₂`, `D₃` of the Gram
matrix, matching the paper's closed forms.
-/

open scoped Matrix
open Real Matrix

def leadingSubmatrix (k : ℕ) (hk : k ≤ 4) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

noncomputable def leadingMinor (k : ℕ) (hk : k ≤ 4) (p q r : ℕ) : ℝ :=
  (leadingSubmatrix k hk (schlafliGram p q r)).det

lemma leadingMinor_one (p q r : ℕ) : leadingMinor 1 (by decide) p q r = 1 := by
  simp [leadingMinor, leadingSubmatrix, schlafliGram]

lemma leadingMinor_two (p q r : ℕ) :
    leadingMinor 2 (by decide) p q r = sin (π / p) ^ 2 := by
  simp [leadingMinor, leadingSubmatrix, schlafliGram, det_fin_two]
  linarith [sin_sq_add_cos_sq (π / p)]

lemma leadingMinor_three (p q r : ℕ) :
    leadingMinor 3 (by decide) p q r = sin (π / p) ^ 2 - cos (π / q) ^ 2 := by
  simp [leadingMinor, leadingSubmatrix, schlafliGram, det_fin_three]
  linarith [sin_sq_add_cos_sq (π / p)]
