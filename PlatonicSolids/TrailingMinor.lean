/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import PlatonicSolids.GramMatrix

/-!
Paper §3.3. The trailing 3×3 principal minor is the cell minor of the
vertex figure `{q, r}`.
-/

open scoped Matrix
open Real Matrix

noncomputable def trailing3 (p q r : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (schlafliGram p q r).submatrix (fun i : Fin 3 => i.succ) (fun i => i.succ)

lemma trailing3_det (p q r : ℕ) :
    (trailing3 p q r).det = sin (π / q) ^ 2 - cos (π / r) ^ 2 := by
  simp [trailing3, schlafliGram, det_fin_three]
  linarith [sin_sq_add_cos_sq (π / q)]
