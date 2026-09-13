/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PlatonicSolids.GramMatrix

/-!
Paper §3.3. The quadratic form of the Schläfli Gram matrix.
-/

open scoped Matrix
open Real Matrix

private lemma sum_fin4 (f : Fin 4 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp
  abel

lemma schlafliGram_quad (p q r : ℕ) (x : Fin 4 → ℝ) :
    star x ⬝ᵥ (schlafliGram p q r *ᵥ x) =
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2
      - 2 * cos (π / p) * x 0 * x 1
      - 2 * cos (π / q) * x 1 * x 2
      - 2 * cos (π / r) * x 2 * x 3 := by
  simp [schlafliGram, dotProduct, mulVec, sum_fin4]
  ring
