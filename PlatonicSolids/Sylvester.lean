/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import PlatonicSolids.CompletingSquare
import PlatonicSolids.DetFormula
import PlatonicSolids.LeadingMinors
import PlatonicSolids.QuadForm

/-!
Paper §3.3. Sylvester's criterion for the Schläfli Gram matrix:
positive-definite iff the four leading principal minors are positive.
`PosDef →` minors uses Mathlib (`PosDef.submatrix`, `PosDef.det_pos`);
the converse is the completing-the-square identity.
-/

open scoped Matrix
open Real Matrix

lemma leadingMinors_pos_of_posDef {p q r : ℕ} (h : (schlafliGram p q r).PosDef) :
    0 < leadingMinor 1 (by decide) p q r ∧
    0 < leadingMinor 2 (by decide) p q r ∧
    0 < leadingMinor 3 (by decide) p q r ∧
    0 < (schlafliGram p q r).det := by
  have h1 := h.submatrix (Fin.castLE_injective (by decide : 1 ≤ 4))
  have h2 := h.submatrix (Fin.castLE_injective (by decide : 2 ≤ 4))
  have h3 := h.submatrix (Fin.castLE_injective (by decide : 3 ≤ 4))
  refine ⟨?_, ?_, ?_, PosDef.det_pos h⟩
  · simpa [leadingMinor, leadingSubmatrix] using PosDef.det_pos h1
  · simpa [leadingMinor, leadingSubmatrix] using PosDef.det_pos h2
  · simpa [leadingMinor, leadingSubmatrix] using PosDef.det_pos h3

/-- Converse Sylvester for this Gram family: positive leading minors ⇒ `PosDef`. -/
theorem schlafliGram_posDef_of_minors {p q r : ℕ}
    (h1 : 0 < leadingMinor 1 (by decide) p q r)
    (h2 : 0 < leadingMinor 2 (by decide) p q r)
    (h3 : 0 < leadingMinor 3 (by decide) p q r)
    (h4 : 0 < (schlafliGram p q r).det) :
    (schlafliGram p q r).PosDef := by
  have hD1 : leadingMinor 1 (by decide) p q r = 1 := leadingMinor_one p q r
  have : (0 : ℝ) < 1 := hD1 ▸ h1
  clear this
  refine posDef_iff_dotProduct_mulVec.mpr ⟨schlafliGram_isHermitian p q r, ?_⟩
  intro x hx
  set α := -cos (π / p)
  set β := -cos (π / q)
  set γ := -cos (π / r)
  have hα : 1 - α ^ 2 = sin (π / p) ^ 2 := by
    simp [α]; linarith [sin_sq_add_cos_sq (π / p)]
  have hβ : 1 - α ^ 2 - β ^ 2 = sin (π / p) ^ 2 - cos (π / q) ^ 2 := by
    simp [α, β]; linarith [sin_sq_add_cos_sq (π / p)]
  have hD2 : leadingMinor 2 (by decide) p q r = sin (π / p) ^ 2 := leadingMinor_two p q r
  have hD3 : leadingMinor 3 (by decide) p q r =
      sin (π / p) ^ 2 - cos (π / q) ^ 2 := leadingMinor_three p q r
  have h2ne : 1 - α ^ 2 ≠ 0 := by
    rw [hα]; exact ne_of_gt (hD2 ▸ h2)
  have h3ne : 1 - α ^ 2 - β ^ 2 ≠ 0 := by
    rw [hβ]; exact ne_of_gt (hD3 ▸ h3)
  have hc1 : 0 < 1 - α ^ 2 := by rw [hα]; exact hD2 ▸ h2
  have hc2 : 0 < 1 - α ^ 2 - β ^ 2 := by rw [hβ]; exact hD3 ▸ h3
  have hγ : 1 - γ ^ 2 = sin (π / r) ^ 2 := by
    simp [γ]; linarith [sin_sq_add_cos_sq (π / r)]
  have hc3 : 0 < 1 - α ^ 2 - β ^ 2 - γ ^ 2 * (1 - α ^ 2) := by
    have : 1 - α ^ 2 - β ^ 2 - γ ^ 2 * (1 - α ^ 2) =
        (1 - α ^ 2) * (1 - γ ^ 2) - β ^ 2 := by ring
    rw [this, hα, hγ]
    have hβsq : β ^ 2 = cos (π / q) ^ 2 := by simp [β]
    rw [hβsq]
    have hdet : sin (π / p) ^ 2 * sin (π / r) ^ 2 - cos (π / q) ^ 2 =
        (schlafliGram p q r).det := by
      rw [schlafliGram_det, schlafliDet]
    rw [hdet]
    exact h4
  have hQ : star x ⬝ᵥ (schlafliGram p q r *ᵥ x) =
      (x 0 + α * x 1) ^ 2
      + (1 - α ^ 2) * (x 1 + β / (1 - α ^ 2) * x 2) ^ 2
      + ((1 - α ^ 2 - β ^ 2) / (1 - α ^ 2)) *
          (x 2 + γ * (1 - α ^ 2) / (1 - α ^ 2 - β ^ 2) * x 3) ^ 2
      + ((1 - α ^ 2 - β ^ 2 - γ ^ 2 * (1 - α ^ 2)) / (1 - α ^ 2 - β ^ 2)) *
          x 3 ^ 2 := by
    calc star x ⬝ᵥ (schlafliGram p q r *ᵥ x)
        = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2
            - 2 * cos (π / p) * x 0 * x 1
            - 2 * cos (π / q) * x 1 * x 2
            - 2 * cos (π / r) * x 2 * x 3 := schlafliGram_quad p q r x
      _ = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2
            + 2 * α * x 0 * x 1 + 2 * β * x 1 * x 2 + 2 * γ * x 2 * x 3 := by
          simp [α, β, γ]; ring
      _ = _ := band_quad_squares α β γ (x 0) (x 1) (x 2) (x 3) h2ne h3ne
  rw [hQ]
  refine weighted_squares_pos hc1 (div_pos hc2 hc1) (div_pos hc3 hc2) ?_
  by_contra hforms
  push Not at hforms
  obtain ⟨h01, h12, h23, h3z⟩ := hforms
  obtain ⟨hx0, hx1, hx2, hx3⟩ := ldl_coords_eq_zero h2ne h3ne h01 h12 h23 h3z
  have : x = 0 := by
    ext i
    fin_cases i <;> simp [hx0, hx1, hx2, hx3]
  exact hx this
