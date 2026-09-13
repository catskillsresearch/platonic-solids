/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PlatonicSolids.Angles
import PlatonicSolids.CompatibleTriples
import PlatonicSolids.D3IffPlatonic
import PlatonicSolids.Regular4
import PlatonicSolids.SignTable
import PlatonicSolids.Sylvester
import PlatonicSolids.TrailingMinor

/-!
Paper §4. The six regular convex 4-polytopes are exactly the
Platonic-compatible triples with `Δ > 0`, equivalently those whose
Schläfli Gram matrix is positive definite.
-/

open Real Matrix

/-- Palomar compared 4D theorem: Platonic cell and vertex figure with
`Δ > 0` force one of the six regular convex 4-polytopes. -/
theorem regular_polychora_classification (p q r : ℕ)
    (h_cell : IsPlatonicPair p q)
    (h_vf : IsPlatonicPair q r)
    (h_det : 0 < schlafliDet p q r) :
    IsRegular4Polytope p q r := by
  rcases platonic_compatible_eleven h_cell h_vf with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact .inl ⟨rfl, rfl, rfl⟩
  · exact .inr <| .inr <| .inl ⟨rfl, rfl, rfl⟩
  · exact .inr <| .inr <| .inr <| .inr <| .inr ⟨rfl, rfl, rfl⟩
  · exact .inr <| .inr <| .inr <| .inl ⟨rfl, rfl, rfl⟩
  · exact .inr <| .inl ⟨rfl, rfl, rfl⟩
  · exact (not_lt_of_ge schlafliDet_434_nonpos h_det).elim
  · exact (lt_asymm schlafliDet_435_neg h_det).elim
  · exact (lt_asymm schlafliDet_353_neg h_det).elim
  · exact .inr <| .inr <| .inr <| .inr <| .inl ⟨rfl, rfl, rfl⟩
  · exact (lt_asymm schlafliDet_534_neg h_det).elim
  · exact (lt_asymm schlafliDet_535_neg h_det).elim

theorem schlafliDet_pos_of_regular {p q r : ℕ} (h : IsRegular4Polytope p q r) :
    0 < schlafliDet p q r := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact schlafliDet_333_pos
  · exact schlafliDet_433_pos
  · exact schlafliDet_334_pos
  · exact schlafliDet_343_pos
  · exact schlafliDet_533_pos
  · exact schlafliDet_335_pos

theorem regular_of_posDef {p q r : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r)
    (h : (schlafliGram p q r).PosDef) :
    IsRegular4Polytope p q r := by
  obtain ⟨_, _, h3, h4⟩ := leadingMinors_pos_of_posDef h
  have hcell : IsPlatonicPair p q := (leadingMinor_three_pos_iff hp hq).mp h3
  have hvf : IsPlatonicPair q r := by
    have hs := h.submatrix (Fin.succ_injective (n := 3))
    have : 0 < (trailing3 p q r).det := by
      simpa [trailing3] using PosDef.det_pos hs
    exact (trailing3_pos_iff hq hr).mp this
  have hdet : 0 < schlafliDet p q r := by
    rw [← schlafliGram_det]
    exact PosDef.det_pos h
  exact regular_polychora_classification p q r hcell hvf hdet

theorem posDef_of_regular {p q r : ℕ} (h : IsRegular4Polytope p q r) :
    (schlafliGram p q r).PosDef := by
  obtain ⟨hp, hq, _hr⟩ := h.ge_three
  obtain ⟨hcell, _hvf⟩ := h.platonic
  refine schlafliGram_posDef_of_minors ?_ ?_ ?_ ?_
  · rw [leadingMinor_one]; norm_num
  · rw [leadingMinor_two]; exact sq_pos_of_pos (sin_angle_pos hp)
  · exact (leadingMinor_three_pos_iff hp hq).mpr hcell
  · rw [schlafliGram_det]; exact schlafliDet_pos_of_regular h

/-- Finite regular convex 4-polytopes are exactly the triples `{p,q,r}`
with `p,q,r ≥ 3` whose Schläfli Gram matrix is positive definite. -/
theorem regular_polychora_iff {p q r : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r) :
    (schlafliGram p q r).PosDef ↔ IsRegular4Polytope p q r :=
  ⟨regular_of_posDef hp hq hr, posDef_of_regular⟩
