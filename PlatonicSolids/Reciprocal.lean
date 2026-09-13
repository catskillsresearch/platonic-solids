/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import PlatonicSolids.PlatonicPair

/-!
Paper §2.3 / §3.3. `1/p + 1/q > 1/2` is the reciprocal form of the
Platonic Diophantine inequality, and is the condition `D₃ > 0`.
-/

lemma reciprocal_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (1 / (p : ℝ) + 1 / q > 1 / 2) ↔ p * q < 2 * p + 2 * q := by
  have : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  constructor
  · intro h
    have h' : (p + q : ℝ) / (p * q) > 1 / 2 := by
      convert h using 1
      field_simp
      ring
    rw [gt_iff_lt, lt_div_iff₀ (by positivity)] at h'
    exact_mod_cast (by linarith : (p * q : ℝ) < 2 * p + 2 * q)
  · intro h
    have hR : (p * q : ℝ) < 2 * p + 2 * q := mod_cast h
    have h' : (p + q : ℝ) / (p * q) > 1 / 2 := by
      rw [gt_iff_lt, lt_div_iff₀ (by positivity)]
      linarith
    convert h' using 1
    field_simp
    ring

theorem platonic_pair_iff {p q : ℕ} :
    IsPlatonicPair p q ↔ 3 ≤ p ∧ 3 ≤ q ∧ p * q < 2 * p + 2 * q := by
  constructor
  · intro h
    exact ⟨h.ge_three.1, h.ge_three.2, h.inequality⟩
  · exact fun ⟨hp, hq, h⟩ => platonic_pairs_of_inequality hp hq h

theorem platonic_pair_iff_reciprocal {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    IsPlatonicPair p q ↔ 1 / (p : ℝ) + 1 / q > 1 / 2 := by
  rw [platonic_pair_iff, reciprocal_iff (by omega) (by omega)]
  simp [hp, hq]
