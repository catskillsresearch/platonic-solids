/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PlatonicSolids.Angles
import PlatonicSolids.LeadingMinors
import PlatonicSolids.Reciprocal
import PlatonicSolids.TrailingMinor

/-!
Paper §3.3. `D₃ > 0` iff the cell is Platonic; the trailing 3×3 minor
is the same statement for the vertex figure.
-/

open Real

lemma angle_mem_Icc {n : ℕ} (hn : 3 ≤ n) :
    π / n ∈ Set.Icc (-(π / 2)) (π / 2) :=
  ⟨by linarith [angle_pos (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hn)), pi_pos],
    (angle_lt_pi_div_two hn).le⟩

lemma complement_mem_Icc {n : ℕ} (hn : 3 ≤ n) :
    π / 2 - π / n ∈ Set.Icc (-(π / 2)) (π / 2) :=
  ⟨by linarith [angle_lt_pi_div_two hn, pi_pos],
    by linarith [angle_pos (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hn))]⟩

/-- `sin(π/p) > cos(π/q)` iff `1/p + 1/q > 1/2`. -/
lemma sin_gt_cos_iff_reciprocal {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    sin (π / p) > cos (π / q) ↔ 1 / (p : ℝ) + 1 / q > 1 / 2 := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hp)
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hq)
  rw [← sin_pi_div_two_sub (π / q), gt_iff_lt, gt_iff_lt]
  rw [strictMonoOn_sin.lt_iff_lt (complement_mem_Icc hq) (angle_mem_Icc hp)]
  constructor
  · intro h
    have hsum : π / p + π / q > π / 2 := by linarith
    have hmul : π * (1 / (p : ℝ) + 1 / q) > π * (1 / 2) := by
      convert hsum using 1 <;> field_simp
    exact lt_of_mul_lt_mul_left hmul pi_pos.le
  · intro h
    have hmul : π * (1 / (p : ℝ) + 1 / q) > π * (1 / 2) :=
      mul_lt_mul_of_pos_left h pi_pos
    have hsum : π / p + π / q > π / 2 := by
      convert hmul using 1 <;> field_simp
    linarith

/-- Leading 3×3 minor `D₃ > 0` iff `{p, q}` is Platonic. -/
theorem leadingMinor_three_pos_iff {p q r : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    0 < leadingMinor 3 (by decide) p q r ↔ IsPlatonicPair p q := by
  rw [leadingMinor_three, platonic_pair_iff_reciprocal hp hq, sub_pos,
    sq_lt_sq₀ (cos_angle_pos hq).le (sin_angle_pos hp).le]
  exact sin_gt_cos_iff_reciprocal hp hq

/-- Trailing 3×3 minor `> 0` iff the vertex figure `{q, r}` is Platonic. -/
theorem trailing3_pos_iff {p q r : ℕ} (hq : 3 ≤ q) (hr : 3 ≤ r) :
    0 < (trailing3 p q r).det ↔ IsPlatonicPair q r := by
  rw [trailing3_det, ← leadingMinor_three (p := q) (q := r) (r := p)]
  exact leadingMinor_three_pos_iff hq hr
