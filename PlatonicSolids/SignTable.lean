/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PlatonicSolids.GramMatrix
import PlatonicSolids.TrigValues

/-!
Paper §4. Sign of `Δ` on the eleven Platonic-compatible triples.
-/

open Real

private lemma unfold_det (p q r : ℕ) :
    schlafliDet p q r = sin (π / p) ^ 2 * sin (π / r) ^ 2 - cos (π / q) ^ 2 :=
  rfl

private lemma cast_angles :
    sin (π / (3 : ℕ)) ^ 2 = sin (π / 3) ^ 2 ∧
    sin (π / (4 : ℕ)) ^ 2 = sin (π / 4) ^ 2 ∧
    sin (π / (5 : ℕ)) ^ 2 = sin (π / 5) ^ 2 ∧
    cos (π / (3 : ℕ)) ^ 2 = cos (π / 3) ^ 2 ∧
    cos (π / (4 : ℕ)) ^ 2 = cos (π / 4) ^ 2 ∧
    cos (π / (5 : ℕ)) ^ 2 = cos (π / 5) ^ 2 := by
  simp [Nat.cast_ofNat]

lemma schlafliDet_333 : schlafliDet 3 3 3 = 5 / 16 := by
  rw [unfold_det, cast_angles.1, cast_angles.2.2.2.1, sq_sin_pi_div_three, sq_cos_pi_div_three]
  norm_num

lemma schlafliDet_334 : schlafliDet 3 3 4 = 1 / 8 := by
  rw [unfold_det, cast_angles.1, cast_angles.2.1, cast_angles.2.2.2.1,
    sq_sin_pi_div_three, sq_sin_pi_div_four, sq_cos_pi_div_three]
  norm_num

lemma schlafliDet_433 : schlafliDet 4 3 3 = 1 / 8 := by
  rw [unfold_det, cast_angles.2.1, cast_angles.1, cast_angles.2.2.2.1,
    sq_sin_pi_div_four, sq_sin_pi_div_three, sq_cos_pi_div_three]
  norm_num

lemma schlafliDet_343 : schlafliDet 3 4 3 = 1 / 16 := by
  rw [unfold_det, cast_angles.1, cast_angles.2.2.2.2.1, sq_sin_pi_div_three, sq_cos_pi_div_four]
  norm_num

lemma schlafliDet_335 : schlafliDet 3 3 5 = (7 - 3 * √5) / 32 := by
  rw [unfold_det, cast_angles.1, cast_angles.2.2.1, cast_angles.2.2.2.1,
    sq_sin_pi_div_three, sq_sin_pi_div_five, sq_cos_pi_div_three]
  ring

lemma schlafliDet_533 : schlafliDet 5 3 3 = (7 - 3 * √5) / 32 := by
  rw [unfold_det, cast_angles.2.2.1, cast_angles.1, cast_angles.2.2.2.1,
    sq_sin_pi_div_five, sq_sin_pi_div_three, sq_cos_pi_div_three]
  ring

lemma schlafliDet_434 : schlafliDet 4 3 4 = 0 := by
  rw [unfold_det, cast_angles.2.1, cast_angles.2.2.2.1, sq_sin_pi_div_four, sq_cos_pi_div_three]
  norm_num

lemma schlafliDet_353 : schlafliDet 3 5 3 = (3 - 2 * √5) / 16 := by
  rw [unfold_det, cast_angles.1, cast_angles.2.2.2.2.2, sq_sin_pi_div_three, sq_cos_pi_div_five]
  ring

lemma schlafliDet_435 : schlafliDet 4 3 5 = (1 - √5) / 16 := by
  rw [unfold_det, cast_angles.2.1, cast_angles.2.2.1, cast_angles.2.2.2.1,
    sq_sin_pi_div_four, sq_sin_pi_div_five, sq_cos_pi_div_three]
  ring

lemma schlafliDet_534 : schlafliDet 5 3 4 = (1 - √5) / 16 := by
  rw [unfold_det, cast_angles.2.2.1, cast_angles.2.1, cast_angles.2.2.2.1,
    sq_sin_pi_div_five, sq_sin_pi_div_four, sq_cos_pi_div_three]
  ring

lemma schlafliDet_535 : schlafliDet 5 3 5 = (14 - 10 * √5) / 64 := by
  rw [unfold_det, cast_angles.2.2.1, cast_angles.2.2.2.1, sq_sin_pi_div_five, sq_cos_pi_div_three]
  have : ((5 - √5) / 8) ^ 2 = (30 - 10 * √5) / 64 := by
    field_simp
    ring_nf
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring
  rw [← pow_two, this]
  ring

lemma schlafliDet_333_pos : 0 < schlafliDet 3 3 3 := by rw [schlafliDet_333]; norm_num
lemma schlafliDet_334_pos : 0 < schlafliDet 3 3 4 := by rw [schlafliDet_334]; norm_num
lemma schlafliDet_433_pos : 0 < schlafliDet 4 3 3 := by rw [schlafliDet_433]; norm_num
lemma schlafliDet_343_pos : 0 < schlafliDet 3 4 3 := by rw [schlafliDet_343]; norm_num

lemma schlafliDet_335_pos : 0 < schlafliDet 3 3 5 := by
  rw [schlafliDet_335]
  have : 0 < 7 - 3 * √5 := by linarith [three_mul_sqrt5_lt_seven]
  positivity

lemma schlafliDet_533_pos : 0 < schlafliDet 5 3 3 := by
  rw [schlafliDet_533]
  have : 0 < 7 - 3 * √5 := by linarith [three_mul_sqrt5_lt_seven]
  positivity

lemma schlafliDet_434_nonpos : schlafliDet 4 3 4 ≤ 0 := by
  rw [schlafliDet_434]

lemma schlafliDet_353_neg : schlafliDet 3 5 3 < 0 := by
  rw [schlafliDet_353]
  have : 3 - 2 * √5 < 0 := by linarith [two_mul_sqrt5_gt_three]
  exact div_neg_of_neg_of_pos this (by positivity)

lemma schlafliDet_435_neg : schlafliDet 4 3 5 < 0 := by
  rw [schlafliDet_435]
  have : 1 - √5 < 0 := by linarith [sqrt5_bounds.1]
  exact div_neg_of_neg_of_pos this (by positivity)

lemma schlafliDet_534_neg : schlafliDet 5 3 4 < 0 := by
  rw [schlafliDet_534]
  have : 1 - √5 < 0 := by linarith [sqrt5_bounds.1]
  exact div_neg_of_neg_of_pos this (by positivity)

lemma schlafliDet_535_neg : schlafliDet 5 3 5 < 0 := by
  rw [schlafliDet_535]
  have : 14 - 10 * √5 < 0 := by
    have : 14 < 10 * √5 := by nlinarith [sqrt5_bounds.1]
    linarith
  exact div_neg_of_neg_of_pos this (by positivity)
