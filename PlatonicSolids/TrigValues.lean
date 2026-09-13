/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Paper §4. Exact `sin²(π/n)` and `cos²(π/n)` for `n ∈ {3,4,5}`, from
Mathlib's `sin_pi_div_*` / `cos_pi_div_*`.
-/

open Real

lemma sq_cos_pi_div_three : cos (π / 3) ^ 2 = 1 / 4 := by
  rw [cos_pi_div_three]; norm_num

lemma sq_sin_pi_div_four : sin (π / 4) ^ 2 = 1 / 2 := by
  rw [sin_pi_div_four, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

lemma sq_cos_pi_div_four : cos (π / 4) ^ 2 = 1 / 2 := by
  rw [cos_pi_div_four, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

lemma sq_cos_pi_div_five : cos (π / 5) ^ 2 = (3 + √5) / 8 := by
  rw [cos_pi_div_five]
  have : (1 + √5) ^ 2 = 6 + 2 * √5 := by
    ring_nf
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring
  field_simp
  rw [this]
  ring

lemma sq_sin_pi_div_five : sin (π / 5) ^ 2 = (5 - √5) / 8 := by
  have h : sin (π / 5) ^ 2 = 1 - cos (π / 5) ^ 2 := by
    linarith [sin_sq_add_cos_sq (π / 5)]
  rw [h, sq_cos_pi_div_five]
  field_simp
  ring

lemma sqrt5_bounds : 2 < √5 ∧ √5 < 3 := by
  constructor
  · rw [lt_sqrt (by norm_num)]; norm_num
  · rw [sqrt_lt' (by norm_num)]; norm_num

lemma three_mul_sqrt5_lt_seven : 3 * √5 < 7 := by
  have h : (3 * √5) ^ 2 < (7 : ℝ) ^ 2 := by
    calc (3 * √5) ^ 2 = 9 * (√5 ^ 2) := by ring
      _ = 9 * 5 := by rw [sq_sqrt (by norm_num)]
      _ = 45 := by norm_num
      _ < 49 := by norm_num
      _ = (7 : ℝ) ^ 2 := by norm_num
  have : 0 ≤ 3 * √5 := by positivity
  nlinarith

lemma two_mul_sqrt5_gt_three : 3 < 2 * √5 := by
  have h : (3 : ℝ) ^ 2 < (2 * √5) ^ 2 := by
    calc (3 : ℝ) ^ 2 = 9 := by norm_num
      _ < 20 := by norm_num
      _ = 4 * 5 := by norm_num
      _ = 4 * (√5 ^ 2) := by rw [sq_sqrt (by norm_num)]
      _ = (2 * √5) ^ 2 := by ring
  have : 0 ≤ 2 * √5 := by positivity
  nlinarith
