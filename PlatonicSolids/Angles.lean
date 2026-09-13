/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Paper §3.3. For `n ≥ 3`, the Schläfli angle `π/n` lies in `(0, π/2)`,
so `sin` and `cos` are positive.
-/

open Real

lemma angle_pos {n : ℕ} (hn : 1 ≤ n) : 0 < π / n := by
  have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  positivity

lemma angle_lt_pi_div_two {n : ℕ} (hn : 3 ≤ n) : π / n < π / 2 :=
  div_lt_div_of_pos_left pi_pos (by positivity : (0 : ℝ) < 2)
    (by exact_mod_cast (lt_of_lt_of_le (by decide : (2 : ℕ) < 3) hn))

lemma sin_angle_pos {n : ℕ} (hn : 3 ≤ n) : 0 < sin (π / n) :=
  sin_pos_of_pos_of_lt_pi (angle_pos (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hn)))
    (angle_lt_pi_div_two hn |>.trans (by linarith [pi_pos]))

lemma cos_angle_pos {n : ℕ} (hn : 3 ≤ n) : 0 < cos (π / n) :=
  cos_pos_of_mem_Ioo ⟨by linarith [angle_pos (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hn)), pi_pos],
    angle_lt_pi_div_two hn⟩
