/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
Paper §3.3. Completing the square (LDL) for the rank-4 tridiagonal
quadratic form that the Schläfli Gram matrix induces.
-/

/-- Weighted sum of squares after the triangular change of variables. -/
lemma band_quad_squares (α β γ : ℝ) (x0 x1 x2 x3 : ℝ)
    (h2 : 1 - α ^ 2 ≠ 0) (h3 : 1 - α ^ 2 - β ^ 2 ≠ 0) :
    x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + 2 * α * x0 * x1 + 2 * β * x1 * x2 +
        2 * γ * x2 * x3 =
      (x0 + α * x1) ^ 2
      + (1 - α ^ 2) * (x1 + β / (1 - α ^ 2) * x2) ^ 2
      + ((1 - α ^ 2 - β ^ 2) / (1 - α ^ 2)) *
          (x2 + γ * (1 - α ^ 2) / (1 - α ^ 2 - β ^ 2) * x3) ^ 2
      + ((1 - α ^ 2 - β ^ 2 - γ ^ 2 * (1 - α ^ 2)) / (1 - α ^ 2 - β ^ 2)) *
          x3 ^ 2 := by
  field_simp [h2, h3]
  ring

lemma weighted_squares_pos {a b c d c1 c2 c3 : ℝ}
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hc3 : 0 < c3)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    0 < a ^ 2 + c1 * b ^ 2 + c2 * c ^ 2 + c3 * d ^ 2 := by
  rcases h with ha | hb | hc | hd
  · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a, sq_nonneg c, sq_nonneg d]
  · nlinarith [sq_pos_of_ne_zero hc, sq_nonneg a, sq_nonneg b, sq_nonneg d]
  · nlinarith [sq_pos_of_ne_zero hd, sq_nonneg a, sq_nonneg b, sq_nonneg c]

/-- The triangular change of variables is invertible. -/
lemma ldl_coords_eq_zero {α β γ x0 x1 x2 x3 : ℝ}
    (_h2 : 1 - α ^ 2 ≠ 0) (_h3 : 1 - α ^ 2 - β ^ 2 ≠ 0)
    (h01 : x0 + α * x1 = 0)
    (h12 : x1 + β / (1 - α ^ 2) * x2 = 0)
    (h23 : x2 + γ * (1 - α ^ 2) / (1 - α ^ 2 - β ^ 2) * x3 = 0)
    (h3z : x3 = 0) :
    x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
  have hx3 : x3 = 0 := h3z
  have hx2 : x2 = 0 := by
    rw [hx3] at h23
    simpa using h23
  have hx1 : x1 = 0 := by
    rw [hx2] at h12
    simp at h12
    exact h12
  have hx0 : x0 = 0 := by
    rw [hx1] at h01
    simpa using h01
  exact ⟨hx0, hx1, hx2, hx3⟩
