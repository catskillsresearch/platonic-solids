/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
Paper §2.3. The five solutions of `(p-2)(q-2) < 4` for `p, q ≥ 3`.
-/

/-- Schläfli pairs of the five Platonic solids. -/
def IsPlatonicPair (p q : ℕ) : Prop :=
  (p = 3 ∧ q = 3) ∨
  (p = 3 ∧ q = 4) ∨
  (p = 4 ∧ q = 3) ∨
  (p = 3 ∧ q = 5) ∨
  (p = 5 ∧ q = 3)

lemma pq_ge_two_p_add_two_q {p q : ℕ} (hp : 4 ≤ p) (hq : 4 ≤ q) :
    2 * p + 2 * q ≤ p * q := by
  zify
  nlinarith

/-- The inequality `pq < 2p + 2q` for `p, q ≥ 3` has exactly the five Platonic solutions. -/
theorem platonic_pairs_of_inequality {p q : ℕ}
    (hp : 3 ≤ p) (hq : 3 ≤ q) (h : p * q < 2 * p + 2 * q) :
    IsPlatonicPair p q := by
  rcases show p = 3 ∨ q = 3 ∨ (4 ≤ p ∧ 4 ≤ q) by omega with rfl | rfl | ⟨hp4, hq4⟩
  · rcases show q = 3 ∨ q = 4 ∨ q = 5 by omega with rfl | rfl | rfl <;> simp [IsPlatonicPair]
  · rcases show p = 3 ∨ p = 4 ∨ p = 5 by omega with rfl | rfl | rfl <;> simp [IsPlatonicPair]
  · exact (lt_irrefl _ (h.trans_le (pq_ge_two_p_add_two_q hp4 hq4))).elim

theorem IsPlatonicPair.ge_three {p q : ℕ} (h : IsPlatonicPair p q) : 3 ≤ p ∧ 3 ≤ q := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem IsPlatonicPair.inequality {p q : ℕ} (h : IsPlatonicPair p q) :
    p * q < 2 * p + 2 * q := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
