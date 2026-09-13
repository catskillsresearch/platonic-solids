/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PlatonicSolids.PlatonicPair

/-!
Paper §4, Group I. The six regular convex 4-polytopes.
-/

/-- Schläfli triples of the six regular convex 4-polytopes. -/
def IsRegular4Polytope (p q r : ℕ) : Prop :=
  (p = 3 ∧ q = 3 ∧ r = 3) ∨
  (p = 4 ∧ q = 3 ∧ r = 3) ∨
  (p = 3 ∧ q = 3 ∧ r = 4) ∨
  (p = 3 ∧ q = 4 ∧ r = 3) ∨
  (p = 5 ∧ q = 3 ∧ r = 3) ∨
  (p = 3 ∧ q = 3 ∧ r = 5)

theorem IsRegular4Polytope.ge_three {p q r : ℕ} (h : IsRegular4Polytope p q r) :
    3 ≤ p ∧ 3 ≤ q ∧ 3 ≤ r := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide

theorem IsRegular4Polytope.platonic {p q r : ℕ} (h : IsRegular4Polytope p q r) :
    IsPlatonicPair p q ∧ IsPlatonicPair q r := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [IsPlatonicPair]
