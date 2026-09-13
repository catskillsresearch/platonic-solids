/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PlatonicSolids.PlatonicPair

/-!
Paper §4. The eleven Schläfli triples whose cell and vertex figure
are both Platonic.
-/

/-- Compatible middle index: 11 of the 25 Platonic-pair products survive. -/
theorem platonic_compatible_eleven {p q r : ℕ}
    (hc : IsPlatonicPair p q) (hv : IsPlatonicPair q r) :
    p = 3 ∧ q = 3 ∧ r = 3 ∨
    p = 3 ∧ q = 3 ∧ r = 4 ∨
    p = 3 ∧ q = 3 ∧ r = 5 ∨
    p = 3 ∧ q = 4 ∧ r = 3 ∨
    p = 4 ∧ q = 3 ∧ r = 3 ∨
    p = 4 ∧ q = 3 ∧ r = 4 ∨
    p = 4 ∧ q = 3 ∧ r = 5 ∨
    p = 3 ∧ q = 5 ∧ r = 3 ∨
    p = 5 ∧ q = 3 ∧ r = 3 ∨
    p = 5 ∧ q = 3 ∧ r = 4 ∨
    p = 5 ∧ q = 3 ∧ r = 5 := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- cell {3,3}
    rcases hv with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
    · exact .inl ⟨rfl, rfl, rfl⟩
    · exact .inr <| .inl ⟨rfl, rfl, rfl⟩
    · cases h
    · exact .inr <| .inr <| .inl ⟨rfl, rfl, rfl⟩
    · cases h
  · -- cell {3,4}
    rcases hv with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · cases h
    · cases h
    · exact .inr <| .inr <| .inr <| .inl ⟨rfl, rfl, rfl⟩
    · cases h
    · cases h
  · -- cell {4,3}
    rcases hv with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
    · exact .inr <| .inr <| .inr <| .inr <| .inl ⟨rfl, rfl, rfl⟩
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨rfl, rfl, rfl⟩
    · cases h
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨rfl, rfl, rfl⟩
    · cases h
  · -- cell {3,5}
    rcases hv with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
    · cases h
    · cases h
    · cases h
    · cases h
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨rfl, rfl, rfl⟩
  · -- cell {5,3}
    rcases hv with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
        .inl ⟨rfl, rfl, rfl⟩
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
        .inr <| .inl ⟨rfl, rfl, rfl⟩
    · cases h
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
        .inr <| .inr ⟨rfl, rfl, rfl⟩
    · cases h
