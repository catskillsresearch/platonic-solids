/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Abel

/-!
The elementwise algebraic core of the small-simplices proof of singular
excision. It is deliberately independent of singular simplices and is
applied to the direct sum of the chain groups of a chain complex of
modules.
-/

open Function

namespace SingularExcision

/-- Ungraded data underlying subdivision: the differential `d`, subdivision
`S`, and prism `H`, with `id - S = dH + Hd`. -/
structure SubdivisionData (A : Type*) [AddCommGroup A] where
  d : A →+ A
  S : A →+ A
  H : A →+ A
  S_comm : ∀ x, d (S x) = S (d x)
  homotopy : ∀ x, x - S x = d (H x) + H (d x)

namespace SubdivisionData

variable {A : Type*} [AddCommGroup A] (D : SubdivisionData A)

def Cycle (x : A) : Prop :=
  D.d x = 0

def Homologous (x y : A) : Prop :=
  ∃ w : A, x - y = D.d w

lemma cycle_S {x : A} (hx : D.Cycle x) :
    D.Cycle (D.S x) := by
  rw [Cycle, D.S_comm, hx, map_zero]

lemma cycle_iterate {x : A} (hx : D.Cycle x) (N : ℕ) :
    D.Cycle (D.S^[N] x) := by
  induction N with
  | zero => simpa
  | succ N ih =>
      rw [iterate_succ_apply']
      exact D.cycle_S ih

lemma homologous_refl (x : A) :
    D.Homologous x x :=
  ⟨0, by simp⟩

lemma homologous_S_of_cycle {x : A} (hx : D.Cycle x) :
    D.Homologous x (D.S x) := by
  refine ⟨D.H x, ?_⟩
  rw [D.homotopy, show D.d x = 0 from hx, map_zero, add_zero]

lemma homologous_trans {x y z : A}
    (hxy : D.Homologous x y) (hyz : D.Homologous y z) :
    D.Homologous x z := by
  obtain ⟨u, hu⟩ := hxy
  obtain ⟨v, hv⟩ := hyz
  refine ⟨u + v, ?_⟩
  rw [map_add, ← hu, ← hv]
  abel

lemma homologous_iterate_of_cycle {x : A} (hx : D.Cycle x) (N : ℕ) :
    D.Homologous x (D.S^[N] x) := by
  induction N with
  | zero => simpa using D.homologous_refl x
  | succ N ih =>
      rw [iterate_succ_apply']
      exact D.homologous_trans ih
        (D.homologous_S_of_cycle (D.cycle_iterate hx N))

variable (B : AddSubgroup A)

/-- The small chains are closed under boundary, subdivision, and prism. -/
structure SmallInvariant : Prop where
  d_mem : ∀ {x}, x ∈ B → D.d x ∈ B
  S_mem : ∀ {x}, x ∈ B → D.S x ∈ B
  H_mem : ∀ {x}, x ∈ B → D.H x ∈ B

lemma iterate_mem (hB : D.SmallInvariant B) {x : A}
    (hx : x ∈ B) (N : ℕ) :
    D.S^[N] x ∈ B := by
  induction N with
  | zero => simpa
  | succ N ih =>
      rw [iterate_succ_apply']
      exact hB.S_mem ih

lemma small_boundary_of_small_homologous
    (hB : D.SmallInvariant B) {x : A}
    (hx : x ∈ B) (hxcycle : D.Cycle x) (N : ℕ) :
    ∃ w ∈ B, x - D.S^[N] x = D.d w := by
  induction N with
  | zero => exact ⟨0, B.zero_mem, by simp⟩
  | succ N ih =>
      obtain ⟨w, hwB, hw⟩ := ih
      let xN := D.S^[N] x
      refine ⟨w + D.H xN,
        B.add_mem hwB (hB.H_mem (D.iterate_mem B hB hx N)), ?_⟩
      rw [map_add, ← hw]
      have hxNcycle := D.cycle_iterate hxcycle N
      have hstep : xN - D.S xN = D.d (D.H xN) := by
        rw [D.homotopy, show D.d xN = 0 from hxNcycle, map_zero, add_zero]
      rw [← hstep, iterate_succ_apply']
      abel

/-- If subdivision eventually puts every finite chain in the small-chain
subgroup, every homology class has a small representative and every small
boundary bounds a small chain. -/
theorem small_cycles_and_boundaries
    (hB : D.SmallInvariant B)
    (eventual : ∀ x : A, ∃ N, D.S^[N] x ∈ B) :
    (∀ z : A, D.Cycle z →
      ∃ b ∈ B, D.Cycle b ∧ D.Homologous z b) ∧
    (∀ b : A, b ∈ B → D.Cycle b →
      (∃ x : A, b = D.d x) → ∃ y ∈ B, b = D.d y) := by
  constructor
  · intro z hz
    obtain ⟨N, hN⟩ := eventual z
    exact ⟨D.S^[N] z, hN, D.cycle_iterate hz N,
      D.homologous_iterate_of_cycle hz N⟩
  · intro b hb hbcycle hboundary
    obtain ⟨x, rfl⟩ := hboundary
    obtain ⟨N, hNx⟩ := eventual x
    obtain ⟨w, hwB, hw⟩ :=
      D.small_boundary_of_small_homologous B hB hb hbcycle N
    refine ⟨D.S^[N] x + w, B.add_mem hNx hwB, ?_⟩
    rw [map_add, ← hw]
    have hcomm : ∀ M : ℕ, D.S^[M] (D.d x) = D.d (D.S^[M] x) := by
      intro M
      induction M with
      | zero => simp
      | succ M ih =>
          rw [iterate_succ_apply', iterate_succ_apply', D.S_comm, ih]
    rw [← hcomm N]
    abel

end SubdivisionData
end SingularExcision
