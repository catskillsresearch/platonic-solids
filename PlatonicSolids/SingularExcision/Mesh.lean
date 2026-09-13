/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
Metric input for the small-simplices theorem.

The Lebesgue-number lemma is most useful for subdivision in the following
form: every nonempty subset of the compact domain whose diameter is smaller
than one fixed positive number lies in one member of the open cover.
-/

open Metric Set

universe u v

variable {α : Type u} {ι : Sort v} [PseudoMetricSpace α]

/-- The classical mesh contraction factor for barycentric subdivision
of an `n`-simplex. -/
noncomputable def barycentricMeshRatio (n : ℕ) : ℝ :=
  n / (n + 1)

lemma barycentricMeshRatio_nonneg (n : ℕ) :
    0 ≤ barycentricMeshRatio n := by
  rw [barycentricMeshRatio]
  exact div_nonneg (Nat.cast_nonneg n) (by positivity)

lemma barycentricMeshRatio_lt_one (n : ℕ) :
    barycentricMeshRatio n < 1 := by
  rw [barycentricMeshRatio, div_lt_one]
  · exact_mod_cast Nat.lt_succ_self n
  · positivity

/-- Iterated barycentric subdivision eventually has mesh below every
positive threshold. -/
lemma exists_barycentricMeshRatio_pow_lt (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, barycentricMeshRatio n ^ k < ε :=
  exists_pow_lt_of_lt_one hε (barycentricMeshRatio_lt_one n)

/-- Diameter form of the Lebesgue-number lemma. -/
theorem exists_diam_lt_forall_subset_openCover
    {K : Set α} {U : ι → Set α}
    (hK : IsCompact K) (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ δ > 0, ∀ ⦃s : Set α⦄, s ⊆ K → s.Nonempty →
      Metric.diam s < δ → ∃ i, s ⊆ U i := by
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric hK hU hcover
  refine ⟨δ, hδ, ?_⟩
  intro s hsK hsne hsdiam
  obtain ⟨x, hxs⟩ := hsne
  obtain ⟨i, hi⟩ := hball x (hsK hxs)
  refine ⟨i, fun y hys ↦ hi ?_⟩
  rw [mem_ball, dist_comm]
  exact (Metric.dist_le_diam_of_mem (hK.isBounded.subset hsK) hxs hys).trans_lt hsdiam

/-- A continuous simplex pulls a two-set open cover back to an open cover
of its compact standard-simplex domain, with a uniform diameter bound. -/
theorem exists_diam_lt_forall_image_subset_left_or_right
    {n : ℕ} {Y : Type u} [TopologicalSpace Y]
    (σ : C(stdSimplex ℝ (Fin (n + 1)), Y))
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : A ∪ B = univ) :
    ∃ δ > 0, ∀ ⦃s : Set (stdSimplex ℝ (Fin (n + 1)))⦄,
      s.Nonempty → Metric.diam s < δ →
        σ '' s ⊆ A ∨ σ '' s ⊆ B := by
  let U : Bool → Set (stdSimplex ℝ (Fin (n + 1))) :=
    fun b ↦ if b then σ ⁻¹' A else σ ⁻¹' B
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    cases b
    · simpa [U] using hB.preimage σ.continuous
    · simpa [U] using hA.preimage σ.continuous
  have hcover : (univ : Set (stdSimplex ℝ (Fin (n + 1)))) ⊆ ⋃ b, U b := by
    intro x hx
    have hxAB : σ x ∈ A ∪ B := by rw [hAB]; exact mem_univ _
    rcases hxAB with hxA | hxB
    · exact mem_iUnion.2 ⟨true, by simpa [U]⟩
    · exact mem_iUnion.2 ⟨false, by simpa [U]⟩
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_diam_lt_forall_subset_openCover
      (U := U) isCompact_univ hU hcover
  refine ⟨δ, hδ, ?_⟩
  intro s hsne hsdiam
  obtain ⟨b, hb⟩ := hsmall (subset_univ s) hsne hsdiam
  cases b
  · right
    rintro _ ⟨x, hx, rfl⟩
    exact hb hx
  · left
    rintro _ ⟨x, hx, rfl⟩
    exact hb hx
