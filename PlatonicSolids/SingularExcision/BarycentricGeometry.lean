/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Module.Convex
import PlatonicSolids.SingularExcision.AffineRealization
import PlatonicSolids.SingularExcision.Mesh

/-!
Diameter of barycentric pieces. Each cone-on-face piece of an
`n`-simplex has diameter at most `n/(n+1)` times the parent, so
iterated subdivision has mesh going to zero.
-/

open Metric Set Bornology
open scoped BigOperators

namespace PlatonicSolids.SingularExcision

noncomputable section

lemma barycentricMeshRatio_le_succ (n : ℕ) :
    barycentricMeshRatio n ≤ barycentricMeshRatio (n + 1) := by
  simp only [barycentricMeshRatio]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast
  nlinarith

lemma AffineSimplex.range_face_subset {V : Type*} {n : ℕ}
    (σ : AffineSimplex V (n + 1)) (i : Fin (n + 2)) :
    Set.range (σ.face i) ⊆ Set.range σ :=
  fun _ ⟨j, hj⟩ => ⟨i.succAbove j, hj⟩

lemma AffineSimplex.range_append {V : Type*} {n : ℕ}
    (ρ : AffineSimplex V n) (v : V) :
    Set.range (ρ.append v) = insert v (Set.range ρ) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last =>
        left
        simp [AffineSimplex.append]
    | cast j =>
        right
        exact ⟨j, by simp [AffineSimplex.append]⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨Fin.last _, by simp [AffineSimplex.append]⟩
    · exact ⟨j.castSucc, by simp [AffineSimplex.append]⟩

lemma AffineSimplex.realize_val {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (x : stdSimplex ℝ (Fin (p + 1))) :
    (σ.realize x : Fin (q + 1) → ℝ) =
      ∑ i, x.1 i • (σ i : Fin (q + 1) → ℝ) := by
  funext j
  rw [realize_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  rfl

lemma AffineSimplex.realize_mem_convexHull {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (x : stdSimplex ℝ (Fin (p + 1))) :
    (σ.realize x : Fin (q + 1) → ℝ) ∈
      convexHull ℝ ((↑) '' Set.range σ) := by
  rw [AffineSimplex.realize_val]
  exact (convex_convexHull ℝ _).sum_mem
    (fun i _ => x.2.1 i) x.2.2
    (fun i _ => subset_convexHull ℝ _ ⟨σ i, ⟨i, rfl⟩, rfl⟩)

lemma AffineSimplex.stdBarycenter_mem_convexHull {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    (σ.stdBarycenter : Fin (q + 1) → ℝ) ∈
      convexHull ℝ ((↑) '' Set.range σ) :=
  σ.realize_mem_convexHull stdSimplex.barycenter

lemma AffineSimplex.range_subset_range_realize {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    Set.range σ ⊆ Set.range σ.realize := by
  rintro _ ⟨i, rfl⟩
  exact ⟨stdSimplex.vertex i, σ.realize_vertex i⟩

lemma isBounded_range_affineSimplex {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    IsBounded (Set.range σ) :=
  (Set.finite_range σ).isBounded

lemma isBounded_range_realize {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    IsBounded (Set.range σ.realize) :=
  (isCompact_range σ.realize.continuous).isBounded

lemma diam_coe_image_of_bounded {ι : Type*} [Fintype ι]
    {s : Set (stdSimplex ℝ ι)} (hs : IsBounded s)
    (hs' : IsBounded ((↑) '' s : Set (ι → ℝ))) :
    diam ((↑) '' s : Set (ι → ℝ)) = diam s := by
  refine le_antisymm ?_ ?_
  · refine diam_le_of_forall_dist_le diam_nonneg ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa [Subtype.dist_eq] using dist_le_diam_of_mem hs hx hy
  · refine diam_le_of_forall_dist_le diam_nonneg ?_
    intro x hx y hy
    simpa [Subtype.dist_eq] using
      dist_le_diam_of_mem hs' ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

lemma diam_coe_image_finite {ι : Type*} [Fintype ι]
    (s : Set (stdSimplex ℝ ι)) (hs : s.Finite) :
    diam ((↑) '' s : Set (ι → ℝ)) = diam s :=
  diam_coe_image_of_bounded hs.isBounded (hs.image _).isBounded

/-- Realization cannot increase diameter: it is the convex hull of the
listed vertices in the ambient coordinate space. -/
lemma diam_range_realize_le {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    diam (Set.range σ.realize) ≤ diam (Set.range σ) := by
  refine diam_le_of_forall_dist_le diam_nonneg ?_
  intro x hx y hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have ha := σ.realize_mem_convexHull a
  have hb := σ.realize_mem_convexHull b
  have hB : IsBounded ((↑) '' Set.range σ : Set (Fin (q + 1) → ℝ)) :=
    ((Set.finite_range σ).image _).isBounded
  have hle : dist (σ.realize a : Fin (q + 1) → ℝ)
      (σ.realize b : Fin (q + 1) → ℝ) ≤
      diam ((↑) '' Set.range σ : Set (Fin (q + 1) → ℝ)) :=
    (dist_le_diam_of_mem (isBounded_convexHull.mpr hB) ha hb).trans
      (by rw [convexHull_diam])
  simpa [Subtype.dist_eq, diam_coe_image_finite _ (Set.finite_range σ)] using hle

lemma diam_range_realize_eq {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    diam (Set.range σ.realize) = diam (Set.range σ) :=
  le_antisymm (diam_range_realize_le σ)
    (diam_mono σ.range_subset_range_realize (isBounded_range_realize σ))

lemma diam_range_affineSimplex_zero {q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) 0) :
    diam (Set.range σ) = 0 := by
  refine diam_subsingleton ?_
  intro x hx y hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  rw [Fin.eq_zero i, Fin.eq_zero j]

/-- Distance from the barycenter to a vertex is at most the mesh ratio
times the vertex diameter. -/
lemma dist_stdBarycenter_vertex {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (i : Fin (p + 1)) :
    dist σ.stdBarycenter (σ i) ≤
      barycentricMeshRatio p * diam (Set.range σ) := by
  classical
  have hne : (p + 1 : ℝ) ≠ 0 := by positivity
  have hval : (σ.stdBarycenter : Fin (q + 1) → ℝ) =
      ∑ j : Fin (p + 1), (p + 1 : ℝ)⁻¹ • (σ j : Fin (q + 1) → ℝ) := by
    rw [AffineSimplex.stdBarycenter, AffineSimplex.realize_val]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [stdSimplex.barycenter, Fintype.card_fin]
  have hsum : ∑ _j : Fin (p + 1), (p + 1 : ℝ)⁻¹ = (1 : ℝ) := by
    simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hne]
  have hi : (σ i : Fin (q + 1) → ℝ) =
      ∑ j : Fin (p + 1), (p + 1 : ℝ)⁻¹ • (σ i : Fin (q + 1) → ℝ) := by
    rw [← Finset.sum_smul, hsum, one_smul]
  have hdiff :
      (σ.stdBarycenter : Fin (q + 1) → ℝ) - (σ i : Fin (q + 1) → ℝ) =
        ∑ j : Fin (p + 1),
          (p + 1 : ℝ)⁻¹ •
            ((σ j : Fin (q + 1) → ℝ) - (σ i : Fin (q + 1) → ℝ)) := by
    rw [hval]
    conv_lhs => rw [hi]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => (smul_sub _ _ _).symm
  have hsub :
      (σ.stdBarycenter : Fin (q + 1) → ℝ) - (σ i : Fin (q + 1) → ℝ) =
        ∑ j ∈ Finset.univ.erase i,
          (p + 1 : ℝ)⁻¹ •
            ((σ j : Fin (q + 1) → ℝ) - (σ i : Fin (q + 1) → ℝ)) := by
    rw [hdiff, ← Finset.sum_erase_add (f := fun j =>
        (p + 1 : ℝ)⁻¹ •
          ((σ j : Fin (q + 1) → ℝ) - (σ i : Fin (q + 1) → ℝ)))
        (h := Finset.mem_univ i)]
    simp [sub_self]
  rw [Subtype.dist_eq, dist_eq_norm]
  change ‖(σ.stdBarycenter : Fin (q + 1) → ℝ) - (σ i : Fin (q + 1) → ℝ)‖ ≤ _
  rw [hsub]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ p + 1))]
  have hterm (j : Fin (p + 1)) :
      (p + 1 : ℝ)⁻¹ *
          ‖(σ j : Fin (q + 1) → ℝ) - (σ i : Fin (q + 1) → ℝ)‖ ≤
        (p + 1 : ℝ)⁻¹ * diam (Set.range σ) := by
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (by positivity))
    simpa [dist_eq_norm, Subtype.dist_eq] using
      dist_le_diam_of_mem (isBounded_range_affineSimplex σ)
        ⟨j, rfl⟩ ⟨i, rfl⟩
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  simp only [Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]
  have hcard : (((p + 1 : ℕ) - 1 : ℕ) : ℝ) = (p : ℝ) := by
    norm_cast
  rw [hcard, barycentricMeshRatio, div_eq_mul_inv, mul_assoc]

/-- Distance from the barycenter to any point of the convex hull of the
vertices is controlled by the same mesh ratio. -/
lemma dist_stdBarycenter_mem_convexHull {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    {x : Fin (q + 1) → ℝ}
    (hx : x ∈ convexHull ℝ ((↑) '' Set.range σ)) :
    dist (σ.stdBarycenter : Fin (q + 1) → ℝ) x ≤
      barycentricMeshRatio p * diam (Set.range σ) := by
  obtain ⟨y, hy, hle⟩ :=
    convexHull_exists_dist_ge hx (σ.stdBarycenter : Fin (q + 1) → ℝ)
  obtain ⟨v, ⟨i, rfl⟩, rfl⟩ := hy
  rw [dist_comm]
  exact hle.trans (by
    simpa [dist_comm, Subtype.dist_eq] using dist_stdBarycenter_vertex σ i)

/-- Vertices of every barycentric piece lie in the convex hull of the
parent vertices. -/
lemma vertices_subdivideStd_mem_convexHull {q : ℕ} (n : ℕ) :
    ∀ (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) n)
      {τ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) n},
      τ ∈ (subdivideStd (q := q) n (simplex σ)).support →
      ∀ i : Fin (n + 1),
        (τ i : Fin (q + 1) → ℝ) ∈ convexHull ℝ ((↑) '' Set.range σ) := by
  induction n with
  | zero =>
      intro σ τ hτ i
      classical
      simp [subdivideStd, subdivide_zero, simplex,
        Finsupp.mem_support_single] at hτ
      rcases hτ with ⟨rfl, _⟩
      exact subset_convexHull ℝ _ ⟨σ i, ⟨i, rfl⟩, rfl⟩
  | succ n ih =>
      intro σ τ hτ i
      obtain ⟨j, ρ, hρ, rfl⟩ :=
        mem_support_subdivide_simplex AffineSimplex.stdBarycenter σ hτ
      induction i using Fin.lastCases with
      | last =>
          simpa [AffineSimplex.append] using σ.stdBarycenter_mem_convexHull
      | cast k =>
          exact convexHull_mono (image_mono (σ.range_face_subset j))
            (by simpa [AffineSimplex.append] using ih (σ.face j) hρ k)

/-- Vertex-diameter of a barycentric piece is at most the mesh ratio
times the parent vertex-diameter. -/
lemma diam_range_subdivideStd_le {q : ℕ} (n : ℕ) :
    ∀ (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) n)
      {τ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) n},
      τ ∈ (subdivideStd (q := q) n (simplex σ)).support →
      diam (Set.range τ) ≤
        barycentricMeshRatio n * diam (Set.range σ) := by
  induction n with
  | zero =>
      intro σ τ hτ
      classical
      simp [subdivideStd, subdivide_zero, simplex,
        Finsupp.mem_support_single] at hτ
      rcases hτ with ⟨rfl, _⟩
      simp [diam_range_affineSimplex_zero]
  | succ n ih =>
      intro σ τ hτ
      obtain ⟨j, ρ, hρ, rfl⟩ :=
        mem_support_subdivide_simplex AffineSimplex.stdBarycenter σ hτ
      set C := barycentricMeshRatio (n + 1) * diam (Set.range σ)
      have hC : 0 ≤ C :=
        mul_nonneg (barycentricMeshRatio_nonneg _) diam_nonneg
      have hρdiam : diam (Set.range ρ) ≤ C := by
        have h1 := ih (σ.face j) (τ := ρ) hρ
        have h2 : diam (Set.range (σ.face j)) ≤ diam (Set.range σ) :=
          diam_mono (σ.range_face_subset j) (isBounded_range_affineSimplex σ)
        have h3 : barycentricMeshRatio n * diam (Set.range σ) ≤ C :=
          mul_le_mul_of_nonneg_right (barycentricMeshRatio_le_succ n)
            diam_nonneg
        exact (h1.trans (mul_le_mul_of_nonneg_left h2
          (barycentricMeshRatio_nonneg n))).trans h3
      have hdist {x : stdSimplex ℝ (Fin (q + 1))}
          (hx : x ∈ Set.range ρ) :
          dist σ.stdBarycenter x ≤ C := by
        obtain ⟨k, rfl⟩ := hx
        have hx' : (ρ k : Fin (q + 1) → ℝ) ∈
            convexHull ℝ ((↑) '' Set.range σ) :=
          convexHull_mono (image_mono (σ.range_face_subset j))
            (vertices_subdivideStd_mem_convexHull n (σ.face j) hρ k)
        simpa [C, Subtype.dist_eq] using
          dist_stdBarycenter_mem_convexHull σ hx'
      rw [AffineSimplex.range_append]
      refine diam_le_of_forall_dist_le hC ?_
      intro x hx y hy
      simp only [mem_insert_iff] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · simpa [dist_self] using hC
      · exact hdist hy
      · rw [dist_comm]
        exact hdist hx
      · exact (dist_le_diam_of_mem (Set.finite_range ρ).isBounded hx hy).trans
          hρdiam

lemma diam_range_idSimplex_le (n : ℕ) :
    diam (Set.range (idSimplex n)) ≤
      diam (univ : Set (stdSimplex ℝ (Fin (n + 1)))) :=
  diam_mono (subset_univ _) isBounded_of_compactSpace

/-- After `k` barycentric subdivisions of the identity `n`-simplex,
every remaining piece has vertex-diameter at most the contracted mesh. -/
lemma diam_range_subdivideStd_iterate_le (n k : ℕ)
    {τ : AffineSimplex (stdSimplex ℝ (Fin (n + 1))) n}
    (hτ : τ ∈ ((subdivideStd (q := n) n)^[k]
      (simplex (idSimplex n))).support) :
    diam (Set.range τ) ≤
      barycentricMeshRatio n ^ k * diam (Set.range (idSimplex n)) := by
  induction k generalizing τ with
  | zero =>
      classical
      simp [Function.iterate_zero, simplex, Finsupp.mem_support_single] at hτ
      rcases hτ with ⟨rfl, _⟩
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply'] at hτ
      obtain ⟨ρ, hρ, hτρ⟩ :=
        mem_support_subdivide AffineSimplex.stdBarycenter n hτ
      have h1 := diam_range_subdivideStd_le (q := n) n ρ hτρ
      have h2 := ih hρ
      have h3 :
          barycentricMeshRatio n *
              (barycentricMeshRatio n ^ k * diam (Set.range (idSimplex n))) =
            barycentricMeshRatio n ^ (k + 1) *
              diam (Set.range (idSimplex n)) := by
        rw [← mul_assoc, mul_comm (barycentricMeshRatio n), ← pow_succ]
      exact (h1.trans (mul_le_mul_of_nonneg_left h2
        (barycentricMeshRatio_nonneg n))).trans_eq h3

lemma diam_range_realize_subdivideStd_iterate_le (n k : ℕ)
    {τ : AffineSimplex (stdSimplex ℝ (Fin (n + 1))) n}
    (hτ : τ ∈ ((subdivideStd (q := n) n)^[k]
      (simplex (idSimplex n))).support) :
    diam (Set.range τ.realize) ≤
      barycentricMeshRatio n ^ k *
        diam (univ : Set (stdSimplex ℝ (Fin (n + 1)))) :=
  (diam_range_realize_le τ).trans <|
    (diam_range_subdivideStd_iterate_le n k hτ).trans <|
      mul_le_mul_of_nonneg_left (diam_range_idSimplex_le n)
        (pow_nonneg (barycentricMeshRatio_nonneg n) k)

/-- Iterated barycentric pieces of `Δ^n` become arbitrarily small. -/
lemma exists_subdivideStd_iterate_diam_lt (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ τ ∈ ((subdivideStd (q := n) n)^[k]
        (simplex (idSimplex n))).support,
      diam (Set.range τ.realize) < ε := by
  obtain ⟨k, hk⟩ :=
    exists_barycentricMeshRatio_pow_mul_diam_stdSimplex_lt n hε
  refine ⟨k, fun τ hτ => ?_⟩
  exact (diam_range_realize_subdivideStd_iterate_le n k hτ).trans_lt hk

/-- Every piece of a sufficiently iterated subdivision of a singular
simplex lands in one member of a two-set open cover. -/
lemma exists_subdivideStd_iterate_image_subset_left_or_right
    {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    (σ : C(stdSimplex ℝ (Fin (n + 1)), Y))
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : A ∪ B = univ) :
    ∃ N : ℕ, ∀ τ ∈ ((subdivideStd (q := n) n)^[N]
        (simplex (idSimplex n))).support,
      σ '' Set.range τ.realize ⊆ A ∨
        σ '' Set.range τ.realize ⊆ B := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_diam_lt_forall_image_subset_left_or_right σ hA hB hAB
  obtain ⟨N, hN⟩ := exists_subdivideStd_iterate_diam_lt n hδ
  refine ⟨N, fun τ hτ => ?_⟩
  exact hsmall ⟨τ.realize (stdSimplex.vertex 0), ⟨stdSimplex.vertex 0, rfl⟩⟩
    (hN τ hτ)

end

end PlatonicSolids.SingularExcision
