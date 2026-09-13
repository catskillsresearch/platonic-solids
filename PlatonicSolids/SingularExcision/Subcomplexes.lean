/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import PlatonicSolids.RelativeHomology

/-!
# Singular subcomplexes subordinate to a pair of subsets

The singular simplices which land in a subset form the range subcomplex
of the singular set of the corresponding subtype. The simplices small
with respect to a two-set cover form the supremum of the two ranges.
-/

open AlgebraicTopology CategoryTheory Limits Set
open scoped Topology

namespace SingularExcision

variable {Y : Type} [TopologicalSpace Y]

/-- The map of singular sets induced by the inclusion of a subtype. -/
noncomputable def subtypeSingularSetMap (A : Set Y) :
    TopCat.toSSet.obj (.of ↥A) ⟶ TopCat.toSSet.obj (.of Y) :=
  TopCat.toSSet.map (subtypeIncl Y A)

/-- The singular subcomplex consisting of simplices which factor through `A`. -/
noncomputable abbrev landsIn (A : Set Y) :
    (TopCat.toSSet.obj (.of Y)).Subcomplex :=
  SSet.Subcomplex.range (subtypeSingularSetMap A)

/-- A simplex is small for the pair `(A, B)` if it lands in one member. -/
noncomputable abbrev small (A B : Set Y) :
    (TopCat.toSSet.obj (.of Y)).Subcomplex :=
  landsIn A ⊔ landsIn B

/-- The singular set of a subtype maps onto the corresponding range subcomplex. -/
noncomputable def subtypeToLandsIn (A : Set Y) :
    TopCat.toSSet.obj (.of ↥A) ⟶ (landsIn A : SSet) :=
  SSet.Subcomplex.toRange (subtypeSingularSetMap A)

instance subtypeSingularSetMap_mono (A : Set Y) :
    Mono (subtypeSingularSetMap A) := by
  exact TopCat.toSSet.map_mono (subtypeIncl Y A)

instance subtypeToLandsIn_isIso (A : Set Y) :
    IsIso (subtypeToLandsIn A) := by
  change IsIso (SSet.Subcomplex.toRange (subtypeSingularSetMap A))
  infer_instance

/-- The singular set of `A` is canonically isomorphic to the subcomplex
of ambient singular simplices which land in `A`. -/
noncomputable def subtypeSingularSetIso (A : Set Y) :
    TopCat.toSSet.obj (.of ↥A) ≅ (landsIn A : SSet) :=
  asIso (subtypeToLandsIn A)

@[simp, reassoc]
lemma subtypeToLandsIn_ι (A : Set Y) :
    subtypeToLandsIn A ≫ (landsIn A).ι = subtypeSingularSetMap A :=
  SSet.Subcomplex.toRange_ι _

/-- Under the concrete description of singular simplices, the singular-set
map of a subtype is postcomposition with `Subtype.val`. -/
lemma subtypeSingularSetMap_toSSetObjEquiv (A : Set Y)
    (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj (.of ↥A)).obj n) :
    (TopCat.of Y).toSSetObjEquiv n
        ((subtypeSingularSetMap A).app n σ) =
      (subtypeIncl Y A).hom.comp
        ((TopCat.of ↥A).toSSetObjEquiv n σ) :=
  rfl

/-- The two evident maps out of an intersection subtype. -/
def interToLeft (A B : Set Y) : TopCat.of ↥(A ∩ B) ⟶ TopCat.of ↥A :=
  TopCat.ofHom (ContinuousMap.inclusion fun _ h => h.1)

def interToRight (A B : Set Y) : TopCat.of ↥(A ∩ B) ⟶ TopCat.of ↥B :=
  TopCat.ofHom (ContinuousMap.inclusion fun _ h => h.2)

lemma interToLeft_comp_subtypeIncl (A B : Set Y) :
    interToLeft A B ≫ subtypeIncl Y A = subtypeIncl Y (A ∩ B) := by
  rfl

lemma interToRight_comp_subtypeIncl (A B : Set Y) :
    interToRight A B ≫ subtypeIncl Y B = subtypeIncl Y (A ∩ B) := by
  rfl

/-- Factoring through the intersection is equivalent to factoring through
both subsets. -/
lemma landsIn_inter (A B : Set Y) :
    landsIn (A ∩ B) = landsIn A ⊓ landsIn B := by
  ext n σ
  constructor
  · rintro ⟨τ, rfl⟩
    constructor
    · refine ⟨(TopCat.toSSet.map (interToLeft A B)).app n τ, ?_⟩
      simpa [subtypeSingularSetMap, ← Functor.map_comp] using
        congrArg (fun q => q.app n τ)
          (congrArg TopCat.toSSet.map (interToLeft_comp_subtypeIncl A B))
    · refine ⟨(TopCat.toSSet.map (interToRight A B)).app n τ, ?_⟩
      simpa [subtypeSingularSetMap, ← Functor.map_comp] using
        congrArg (fun q => q.app n τ)
          (congrArg TopCat.toSSet.map (interToRight_comp_subtypeIncl A B))
  · rintro ⟨⟨τA, hA⟩, ⟨τB, hB⟩⟩
    let fA := (TopCat.of ↥A).toSSetObjEquiv n τA
    let fB := (TopCat.of ↥B).toSSetObjEquiv n τB
    have hval : ∀ x, (fA x : Y) = fB x := by
      intro x
      have h := congrArg
        (fun q => (TopCat.of Y).toSSetObjEquiv n q x)
        (hA.trans hB.symm)
      simpa [fA, fB, subtypeSingularSetMap_toSSetObjEquiv] using h
    let fI : C(TopCat.of (stdSimplex ℝ (Fin (n.unop.len + 1))),
        TopCat.of ↥(A ∩ B)) :=
      ⟨fun x => ⟨fA x, (fA x).property, by
          rw [hval x]
          exact (fB x).property⟩,
        (continuous_subtype_val.comp fA.continuous).subtype_mk _⟩
    refine ⟨((TopCat.of ↥(A ∩ B)).toSSetObjEquiv n).symm fI, ?_⟩
    apply (TopCat.of Y).toSSetObjEquiv n |>.injective
    ext x
    simpa [fI, fA, subtypeSingularSetMap_toSSetObjEquiv] using
      congrArg (fun q => (TopCat.of Y).toSSetObjEquiv n q x) hA

/-- The corresponding simplicial sets are canonically isomorphic. -/
noncomputable def landsInInterIso (A B : Set Y) :
    (landsIn (A ∩ B) : SSet) ≅
      ((landsIn A ⊓ landsIn B :
        (TopCat.toSSet.obj (.of Y)).Subcomplex) : SSet) :=
  SSet.Subcomplex.eqToIso (landsIn_inter A B)

@[simp, reassoc]
lemma landsInInterIso_hom_ι (A B : Set Y) :
    (landsInInterIso A B).hom ≫ (landsIn A ⊓ landsIn B).ι =
      (landsIn (A ∩ B)).ι :=
  SSet.Subcomplex.homOfLE_ι (landsIn_inter A B).le

/-- The two lands-in subcomplexes and their infimum/supremum form a
pushout square of simplicial sets. -/
noncomputable def smallIsPushout (A B : Set Y) :
    IsPushout
      (SSet.Subcomplex.homOfLE (inf_le_left :
        landsIn A ⊓ landsIn B ≤ landsIn A))
      (SSet.Subcomplex.homOfLE (inf_le_right :
        landsIn A ⊓ landsIn B ≤ landsIn B))
      (SSet.Subcomplex.homOfLE (le_sup_left :
        landsIn A ≤ small A B))
      (SSet.Subcomplex.homOfLE (le_sup_right :
        landsIn B ≤ small A B)) :=
  (show SSet.Subcomplex.BicartSq
      (landsIn A ⊓ landsIn B) (landsIn A) (landsIn B) (small A B) from
    { sup_eq := rfl
      inf_eq := rfl }).isPushout

/-- Degreewise membership in `landsIn A` is exactly factorization through
the singular set of the subtype. -/
lemma mem_landsIn_iff {A : Set Y} {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj (.of Y)).obj n) :
    σ ∈ (landsIn A).obj n ↔
      ∃ τ : (TopCat.toSSet.obj (.of ↥A)).obj n,
        (subtypeSingularSetMap A).app n τ = σ :=
  Iff.rfl

/-- Degreewise membership in the small subcomplex has the expected
disjunctive description. -/
lemma mem_small_iff {A B : Set Y} {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj (.of Y)).obj n) :
    σ ∈ (small A B).obj n ↔
      σ ∈ (landsIn A).obj n ∨ σ ∈ (landsIn B).obj n :=
  Iff.rfl

end SingularExcision
