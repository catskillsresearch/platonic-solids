/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PlatonicSolids.MayerVietoris
import PlatonicSolids.SingularExcision.CokernelPushout

/-!
# Cover chains as small singular chains

The singular sets of the three subtypes in a two-set cover are transported
to the two lands-in subcomplexes and their infimum. The resulting pushout
identifies the existing `coverChains` cokernel with the chain complex on
small singular simplices.
-/

open AlgebraicTopology CategoryTheory Limits HomologicalComplex
open scoped Topology

universe v u

namespace SingularExcision

variable {Y : Type} [TopologicalSpace Y]

/-- The singular set of the intersection, expressed as the infimum of the
two ambient lands-in subcomplexes. -/
noncomputable def intersectionSingularSetIso (A B : Set Y) :
    TopCat.toSSet.obj (.of ↥(A ∩ B)) ≅
      ((landsIn A ⊓ landsIn B :
        (TopCat.toSSet.obj (.of Y)).Subcomplex) : SSet) :=
  subtypeSingularSetIso (A ∩ B) ≪≫ landsInInterIso A B

lemma intersectionSingularSetIso_hom_comp_left (A B : Set Y) :
    (intersectionSingularSetIso A B).hom ≫
        SSet.Subcomplex.homOfLE (inf_le_left :
          landsIn A ⊓ landsIn B ≤ landsIn A) =
      TopCat.toSSet.map (interInclLeft A B) ≫
        (subtypeSingularSetIso A).hom := by
  rw [← cancel_mono (landsIn A).ι]
  simp [intersectionSingularSetIso, subtypeSingularSetIso,
    subtypeSingularSetMap, interInclLeft,
    ← Functor.map_comp]
  simpa [interInclLeft, interToLeft] using
    congrArg TopCat.toSSet.map (interToLeft_comp_subtypeIncl A B).symm

lemma intersectionSingularSetIso_hom_comp_right (A B : Set Y) :
    (intersectionSingularSetIso A B).hom ≫
        SSet.Subcomplex.homOfLE (inf_le_right :
          landsIn A ⊓ landsIn B ≤ landsIn B) =
      TopCat.toSSet.map (interInclRight A B) ≫
        (subtypeSingularSetIso B).hom := by
  rw [← cancel_mono (landsIn B).ι]
  simp [intersectionSingularSetIso, subtypeSingularSetIso,
    subtypeSingularSetMap, interInclRight,
    ← Functor.map_comp]
  simpa [interInclRight, interToRight] using
    congrArg TopCat.toSSet.map (interToRight_comp_subtypeIncl A B).symm

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{0} C] [HasPullbacks C]

/-- Chain-level form of `intersectionSingularSetIso`. -/
noncomputable def intersectionChainComplexIso (R : C) (A B : Set Y) :
    ((singularChainComplexFunctor C).obj R).obj (.of ↥(A ∩ B)) ≅
      ((landsIn A ⊓ landsIn B :
        (TopCat.toSSet.obj (.of Y)).Subcomplex) : SSet).chainComplex R :=
  ((SSet.chainComplexFunctor C).obj R).mapIso
    (intersectionSingularSetIso A B)

omit [HasPullbacks C] in
lemma intersectionChainComplexIso_hom_comp_left (R : C) (A B : Set Y) :
    (intersectionChainComplexIso R A B).hom ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (inf_le_left :
            landsIn A ⊓ landsIn B ≤ landsIn A)) R =
      ((singularChainComplexFunctor C).obj R).map (interInclLeft A B) ≫
        (subtypeChainComplexIso R A).hom := by
  simpa [intersectionChainComplexIso, subtypeChainComplexIso,
    singularChainComplexFunctor, SSet.chainComplexMap, Functor.map_comp] using
    congrArg (fun q => ((SSet.chainComplexFunctor C).obj R).map q)
      (intersectionSingularSetIso_hom_comp_left A B)

omit [HasPullbacks C] in
lemma intersectionChainComplexIso_hom_comp_right (R : C) (A B : Set Y) :
    (intersectionChainComplexIso R A B).hom ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (inf_le_right :
            landsIn A ⊓ landsIn B ≤ landsIn B)) R =
      ((singularChainComplexFunctor C).obj R).map (interInclRight A B) ≫
        (subtypeChainComplexIso R B).hom := by
  simpa [intersectionChainComplexIso, subtypeChainComplexIso,
    singularChainComplexFunctor, SSet.chainComplexMap, Functor.map_comp] using
    congrArg (fun q => ((SSet.chainComplexFunctor C).obj R).map q)
      (intersectionSingularSetIso_hom_comp_right A B)

/-- The square of actual subtype singular chains is a pushout onto the
small singular chain complex. -/
noncomputable def subtypeChainsSmallIsPushout (R : C) (A B : Set Y) :
    IsPushout
      (((singularChainComplexFunctor C).obj R).map (interInclLeft A B))
      (((singularChainComplexFunctor C).obj R).map (interInclRight A B))
      ((subtypeChainComplexIso R A).hom ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_left :
            landsIn A ≤ small A B)) R)
      ((subtypeChainComplexIso R B).hom ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_right :
            landsIn B ≤ small A B)) R) := by
  apply (smallChainIsPushout R A B).of_iso'
    (intersectionChainComplexIso R A B)
    (subtypeChainComplexIso R A)
    (subtypeChainComplexIso R B)
    (Iso.refl _)
  · exact intersectionChainComplexIso_hom_comp_left R A B
  · exact intersectionChainComplexIso_hom_comp_right R A B
  · simp only [Iso.refl_hom, Category.comp_id]
    congr
  · simp only [Iso.refl_hom, Category.comp_id]
    congr

/-- The existing Mayer--Vietoris cover-chain cokernel is canonically
isomorphic to the chain complex generated by small singular simplices. -/
noncomputable def coverChainsIsoSmall (R : C) (A B : Set Y) :
    coverChains (C := C) R (interInclLeft A B) (interInclRight A B) ≅
      (small A B : SSet).chainComplex R :=
  (pushoutIsoCokernel
      (((singularChainComplexFunctor C).obj R).map (interInclLeft A B))
      (((singularChainComplexFunctor C).obj R).map (interInclRight A B))
      (subtypeChainsSmallIsPushout R A B)).symm

end SingularExcision
