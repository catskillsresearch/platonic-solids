/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import PlatonicSolids.SingularExcision.Subcomplexes

/-!
# Degreewise pushouts for small singular chains

The lattice pushout of the two lands-in subcomplexes remains a pushout
after evaluation in each simplicial degree and after applying the free
`R`-object functor `sigmaConst.obj R`.
-/

open AlgebraicTopology CategoryTheory Limits
open scoped Simplicial

namespace SingularExcision

variable {Y : Type} [TopologicalSpace Y]
variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{0} C]

/-- The degreewise pushout square of sets of small singular simplices. -/
noncomputable def smallSimplexSetIsPushout (A B : Set Y)
    (n : SimplexCategoryᵒᵖ) :
    IsPushout
      ((SSet.Subcomplex.homOfLE (inf_le_left :
        landsIn A ⊓ landsIn B ≤ landsIn A)).app n)
      ((SSet.Subcomplex.homOfLE (inf_le_right :
        landsIn A ⊓ landsIn B ≤ landsIn B)).app n)
      ((SSet.Subcomplex.homOfLE (le_sup_left :
        landsIn A ≤ small A B)).app n)
      ((SSet.Subcomplex.homOfLE (le_sup_right :
        landsIn B ≤ small A B)).app n) :=
  (smallIsPushout A B).map ((evaluation SimplexCategoryᵒᵖ (Type)).obj n)

/-- Applying `sigmaConst.obj R` to the degreewise set pushout gives a
pushout in any coefficient category with the required coproducts. -/
noncomputable def smallSigmaConstIsPushout (R : C) (A B : Set Y)
    (n : SimplexCategoryᵒᵖ) :
    IsPushout
      ((sigmaConst.obj R).map
        ((SSet.Subcomplex.homOfLE (inf_le_left :
          landsIn A ⊓ landsIn B ≤ landsIn A)).app n))
      ((sigmaConst.obj R).map
        ((SSet.Subcomplex.homOfLE (inf_le_right :
          landsIn A ⊓ landsIn B ≤ landsIn B)).app n))
      ((sigmaConst.obj R).map
        ((SSet.Subcomplex.homOfLE (le_sup_left :
          landsIn A ≤ small A B)).app n))
      ((sigmaConst.obj R).map
        ((SSet.Subcomplex.homOfLE (le_sup_right :
          landsIn B ≤ small A B)).app n)) :=
  (smallSimplexSetIsPushout A B n).map (sigmaConst.obj R)

/-- The chain complex of the singular set of a subtype is isomorphic to
the chain complex on the corresponding lands-in subcomplex. -/
noncomputable def subtypeChainComplexIso (R : C) (A : Set Y) :
    (TopCat.toSSet.obj (.of ↥A)).chainComplex R ≅
      (landsIn A : SSet).chainComplex R :=
  ((SSet.chainComplexFunctor C).obj R).mapIso (subtypeSingularSetIso A)

/-- In each degree, the maps between chain objects of the two lands-in
subcomplexes and their supremum form a pushout square. -/
noncomputable def smallChainDegreeIsPushout (R : C) (A B : Set Y) (n : ℕ) :
    IsPushout
      ((SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left :
          landsIn A ⊓ landsIn B ≤ landsIn A)) R).f n)
      ((SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_right :
          landsIn A ⊓ landsIn B ≤ landsIn B)) R).f n)
      ((SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_left :
          landsIn A ≤ small A B)) R).f n)
      ((SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_right :
          landsIn B ≤ small A B)) R).f n) := by
  simpa [SSet.chainComplexMap, SSet.chainComplexFunctor,
    AlgebraicTopology.alternatingFaceMapComplex] using
    smallSigmaConstIsPushout R A B (Opposite.op ⦋n⦌)

/-- The degreewise pushout assembles to a pushout of chain complexes. -/
noncomputable def smallChainIsPushout (R : C) (A B : Set Y) :
    IsPushout
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left :
          landsIn A ⊓ landsIn B ≤ landsIn A)) R)
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_right :
          landsIn A ⊓ landsIn B ≤ landsIn B)) R)
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_left :
          landsIn A ≤ small A B)) R)
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_right :
          landsIn B ≤ small A B)) R) := by
  refine
    { w := by
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl
      isColimit' := ⟨?_⟩ }
  apply HomologicalComplex.isColimitOfEval
  intro n
  exact (PushoutCocone.isColimitMapCoconeEquiv _ _).symm
    (smallChainDegreeIsPushout R A B n).isColimit

end SingularExcision
