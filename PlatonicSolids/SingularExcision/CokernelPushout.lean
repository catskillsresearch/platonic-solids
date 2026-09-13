/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import PlatonicSolids.SingularExcision.DegreewisePushout

/-!
# A cokernel model for a preadditive pushout

The pushout of `f : I ⟶ A` and `g : I ⟶ B` is the cokernel of
`(f, -g) : I ⟶ A ⊞ B`.
-/

open CategoryTheory Limits

universe v u

namespace SingularExcision

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C] [HasCokernels C]
variable {I A B P : C} (f : I ⟶ A) (g : I ⟶ B)

/-- The relation map `(f, -g)` presenting a pushout as a cokernel. -/
noncomputable def pushoutRelation : I ⟶ A ⊞ B :=
  biprod.lift f (-g)

omit [HasCokernels C] in
lemma pushoutRelation_eq :
    pushoutRelation f g = f ≫ biprod.inl + (-g) ≫ biprod.inr := by
  ext
  · simp [pushoutRelation, Preadditive.add_comp]
  · simp [pushoutRelation, Preadditive.add_comp]

/-- The two canonical maps into the cokernel of `(f, -g)`. -/
noncomputable def cokernelPushoutInl :
    A ⟶ cokernel (pushoutRelation f g) :=
  biprod.inl ≫ cokernel.π (pushoutRelation f g)

noncomputable def cokernelPushoutInr :
    B ⟶ cokernel (pushoutRelation f g) :=
  biprod.inr ≫ cokernel.π (pushoutRelation f g)

lemma cokernelPushout_comm :
    f ≫ cokernelPushoutInl f g = g ≫ cokernelPushoutInr f g := by
  have h := cokernel.condition (pushoutRelation f g)
  rw [pushoutRelation_eq, Preadditive.add_comp] at h
  rw [← pushoutRelation_eq] at h
  apply sub_eq_zero.mp
  simpa only [cokernelPushoutInl, cokernelPushoutInr, Category.assoc,
    Preadditive.neg_comp, sub_eq_add_neg] using h

/-- The cokernel of `(f, -g)` satisfies the pushout universal property. -/
noncomputable def cokernelIsPushout :
    IsPushout f g (cokernelPushoutInl f g) (cokernelPushoutInr f g) := by
  refine
    { w := cokernelPushout_comm f g
      isColimit' := ⟨PushoutCocone.IsColimit.mk _ ?_ ?_ ?_ ?_⟩ }
  · intro s
    refine cokernel.desc (pushoutRelation f g) (biprod.desc s.inl s.inr) ?_
    rw [pushoutRelation_eq, Preadditive.add_comp]
    simp only [Category.assoc, biprod.inl_desc, biprod.inr_desc]
    simpa only [Preadditive.neg_comp, sub_eq_add_neg] using
      sub_eq_zero.mpr s.condition
  · intro s
    simp [cokernelPushoutInl]
  · intro s
    simp [cokernelPushoutInr]
  · intro s m hmA hmB
    apply (cancel_epi (cokernel.π (pushoutRelation f g))).1
    rw [cokernel.π_desc]
    ext
    · simpa [cokernelPushoutInl, Category.assoc] using hmA
    · simpa [cokernelPushoutInr, Category.assoc] using hmB

/-- Any chosen pushout is canonically isomorphic to the cokernel
presentation. -/
noncomputable def pushoutIsoCokernel {h : A ⟶ P} {k : B ⟶ P}
    (sq : IsPushout f g h k) :
    P ≅ cokernel (pushoutRelation f g) :=
  sq.isoIsPushout _ _ (cokernelIsPushout f g)

section SmallChains

open AlgebraicTopology
open scoped Simplicial

variable {Y : Type} [TopologicalSpace Y]
variable {D : Type*} [Category D] [Abelian D] [HasCoproducts.{0} D]

/-- In every degree, the small-chain object is the cokernel of the
signed map from the infimum of the two lands-in subcomplexes. -/
noncomputable def smallChainDegreeIsoCokernel (R : D)
    (A B : Set Y) (n : ℕ) :
    ((small A B : SSet).chainComplex R).X n ≅
      cokernel
        (pushoutRelation
          ((SSet.chainComplexMap
            (SSet.Subcomplex.homOfLE (inf_le_left :
              landsIn A ⊓ landsIn B ≤ landsIn A)) R).f n)
          ((SSet.chainComplexMap
            (SSet.Subcomplex.homOfLE (inf_le_right :
              landsIn A ⊓ landsIn B ≤ landsIn B)) R).f n)) :=
  pushoutIsoCokernel _ _
    (smallChainDegreeIsPushout R A B n)

end SmallChains

end SingularExcision
