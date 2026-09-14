/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.CommSq
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.Topology.Instances.AddCircle.Real
import PlatonicSolids.SingularHomology

/-!
The canonical chain map from the simplicial chains of a simplicial set to
the singular chains of its geometric realization.

The intended comparison theorem says that this map is a quasi-isomorphism
for finite nonsingular simplicial sets. This file begins by fixing the
canonical map, its normalized form, and the naturality and reduction lemmas
needed by an attachment proof.
-/

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits HomologicalComplex Module
open scoped Simplicial Topology

variable {k : Type} [Ring k]

universe u

/-- Singular chains on the geometric realization of `X`. -/
abbrev singularChainsOfRealization (R : ModuleCat.{0} k) (X : SSet.{0}) :
    ChainComplex (ModuleCat.{0} k) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj |X|

/-- The canonical comparison from simplicial chains to singular chains of
the geometric realization, induced by the realization--singular adjunction
unit. -/
def simplicialSingularComparison (R : ModuleCat.{0} k) (X : SSet.{0}) :
    X.chainComplex R ⟶ singularChainsOfRealization R X :=
  SSet.chainComplexMap (sSetTopAdj.unit.app X) R

/-- The normalized canonical comparison. -/
def normalizedSimplicialSingularComparison
    (R : ModuleCat.{0} k) (X : SSet.{0}) :
    X.normalizedChainComplex R ⟶ singularChainsOfRealization R X :=
  X.fromNormalizedChainComplex R ≫ simplicialSingularComparison R X

/-- On a simplex generator, the comparison is the singular simplex given by
the canonical realization of that abstract simplex. -/
@[reassoc (attr := simp)]
lemma ι_simplicialSingularComparison
    (R : ModuleCat.{0} k) (X : SSet.{0}) {n : ℕ}
    (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (simplicialSingularComparison R X).f n =
      (TopCat.toSSet.obj |X|).ιChainComplex
        ((sSetTopAdj.unit.app X).app _ x) := by
  exact SSet.ι_chainComplexMap_f X (TopCat.toSSet.obj |X|)
    (sSetTopAdj.unit.app X) R x

/-- The canonical comparison is natural in the simplicial set. -/
lemma simplicialSingularComparison_naturality
    (R : ModuleCat.{0} k) {X Y : SSet.{0}} (f : X ⟶ Y) :
    SSet.chainComplexMap f R ≫ simplicialSingularComparison R Y =
      simplicialSingularComparison R X ≫
        SSet.chainComplexMap
          (TopCat.toSSet.map (SSet.toTop.map f)) R := by
  change
    ((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map f ≫
        ((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (sSetTopAdj.unit.app Y) =
      ((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (sSetTopAdj.unit.app X) ≫
        ((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (TopCat.toSSet.map (SSet.toTop.map f))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp

/-- The normalized comparison is a quasi-isomorphism exactly when the
unnormalized comparison is. -/
lemma normalizedSimplicialSingularComparison_quasiIso_iff
    (R : ModuleCat.{0} k) (X : SSet.{0}) :
    QuasiIso (normalizedSimplicialSingularComparison R X) ↔
      QuasiIso (simplicialSingularComparison R X) := by
  exact quasiIso_iff_comp_left
    (X.fromNormalizedChainComplex R) (simplicialSingularComparison R X)

/-! ## Chain-level gluing for subcomplexes -/

/-- The infimum and supremum of two subcomplexes form a pushout square
after evaluation in each simplicial degree. -/
noncomputable def subcomplexSimplexSetIsPushout
    {X : SSet.{0}} (A B : X.Subcomplex) (n : SimplexCategoryᵒᵖ) :
    IsPushout
      ((SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)).app n)
      ((SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)).app n)
      ((SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)).app n)
      ((SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)).app n) :=
  (show SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) from
    { sup_eq := rfl
      inf_eq := rfl }).isPushout.map
        ((evaluation SimplexCategoryᵒᵖ (Type)).obj n)

/-- Applying the free `R`-module functor preserves the degreewise
subcomplex pushout. -/
noncomputable def subcomplexSigmaConstIsPushout
    (R : ModuleCat.{0} k) {X : SSet.{0}}
    (A B : X.Subcomplex) (n : SimplexCategoryᵒᵖ) :
    IsPushout
      ((sigmaConst.obj R).map
        ((SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)).app n))
      ((sigmaConst.obj R).map
        ((SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)).app n))
      ((sigmaConst.obj R).map
        ((SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)).app n))
      ((sigmaConst.obj R).map
        ((SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)).app n)) :=
  (subcomplexSimplexSetIsPushout A B n).map (sigmaConst.obj R)

/-- In every chain degree, simplicial chains carry the union of two
subcomplexes to the pushout of their chain objects. -/
noncomputable def subcomplexChainDegreeIsPushout
    (R : ModuleCat.{0} k) {X : SSet.{0}}
    (A B : X.Subcomplex) (n : ℕ) :
    IsPushout
      ((SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) R).f n)
      ((SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) R).f n)
      ((SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)) R).f n)
      ((SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) R).f n) := by
  simpa [SSet.chainComplexMap, SSet.chainComplexFunctor,
    AlgebraicTopology.alternatingFaceMapComplex] using
    subcomplexSigmaConstIsPushout R A B (Opposite.op ⦋n⦌)

/-- Simplicial chain complexes turn a union of two subcomplexes into a
pushout square. This is the source-side gluing theorem needed by an
attachment induction. -/
noncomputable def subcomplexChainIsPushout
    (R : ModuleCat.{0} k) {X : SSet.{0}} (A B : X.Subcomplex) :
    IsPushout
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) R)
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) R)
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)) R)
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) R) := by
  refine
    { w := by
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl
      isColimit' := ⟨?_⟩ }
  apply HomologicalComplex.isColimitOfEval
  intro n
  exact (PushoutCocone.isColimitMapCoconeEquiv _ _).symm
    (subcomplexChainDegreeIsPushout R A B n).isColimit

/-! ### The first two-dimensional boundary attachment -/

/-- One edge of the boundary of the standard two-simplex. -/
abbrev boundaryTwoFirstFace :
    (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex :=
  SSet.stdSimplex.face ({0}ᶜ : Finset (Fin 3))

/-- The union of the other two edges of the boundary of the standard
two-simplex. -/
abbrev boundaryTwoRemainingFaces :
    (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex :=
  SSet.stdSimplex.face ({1}ᶜ : Finset (Fin 3)) ⊔
    SSet.stdSimplex.face ({2}ᶜ : Finset (Fin 3))

/-- The boundary of the two-simplex is the union of one edge and the
remaining two-edge path. -/
lemma boundary_two_eq_face_sup :
    (SSet.boundary 2 : (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) =
      boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces := by
  rw [SSet.boundary_eq_iSup]
  apply le_antisymm
  · rw [iSup_le_iff]
    intro i
    fin_cases i
    · exact le_sup_left
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_right
  · rw [← SSet.boundary_eq_iSup]
    exact sup_le
      (SSet.face_singleton_compl_le_boundary (n := 2) 0)
      (sup_le
        (SSet.face_singleton_compl_le_boundary (n := 2) 1)
        (SSet.face_singleton_compl_le_boundary (n := 2) 2))

/-- On simplicial chains, the decomposition of `∂Δ[2]` into an edge
and the other two edges is a pushout square. -/
noncomputable def boundaryTwoChainIsPushout (R : ModuleCat.{0} k) :
    IsPushout
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE
          (inf_le_left :
            boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
              boundaryTwoFirstFace)) R)
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE
          (inf_le_right :
            boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
              boundaryTwoRemainingFaces)) R)
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE
          (le_sup_left :
            boundaryTwoFirstFace ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)) R)
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE
          (le_sup_right :
            boundaryTwoRemainingFaces ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)) R) :=
  subcomplexChainIsPushout R
    boundaryTwoFirstFace boundaryTwoRemainingFaces

/-! ### Source facts for `∂Δ[2]` -/

/-- The simplicial set underlying the boundary of the standard two-simplex. -/
abbrev boundaryTwoSSet : SSet.{0} :=
  (SSet.boundary 2 : (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex)

instance : boundaryTwoSSet.Nonempty :=
  ⟨⟨SSet.stdSimplex.obj₀Equiv.symm 0, by
      simp [SSet.boundary_obj_eq_univ]⟩⟩

/-- Connectedness of simplicial sets is invariant under isomorphism. -/
lemma isConnected_of_sset_iso {X Y : SSet.{0}} (e : X ≅ Y) [X.IsConnected] :
    Y.IsConnected := by
  rw [SSet.isConnected_iff]
  refine ⟨?_, ⟨e.hom.app _ (Classical.arbitrary (X _⦋0⦌))⟩⟩
  have hsub : Subsingleton (SSet.π₀ X) :=
    ((SSet.isConnected_iff (X := X)).mp inferInstance).1
  haveI : IsIso (SSet.π₀Functor.map e.hom) := inferInstance
  have eπ : SSet.π₀ X ≃ SSet.π₀ Y :=
    (asIso (SSet.π₀Functor.map e.hom)).toEquiv
  exact @Equiv.subsingleton (SSet.π₀ Y) (SSet.π₀ X) eπ.symm hsub

/-- The union of two connected subcomplexes that share a vertex is connected. -/
lemma subcomplex_sup_isConnected {X : SSet.{0}} (A B : X.Subcomplex)
    [hA : (A : SSet.{0}).IsConnected] [hB : (B : SSet.{0}).IsConnected]
    (hAB : ((A ⊓ B : X.Subcomplex) : SSet.{0}).Nonempty) :
    ((A ⊔ B : X.Subcomplex) : SSet.{0}).IsConnected := by
  rw [SSet.isConnected_iff]
  constructor
  · constructor
    intro a b
    induction a using SSet.π₀.rec with
    | mk x =>
      induction b using SSet.π₀.rec with
      | mk y =>
        obtain ⟨z₀⟩ := hAB
        let z : ((A ⊔ B : X.Subcomplex) : SSet.{0}) _⦋0⦌ :=
          ⟨z₀.val, (inf_le_left : A ⊓ B ≤ A).trans le_sup_left _ z₀.property⟩
        let inclA : (A : SSet.{0}) ⟶ (A ⊔ B : X.Subcomplex) :=
          SSet.Subcomplex.homOfLE le_sup_left
        let inclB : (B : SSet.{0}) ⟶ (A ⊔ B : X.Subcomplex) :=
          SSet.Subcomplex.homOfLE le_sup_right
        have mem_sup {s : ((A ⊔ B : X.Subcomplex) : SSet.{0}) _⦋0⦌} :
            s.val ∈ A.obj _ ∨ s.val ∈ B.obj _ := by
          rw [← Set.mem_union, ← Subfunctor.max_obj]
          exact s.property
        have eq_of_mem_left {s : ((A ⊔ B : X.Subcomplex) : SSet.{0}) _⦋0⦌}
            (hs : s.val ∈ A.obj _) :
            SSet.π₀.mk s = SSet.π₀.mk z := by
          let sA : (A : SSet.{0}) _⦋0⦌ := ⟨s.val, hs⟩
          let zA : (A : SSet.{0}) _⦋0⦌ :=
            ⟨z₀.val, (inf_le_left : A ⊓ B ≤ A) _ z₀.property⟩
          have hπ : SSet.π₀.mk sA = SSet.π₀.mk zA := Subsingleton.elim _ _
          have hsA : inclA.app _ sA = s := Subtype.ext rfl
          have hzA : inclA.app _ zA = z := Subtype.ext rfl
          simpa [SSet.mapπ₀_mk, hsA, hzA] using congrArg (SSet.mapπ₀ inclA) hπ
        have eq_of_mem_right {s : ((A ⊔ B : X.Subcomplex) : SSet.{0}) _⦋0⦌}
            (hs : s.val ∈ B.obj _) :
            SSet.π₀.mk s = SSet.π₀.mk z := by
          let sB : (B : SSet.{0}) _⦋0⦌ := ⟨s.val, hs⟩
          let zB : (B : SSet.{0}) _⦋0⦌ :=
            ⟨z₀.val, (inf_le_right : A ⊓ B ≤ B) _ z₀.property⟩
          have hπ : SSet.π₀.mk sB = SSet.π₀.mk zB := Subsingleton.elim _ _
          have hsB : inclB.app _ sB = s := Subtype.ext rfl
          have hzB : inclB.app _ zB = z := Subtype.ext rfl
          simpa [SSet.mapπ₀_mk, hsB, hzB] using congrArg (SSet.mapπ₀ inclB) hπ
        have hx := mem_sup (s := x)
        have hy := mem_sup (s := y)
        cases hx with
        | inl hx =>
          cases hy with
          | inl hy => exact (eq_of_mem_left hx).trans (eq_of_mem_left hy).symm
          | inr hy => exact (eq_of_mem_left hx).trans (eq_of_mem_right hy).symm
        | inr hx =>
          cases hy with
          | inl hy => exact (eq_of_mem_right hx).trans (eq_of_mem_left hy).symm
          | inr hy => exact (eq_of_mem_right hx).trans (eq_of_mem_right hy).symm
  · obtain ⟨z₀⟩ := hAB
    exact ⟨⟨z₀.val, (inf_le_left : A ⊓ B ≤ A).trans le_sup_left _ z₀.property⟩⟩

/-- The two remaining faces of `∂Δ[2]` are the horn `Λ[2, 0]`. -/
lemma boundaryTwoRemainingFaces_eq_horn :
    boundaryTwoRemainingFaces = Λ[2, 0] := by
  rw [SSet.horn_eq_iSup]
  refine le_antisymm ?_ ?_
  · exact sup_le
      (le_iSup_of_le ⟨(1 : Fin 3), by decide⟩ le_rfl)
      (le_iSup_of_le ⟨(2 : Fin 3), by decide⟩ le_rfl)
  · rw [iSup_le_iff]
    intro ⟨j, hj⟩
    fin_cases j
    · exact (hj (by decide)).elim
    · exact le_sup_left
    · exact le_sup_right

/-- The boundary of the standard two-simplex is connected. -/
instance boundary_two_isConnected : boundaryTwoSSet.IsConnected := by
  rw [SSet.isConnected_iff]
  constructor
  · constructor
    intro a b
    induction a using SSet.π₀.rec with
    | mk x =>
      induction b using SSet.π₀.rec with
      | mk y =>
        let z : boundaryTwoSSet _⦋0⦌ :=
          ⟨SSet.stdSimplex.obj₀Equiv.symm 0, by
            simp [SSet.boundary_obj_eq_univ]⟩
        have connected_to_z (w : boundaryTwoSSet _⦋0⦌) :
            SSet.π₀.mk z = SSet.π₀.mk w := by
          let s : boundaryTwoSSet _⦋1⦌ :=
            ⟨SSet.stdSimplex.edge 2 0
                (SSet.stdSimplex.obj₀Equiv w.val) (Fin.zero_le _), by
              simp [SSet.boundary_obj_eq_univ]⟩
          have hsrc : boundaryTwoSSet.δ 1 s = z := by
            apply Subtype.ext
            apply SSet.stdSimplex.obj₀Equiv.injective
            rfl
          have htgt : boundaryTwoSSet.δ 0 s = w := by
            apply Subtype.ext
            apply SSet.stdSimplex.obj₀Equiv.injective
            rfl
          rw [← hsrc, ← htgt]
          exact SSet.π₀.sound (SSet.Edge.mk' s)
        exact (connected_to_z x).symm.trans (connected_to_z y)
  · infer_instance

/-- Simplicial homology of `∂Δ[2]` vanishes in degrees at least two. -/
lemma isZero_boundary_two_homology_of_ge_two
    (R : ModuleCat.{0} k) (n : ℕ) (hn : 2 ≤ n) :
    IsZero (boundaryTwoSSet.homology R n) :=
  SSet.isZero_homology_of_hasDimensionLT _ R n 2 hn

/-! ## The representable-simplex case -/

/-- Naturality of the canonical augmentation from simplicial homology in
degree zero to the coefficient object. -/
lemma sset_homology₀ε_natural
    {C : Type u} [Category.{0} C] [HasCoproducts.{0} C]
    [Preadditive C] [CategoryWithHomology C]
    {X Y : SSet.{0}} (f : X ⟶ Y) (R : C) :
    homologyMap (SSet.chainComplexMap f R) 0 ≫ Y.homology₀ε R =
      X.homology₀ε R := by
  let φ := SSet.chainComplexMap f R
  let KX := X.chainComplex R
  let KY := Y.chainComplex R
  apply (cancel_epi (KX.homologyπ 0)).1
  apply (cancel_epi (ChainComplex.cycles₀Iso KX).inv).1
  apply SSet.chainComplex_hom_ext
  intro x
  have hx :
      KX.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) =
        X.ιChainComplex x ≫ (ChainComplex.cycles₀Iso KX).inv := by
    rw [← cancel_mono (KX.iCycles 0)]
    simp [ChainComplex.cycles₀Iso]
    exact (Category.comp_id _).symm
  have hnat := HomologicalComplex.homologyπ_naturality (φ := φ) (i := 0)
  have hcycle := HomologicalComplex.liftCycles_comp_cyclesMap
    (k := X.ιChainComplex x) (j := 0) (hj := by simp) (hk := by simp) φ
  have hf : X.ιChainComplex x ≫ φ.f 0 = Y.ιChainComplex (f.app _ x) :=
    SSet.ι_chainComplexMap_f (X := X) (Y := Y) (f := f) (R := R) x
  have hY := SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε Y R (f.app _ x)
  have hX := SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε X R x
  have lhs :
      X.ιChainComplex x ≫ (ChainComplex.cycles₀Iso KX).inv ≫
        KX.homologyπ 0 ≫ homologyMap φ 0 ≫ Y.homology₀ε R = 𝟙 R := by
    rw [← Category.assoc, ← hx, reassoc_of% hnat, reassoc_of% hcycle]
    exact (congrArg (fun t =>
      KY.liftCycles t 0 (by simp) (by simp) ≫
        KY.homologyπ 0 ≫ Y.homology₀ε R) hf).trans hY
  have rhs :
      X.ιChainComplex x ≫ (ChainComplex.cycles₀Iso KX).inv ≫
        KX.homologyπ 0 ≫ X.homology₀ε R = 𝟙 R := by
    rw [← Category.assoc, ← hx]
    exact hX
  exact lhs.trans rhs.symm

namespace SSet

open stdSimplex

/-- Every representable standard simplex is connected as a simplicial set. -/
instance stdSimplex_isConnected (n : ℕ) : (Δ[n] : SSet.{0}).IsConnected := by
  rw [isConnected_iff]
  constructor
  · constructor
    intro a b
    induction a using SSet.π₀.rec with
    | mk x =>
      induction b using SSet.π₀.rec with
      | mk y =>
        let z : Δ[n] _⦋0⦌ := obj₀Equiv.symm 0
        have hx : SSet.π₀.mk z = SSet.π₀.mk x := by
          let s := edge n 0 (obj₀Equiv x) (Fin.zero_le _)
          have hsrc : (Δ[n] : SSet.{0}).δ 1 s = z := by
            apply obj₀Equiv.injective
            rfl
          have htgt : (Δ[n] : SSet.{0}).δ 0 s = x := by
            apply obj₀Equiv.injective
            rfl
          simpa [hsrc, htgt] using SSet.π₀.sound (SSet.Edge.mk' s)
        have hy : SSet.π₀.mk z = SSet.π₀.mk y := by
          let s := edge n 0 (obj₀Equiv y) (Fin.zero_le _)
          have hsrc : (Δ[n] : SSet.{0}).δ 1 s = z := by
            apply obj₀Equiv.injective
            rfl
          have htgt : (Δ[n] : SSet.{0}).δ 0 s = y := by
            apply obj₀Equiv.injective
            rfl
          simpa [hsrc, htgt] using SSet.π₀.sound (SSet.Edge.mk' s)
        exact hx.symm.trans hy
  · infer_instance

/-- A vertex face of `Δ[n]` is connected. -/
instance stdSimplex_faceSingleton_isConnected {n : ℕ} (i : Fin (n + 1)) :
    (stdSimplex.face ({i} : Finset (Fin (n + 1))) : SSet.{0}).IsConnected :=
  isConnected_of_sset_iso (stdSimplex.faceSingletonIso i)

/-- An edge face of `Δ[n]` is connected. -/
instance stdSimplex_facePair_isConnected {n : ℕ} (i j : Fin (n + 1)) (hij : i < j) :
    (stdSimplex.face ({i, j} : Finset (Fin (n + 1))) : SSet.{0}).IsConnected :=
  isConnected_of_sset_iso (stdSimplex.facePairIso i j hij)

/-- Each complementary edge of `Δ[2]` is connected. -/
instance stdSimplex_faceSingletonCompl_isConnected (i : Fin 3) :
    (stdSimplex.face ({i}ᶜ : Finset (Fin 3)) : SSet.{0}).IsConnected :=
  isConnected_of_sset_iso (stdSimplex.faceSingletonComplIso (n := 1) i)

end SSet

/-- The two-edge horn `Λ[2, 0]` is connected. -/
instance horn_two_zero_isConnected : (Λ[2, 0] : SSet.{0}).IsConnected := by
  rw [← boundaryTwoRemainingFaces_eq_horn]
  refine subcomplex_sup_isConnected
    (SSet.stdSimplex.face ({1}ᶜ : Finset (Fin 3)))
    (SSet.stdSimplex.face ({2}ᶜ : Finset (Fin 3))) ?_
  rw [SSet.stdSimplex.face_inter_face]
  exact ⟨⟨SSet.stdSimplex.obj₀Equiv.symm 0, by
    rw [SSet.stdSimplex.obj₀Equiv_symm_mem_face_iff]
    decide⟩⟩

/-- Reindexing the coproduct of copies of `R` along an injection is monic. -/
lemma sigmaConst_map_mono_of_injective
    (R : ModuleCat.{0} k) {α β : Type} (f : α ⟶ β) (hf : Function.Injective f) :
    Mono ((sigmaConst.obj R).map f) := by
  let e := Equiv.ofInjective f hf
  let reindex : ∐ (fun _ : α ↦ R) ≅ ∐ (fun _ : Set.range f ↦ R) :=
    Sigma.whiskerEquiv e (fun _ ↦ Iso.refl R)
  let incl : ∐ (fun _ : Set.range f ↦ R) ⟶ ∐ (fun _ : β ↦ R) :=
    Sigma.map' (Subtype.val : Set.range f → β) fun _ ↦ 𝟙 R
  classical
  let retr : ∐ (fun _ : β ↦ R) ⟶ ∐ (fun _ : Set.range f ↦ R) :=
    Sigma.desc fun b ↦
      if h : b ∈ Set.range f then
        Sigma.ι (fun _ : Set.range f ↦ R) ⟨b, h⟩
      else
        0
  have hretr : incl ≫ retr = 𝟙 _ := by
    apply colimit.hom_ext
    rintro ⟨⟨b, hb⟩⟩
    dsimp [incl, retr]
    rw [Sigma.ι_comp_map'_assoc, Category.id_comp, Sigma.ι_desc, dif_pos hb,
      Category.comp_id]
  haveI : Mono incl := mono_of_mono_fac hretr
  have hmap : (sigmaConst.obj R).map f = reindex.hom ≫ incl := by
    dsimp [reindex, incl, sigmaConst]
    rw [Sigma.map'_comp_map']
    refine Sigma.map'_eq ?_ fun _ ↦ Category.id_comp _
    ext a
    rfl
  rw [hmap]
  exact mono_comp reindex.hom incl

/-- A monomorphism of simplicial sets remains monic on simplicial chains. -/
lemma chainComplexMap_mono_of_mono {X Y : SSet.{0}} (f : X ⟶ Y) [Mono f]
    (R : ModuleCat.{0} k) :
    Mono (SSet.chainComplexMap f R) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n ↦ ?_
  have : Mono (f.app (Opposite.op ⦋n⦌)) := inferInstance
  have hf : Function.Injective (f.app (Opposite.op ⦋n⦌)) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1 this
  change Mono ((sigmaConst.obj R).map (f.app (Opposite.op ⦋n⦌)))
  exact sigmaConst_map_mono_of_injective R (f.app (Opposite.op ⦋n⦌)) hf

/-- The Mayer–Vietoris short exact sequence of simplicial chains for a
union of two subcomplexes. -/
noncomputable def subcomplexChainShortComplex
    (R : ModuleCat.{0} k) {X : SSet.{0}} (A B : X.Subcomplex) :
    ShortComplex (ChainComplex (ModuleCat.{0} k) ℕ) :=
  (subcomplexChainIsPushout R A B).shortComplex

lemma subcomplexChainShortComplex_shortExact
    (R : ModuleCat.{0} k) {X : SSet.{0}} (A B : X.Subcomplex) :
    (subcomplexChainShortComplex R A B).ShortExact := by
  let h := subcomplexChainIsPushout R A B
  let S := subcomplexChainShortComplex R A B
  let iA := SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)
  haveI : Mono iA := inferInstance
  let iB := SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)
  have hmonoIA : Mono (SSet.chainComplexMap iA R) :=
    chainComplexMap_mono_of_mono iA R
  have hfst : S.f ≫ biprod.fst = SSet.chainComplexMap iA R :=
    biprod.lift_fst (SSet.chainComplexMap iA R) (-SSet.chainComplexMap iB R)
  haveI : Mono S.f :=
    ⟨fun {Z} a b eq ↦ by
      haveI := hmonoIA
      apply (cancel_mono (SSet.chainComplexMap iA R)).1
      simpa [← hfst, ← Category.assoc] using
        congrArg (fun k => k ≫ biprod.fst) eq⟩
  haveI : Epi S.g := h.epi_shortComplex_g
  letI : CategoryWithHomology (ChainComplex (ModuleCat.{0} k) ℕ) :=
    CategoryTheory.categoryWithHomology_of_abelian
  exact ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel h.isColimitCokernelCofork)
    inferInstance inferInstance

/-- Simplicial homology of `Λ[2, 0]` vanishes in degrees at least two. -/
lemma isZero_horn_two_zero_homology_of_ge_two
    (R : ModuleCat.{0} k) (n : ℕ) (hn : 2 ≤ n) :
    IsZero ((Λ[2, 0] : SSet.{0}).homology R n) :=
  SSet.isZero_homology_of_hasDimensionLT _ R n 2 hn

/-- The realization of every representable standard simplex is contractible. -/
instance realization_stdSimplex_contractible (n : ℕ) :
    ContractibleSpace |(SSet.stdSimplex.obj ⦋n⦌ : SSet.{0})| := by
  letI : ContractibleSpace (_root_.stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨(_root_.stdSimplex.vertex 0).1, (_root_.stdSimplex.vertex 0).2⟩
  exact (SimplexCategory.toTopHomeo ⦋n⦌).contractibleSpace

/-- A standard simplex has zero simplicial homology in every positive degree.
This is the chain-level contraction supplied by its extra degeneracy. -/
lemma isZero_stdSimplex_homology
    (R : ModuleCat.{0} k) (n i : ℕ) (hi : i ≠ 0) :
    IsZero ((SSet.stdSimplex.obj ⦋n⦌).homology R i) := by
  let ed := (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋n⦌).map
    (sigmaConst.obj R)
  let he := ed.homotopyEquiv
  letI : QuasiIso he.hom := he.quasiIso_hom
  have hz := HomologicalComplex.isZero_single_obj_homology
    (ComplexShape.down ℕ) 0
    (SimplicialObject.Augmented.point.obj
      (((SimplicialObject.Augmented.whiskering Type (ModuleCat.{0} k)).obj
        (sigmaConst.obj R)).obj (SSet.Augmented.stdSimplex.obj ⦋n⦌))) i hi
  exact hz.of_iso (isoOfQuasiIsoAt he.hom i)

/-- An isomorphism with a standard simplex identifies positive-degree
simplicial homology. -/
lemma isZero_homology_of_stdSimplex_iso
    (R : ModuleCat.{0} k) {X : SSet.{0}} {n : ℕ}
    (e : SSet.stdSimplex.obj ⦋n⦌ ≅ X) (i : ℕ) (hi : i ≠ 0) :
    IsZero (X.homology R i) := by
  haveI : IsIso (SSet.chainComplexMap e.hom R) :=
    Functor.map_isIso _ _
  exact (isZero_stdSimplex_homology R n i hi).of_iso
    (asIso (homologyMap (SSet.chainComplexMap e.hom R) i)).symm

/-- The two remaining faces of `∂Δ[2]` meet at the vertex `0`. -/
lemma boundaryTwoRemainingFaces_inf :
    SSet.stdSimplex.face ({1}ᶜ : Finset (Fin 3)) ⊓
      SSet.stdSimplex.face ({2}ᶜ : Finset (Fin 3)) =
    SSet.stdSimplex.face ({0} : Finset (Fin 3)) := by
  rw [SSet.stdSimplex.face_inter_face]
  congr 1

/-- The last edge of `∂Δ[2]` meets the two-edge horn at the two endpoints. -/
lemma boundaryTwoFirstFace_inf :
    boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces =
      SSet.stdSimplex.face ({1} : Finset (Fin 3)) ⊔
        SSet.stdSimplex.face ({2} : Finset (Fin 3)) := by
  unfold boundaryTwoFirstFace boundaryTwoRemainingFaces
  rw [inf_comm, Subfunctor.max_min, inf_comm,
    inf_comm (a := SSet.stdSimplex.face ({2}ᶜ : Finset (Fin 3)))]
  rw [SSet.stdSimplex.face_inter_face, SSet.stdSimplex.face_inter_face]
  have h2 : ({0}ᶜ ⊓ {1}ᶜ : Finset (Fin 3)) = {2} := by decide
  have h1 : ({0}ᶜ ⊓ {2}ᶜ : Finset (Fin 3)) = {1} := by decide
  rw [h2, h1, sup_comm]

/-- The two endpoints of the last edge are disjoint as faces. -/
lemma face_one_inf_face_two :
    SSet.stdSimplex.face ({1} : Finset (Fin 3)) ⊓
      SSet.stdSimplex.face ({2} : Finset (Fin 3)) = ⊥ := by
  rw [SSet.stdSimplex.face_inter_face]
  have : ({1} ⊓ {2} : Finset (Fin 3)) = ∅ := by decide
  rw [this, SSet.stdSimplex.face_empty]

/-- The two endpoints form a 0-dimensional subcomplex. -/
instance hasDimensionLT_one_twoVertices :
    SSet.HasDimensionLT
      ((SSet.stdSimplex.face ({1} : Finset (Fin 3)) ⊔
        SSet.stdSimplex.face ({2} : Finset (Fin 3)) :
          (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0}) 1 := by
  let A : Bool → (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex :=
    fun b => if b then SSet.stdSimplex.face ({1} : Finset (Fin 3))
      else SSet.stdSimplex.face ({2} : Finset (Fin 3))
  have hA : ⨆ b, A b =
      SSet.stdSimplex.face ({1} : Finset (Fin 3)) ⊔
        SSet.stdSimplex.face ({2} : Finset (Fin 3)) := by
    apply le_antisymm
    · rw [iSup_le_iff]
      intro b
      cases b <;> simp [A]
    · exact sup_le (le_iSup A true) (le_iSup A false)
  rw [← hA]
  exact (SSet.hasDimensionLT_iSup_iff A 1).2 fun b => by
    cases b
    · exact SSet.stdSimplex.hasDimensionLT_face _ 1 (by decide)
    · exact SSet.stdSimplex.hasDimensionLT_face _ 1 (by decide)

/-- The last-edge ∩ horn intersection has vanishing positive simplicial homology. -/
lemma isZero_boundaryTwoFirstFace_inf_homology
    (R : ModuleCat.{0} k) (n : ℕ) (hn : n ≠ 0) :
    IsZero
      (((boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces :
          (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0}).homology R n) := by
  rw [boundaryTwoFirstFace_inf]
  exact SSet.isZero_homology_of_hasDimensionLT _ R n 1 (by omega)

/-- As simplicial sets, `∂Δ[2]` is the union of the last edge and the horn. -/
lemma boundaryTwoSSet_eq_sup :
    boundaryTwoSSet =
      ((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
        (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0}) :=
  congrArg
    (fun C : (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex => (C : SSet.{0}))
    boundary_two_eq_face_sup

/-- The last-edge decomposition of `∂Δ[2]` is a pushout of simplicial sets. -/
lemma boundaryTwo_isPushout :
    IsPushout
      (SSet.Subcomplex.homOfLE
        (inf_le_left :
          boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
            boundaryTwoFirstFace))
      (SSet.Subcomplex.homOfLE
        (inf_le_right :
          boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
            boundaryTwoRemainingFaces))
      (SSet.Subcomplex.homOfLE
        (le_sup_left :
          boundaryTwoFirstFace ≤
            boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))
      (SSet.Subcomplex.homOfLE
        (le_sup_right :
          boundaryTwoRemainingFaces ≤
            boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)) :=
  SSet.Subcomplex.BicartSq.isPushout
    (⟨rfl, rfl⟩ : SSet.Subcomplex.BicartSq
      (boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces)
      boundaryTwoFirstFace boundaryTwoRemainingFaces
      (boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))

/-- Realization preserves the last-edge pushout of `∂Δ[2]`. -/
lemma toTop_boundaryTwo_isPushout :
    IsPushout
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (inf_le_left :
            boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
              boundaryTwoFirstFace)))
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (inf_le_right :
            boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
              boundaryTwoRemainingFaces)))
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_left :
            boundaryTwoFirstFace ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)))
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_right :
            boundaryTwoRemainingFaces ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))) :=
  boundaryTwo_isPushout.map SSet.toTop

/-- Mayer–Vietoris short exact sequence of simplicial chains for the
last-edge decomposition of `∂Δ[2]`. -/
lemma boundaryTwoChainShortExact (R : ModuleCat.{0} k) :
    (subcomplexChainShortComplex R boundaryTwoFirstFace
      boundaryTwoRemainingFaces).ShortExact :=
  subcomplexChainShortComplex_shortExact R _ _

/-- A map into a zero object is an epimorphism. -/
lemma epi_of_isZero_target {C : Type*} [Category* C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) (hY : IsZero Y) : Epi f :=
  ⟨fun _ _ _ => hY.eq_of_src _ _⟩

/-- Homology in a fixed degree preserves binary biproducts of chain complexes. -/
instance preservesBinaryBiproduct_sset_homologyFunctor (n : ℕ)
    (K L : ChainComplex (ModuleCat.{0} k) ℕ) :
    PreservesBinaryBiproduct K L
      (homologyFunctor (ModuleCat.{0} k) (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproduct_of_preservesBiproduct _ K L

/-- The biproduct of two chain complexes with vanishing homology in degree `n`
again has vanishing homology in that degree. -/
lemma isZero_homology_sset_biprod
    {K L : ChainComplex (ModuleCat.{0} k) ℕ} {n : ℕ}
    (hK : IsZero (K.homology n)) (hL : IsZero (L.homology n)) :
    IsZero ((K ⊞ L).homology n) := by
  rw [IsZero.iff_id_eq_zero, ← homologyMap_id (K ⊞ L) n, ← biprod.total]
  rw [homologyMap_add, homologyMap_comp, homologyMap_comp]
  have hf : homologyMap (biprod.fst : K ⊞ L ⟶ K) n = 0 := hK.eq_of_tgt _ _
  have hs : homologyMap (biprod.snd : K ⊞ L ⟶ L) n = 0 := hL.eq_of_tgt _ _
  simp [hf, hs]

/-- `(1, -1) : X ⟶ X ⊞ X` is a monomorphism. -/
lemma mono_biprod_lift_id_neg (X : ModuleCat.{0} k) :
    Mono (biprod.lift (𝟙 X) (-𝟙 X)) :=
  ⟨fun {Z} a b eq ↦ by
    simpa using congrArg (fun t => t ≫ biprod.fst) eq⟩

/-- Complementary edges of `Δ[2]` have vanishing positive simplicial homology. -/
lemma isZero_boundaryTwoFace_homology
    (R : ModuleCat.{0} k) (i : Fin 3) (n : ℕ) (hn : n ≠ 0) :
    IsZero
      ((SSet.stdSimplex.face ({i}ᶜ : Finset (Fin 3)) : SSet.{0}).homology R n) :=
  isZero_homology_of_stdSimplex_iso R
    (SSet.stdSimplex.faceSingletonComplIso (n := 1) i) n hn

/-- The shared vertex of the two remaining faces has vanishing positive
simplicial homology. -/
lemma isZero_boundaryTwoRemainingFaces_inf_homology
    (R : ModuleCat.{0} k) (n : ℕ) (hn : n ≠ 0) :
    IsZero
      (((SSet.stdSimplex.face ({1}ᶜ : Finset (Fin 3)) ⊓
          SSet.stdSimplex.face ({2}ᶜ : Finset (Fin 3)) :
            (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) :
          SSet.{0}).homology R n) := by
  rw [boundaryTwoRemainingFaces_inf]
  exact isZero_homology_of_stdSimplex_iso R
    (SSet.stdSimplex.faceSingletonIso 0) n hn

/-- The Mayer–Vietoris inclusion on `H₀` for a union of connected subcomplexes
is monic: after augmentation it is `(1, -1) : R ⟶ R ⊕ R`. -/
lemma mono_homologyMap_subcomplex_incl_zero
    (R : ModuleCat.{0} k) {X : SSet.{0}} (A B : X.Subcomplex)
    [((A ⊓ B : X.Subcomplex) : SSet.{0}).IsConnected]
    [(A : SSet.{0}).IsConnected] [(B : SSet.{0}).IsConnected] :
    Mono (homologyMap (subcomplexChainShortComplex R A B).f 0) := by
  let S := subcomplexChainShortComplex R A B
  let iA := SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)
  let iB := SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)
  let εA := (A : SSet.{0}).homology₀ε R
  let εB := (B : SSet.{0}).homology₀ε R
  let εW := ((A ⊓ B : X.Subcomplex) : SSet.{0}).homology₀ε R
  let F := homologyFunctor (ModuleCat.{0} k) (ComplexShape.down ℕ) 0
  let e := F.mapBiprod ((A : SSet.{0}).chainComplex R) ((B : SSet.{0}).chainComplex R)
  have hnatA := sset_homology₀ε_natural iA R
  have hnatB := sset_homology₀ε_natural iB R
  have hlift :
      homologyMap S.f 0 ≫ e.hom ≫ biprod.map εA εB =
        εW ≫ biprod.lift (𝟙 R) (-𝟙 R) := by
    change F.map
        (biprod.lift (SSet.chainComplexMap iA R) (-SSet.chainComplexMap iB R)) ≫
        (F.mapBiprod ((A : SSet.{0}).chainComplex R)
          ((B : SSet.{0}).chainComplex R)).hom ≫
        biprod.map εA εB =
      εW ≫ biprod.lift (𝟙 R) (-𝟙 R)
    rw [← Category.assoc, biprod.map_lift_mapBiprod, F.map_neg]
    have hfst : (εW ≫ biprod.lift (𝟙 R) (-𝟙 R)) ≫ biprod.fst = εW := by
      rw [Category.assoc, biprod.lift_fst, Category.comp_id]
    have hsnd : (εW ≫ biprod.lift (𝟙 R) (-𝟙 R)) ≫ biprod.snd = -εW := by
      rw [Category.assoc, biprod.lift_snd, Preadditive.comp_neg, Category.comp_id]
    apply biprod.hom_ext
    · simp [biprod.map_fst]
      exact hnatA.trans hfst.symm
    · simp [biprod.map_snd, Preadditive.neg_comp]
      exact (congrArg Neg.neg hnatB).trans hsnd.symm
  refine ⟨fun {Z} a b eq ↦ ?_⟩
  haveI : IsIso εW := inferInstance
  haveI : Mono (biprod.lift (𝟙 R) (-𝟙 R)) := mono_biprod_lift_id_neg R
  haveI : Mono (εW ≫ biprod.lift (𝟙 R) (-𝟙 R)) := inferInstance
  apply (cancel_mono (εW ≫ biprod.lift (𝟙 R) (-𝟙 R))).1
  simpa [← hlift, ← Category.assoc, S] using
    congrArg (fun t => t ≫ e.hom ≫ biprod.map εA εB) eq

/-- `H₁(Λ[2, 0]) = 0`: the two-edge horn is a tree. -/
lemma isZero_horn_two_zero_homology_one (R : ModuleCat.{0} k) :
    IsZero ((Λ[2, 0] : SSet.{0}).homology R 1) := by
  rw [← boundaryTwoRemainingFaces_eq_horn]
  let A := SSet.stdSimplex.face ({1}ᶜ : Finset (Fin 3))
  let B := SSet.stdSimplex.face ({2}ᶜ : Finset (Fin 3))
  let S := subcomplexChainShortComplex R A B
  have hS := subcomplexChainShortComplex_shortExact R A B
  have hA := isZero_boundaryTwoFace_homology R 1 1 (by decide)
  have hB := isZero_boundaryTwoFace_homology R 2 1 (by decide)
  have hInf := isZero_boundaryTwoRemainingFaces_inf_homology R 1 (by decide)
  have hX₂ : IsZero (S.X₂.homology 1) :=
    isZero_homology_sset_biprod hA hB
  haveI : ((A ⊓ B : (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) :
      SSet.{0}).IsConnected := by
    rw [boundaryTwoRemainingFaces_inf]
    infer_instance
  have hmono0 : Mono (homologyMap S.f 0) :=
    mono_homologyMap_subcomplex_incl_zero R A B
  have hX₃ : S.X₃.ExactAt 1 :=
    hS.exactAt_X₃ (i := 1) (h₁ := epi_of_isZero_target _ hX₂)
      (h₂ := fun j hij => by
        have : j = 0 := by
          simp [ComplexShape.down_Rel] at hij
          exact hij
        subst j
        exact hmono0)
  rwa [exactAt_iff_isZero_homology] at hX₃

/-- Simplicial homology of `Λ[2, 0]` vanishes in every positive degree. -/
lemma isZero_horn_two_zero_homology
    (R : ModuleCat.{0} k) (n : ℕ) (hn : n ≠ 0) :
    IsZero ((Λ[2, 0] : SSet.{0}).homology R n) := by
  by_cases h2 : 2 ≤ n
  · exact isZero_horn_two_zero_homology_of_ge_two R n h2
  · have : n = 1 := by omega
    subst n
    exact isZero_horn_two_zero_homology_one R

/-- The face inclusion `δ₁ : Δ[0] ⟶ Δ[1]` realises as the endpoint `0` of `I`. -/
lemma toTop_map_δ_one_comp_toTopObjIsoI :
    SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      SSet.stdSimplex.toTopObjIsoI.hom =
      TopCat.const (0 : TopCat.I.{0}) := by
  apply (sSetTopAdj.homEquiv (Δ[0] : SSet.{0}) TopCat.I.{0}).injective
  rw [Adjunction.homEquiv_naturality_left]
  change SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.toSSetObjI = _
  rw [SSet.stdSimplex.δ_one_toSSetObjI, sSetTopAdj_homEquiv_stdSimplex_zero]
  simp [TopCat.const_apply]

/-- The face inclusion `δ₀ : Δ[0] ⟶ Δ[1]` realises as the endpoint `1` of `I`. -/
lemma toTop_map_δ_zero_comp_toTopObjIsoI :
    SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) ≫
      SSet.stdSimplex.toTopObjIsoI.hom =
      TopCat.const (1 : TopCat.I.{0}) := by
  apply (sSetTopAdj.homEquiv (Δ[0] : SSet.{0}) TopCat.I.{0}).injective
  rw [Adjunction.homEquiv_naturality_left]
  change SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.stdSimplex.toSSetObjI = _
  rw [SSet.stdSimplex.δ_zero_toSSetObjI, sSetTopAdj_homEquiv_stdSimplex_zero]
  simp [TopCat.const_apply]

/-- `toTop` sends the two-edge horn pushout to a pushout of spaces. -/
lemma toTop_horn₂₀_isPushout :
    IsPushout
      (SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)))
      (SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)))
      (SSet.toTop.map SSet.horn₂₀.ι₀₁)
      (SSet.toTop.map SSet.horn₂₀.ι₀₂) :=
  SSet.horn₂₀.isPushout.map SSet.toTop

/-- The closed interval obtained by gluing two copies of `I` at `0`. -/
abbrev hornIcc : TopCat.{0} := TopCat.of (Set.Icc (-1 : ℝ) 1)

/-- Include `|Δ[1]| ≅ I` as the nonnegative half of `[-1, 1]`. -/
def hornIcc_inl : |(Δ[1] : SSet.{0})| ⟶ hornIcc :=
  TopCat.ofHom
    { toFun := fun x =>
        let t := TopCat.I.homeomorph (SSet.stdSimplex.toTopObjIsoI.hom x)
        ⟨(t : ℝ), (by norm_num : (-1 : ℝ) ≤ 0).trans t.2.1, t.2.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact continuous_induced_dom.comp
          (TopCat.I.homeomorph.continuous.comp
            SSet.stdSimplex.toTopObjIsoI.hom.hom.continuous) }

/-- Include `|Δ[1]| ≅ I` as the nonpositive half of `[-1, 1]`. -/
def hornIcc_inr : |(Δ[1] : SSet.{0})| ⟶ hornIcc :=
  TopCat.ofHom
    { toFun := fun x =>
        let t := TopCat.I.homeomorph (SSet.stdSimplex.toTopObjIsoI.hom x)
        ⟨-(t : ℝ), neg_le_neg t.2.2, (neg_nonpos.2 t.2.1).trans (by norm_num)⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact continuous_neg.comp
          (continuous_induced_dom.comp
            (TopCat.I.homeomorph.continuous.comp
              SSet.stdSimplex.toTopObjIsoI.hom.hom.continuous)) }

lemma hornIcc_inl_δ_one :
    SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) ≫ hornIcc_inl =
      TopCat.const (⟨0, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) := by
  ext x
  have hx : SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) x) = 0 := by
    simpa using congrArg (fun f : _ ⟶ TopCat.I.{0} => f x)
      toTop_map_δ_one_comp_toTopObjIsoI
  simp [hornIcc_inl, hx, TopCat.I.homeomorph_zero]
  rfl

lemma hornIcc_inr_δ_one :
    SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) ≫ hornIcc_inr =
      TopCat.const (⟨0, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) := by
  ext x
  have hx : SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) x) = 0 := by
    simpa using congrArg (fun f : _ ⟶ TopCat.I.{0} => f x)
      toTop_map_δ_one_comp_toTopObjIsoI
  simp [hornIcc_inr, hx, TopCat.I.homeomorph_zero]
  rfl

lemma hornIcc_inl_comp_δ :
    SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) ≫ hornIcc_inl =
      SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) ≫ hornIcc_inr := by
  rw [hornIcc_inl_δ_one, hornIcc_inr_δ_one]

/-- The comparison `|Λ[2, 0]| ⟶ [-1, 1]` induced by the two endpoint-glued intervals. -/
noncomputable def horn_two_zero_toIcc :
    |(Λ[2, 0] : SSet.{0})| ⟶ hornIcc :=
  toTop_horn₂₀_isPushout.desc hornIcc_inl hornIcc_inr hornIcc_inl_comp_δ

lemma toTopObjIsoI_inv_zero :
    SSet.stdSimplex.toTopObjIsoI.inv (0 : TopCat.I.{0}) =
      SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2))
        (default : |(Δ[0] : SSet.{0})|) := by
  have h : SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) default) = 0 := by
    simpa using congrArg (fun f : _ ⟶ TopCat.I.{0} => f default)
      toTop_map_δ_one_comp_toTopObjIsoI
  simpa using (congrArg SSet.stdSimplex.toTopObjIsoI.inv h).symm

lemma horn_two_zero_glue_zero :
    SSet.toTop.map SSet.horn₂₀.ι₀₁
        (SSet.stdSimplex.toTopObjIsoI.inv (0 : TopCat.I.{0})) =
      SSet.toTop.map SSet.horn₂₀.ι₀₂
        (SSet.stdSimplex.toTopObjIsoI.inv (0 : TopCat.I.{0})) := by
  rw [toTopObjIsoI_inv_zero]
  have hw := congrArg (fun f => f (default : |(Δ[0] : SSet.{0})|))
    toTop_horn₂₀_isPushout.w
  simpa using hw

/-- The inverse `[-1, 1] ⟶ |Λ[2, 0]|`, sending the two halves back to the two edges. -/
noncomputable def hornIcc_to_horn_two_zero (t : Set.Icc (-1 : ℝ) 1) :
    |(Λ[2, 0] : SSet.{0})| :=
  if (0 : ℝ) ≤ t.1 then
    SSet.toTop.map SSet.horn₂₀.ι₀₁
      (SSet.stdSimplex.toTopObjIsoI.inv ⟨Set.projIcc (0 : ℝ) 1 zero_le_one t.1⟩)
  else
    SSet.toTop.map SSet.horn₂₀.ι₀₂
      (SSet.stdSimplex.toTopObjIsoI.inv ⟨Set.projIcc (0 : ℝ) 1 zero_le_one (-t.1)⟩)

lemma continuous_hornIcc_to_horn_two_zero :
    Continuous hornIcc_to_horn_two_zero := by
  refine Continuous.if_le
    (f' := fun t : Set.Icc (-1 : ℝ) 1 =>
      SSet.toTop.map SSet.horn₂₀.ι₀₁
        (SSet.stdSimplex.toTopObjIsoI.inv ⟨Set.projIcc (0 : ℝ) 1 zero_le_one t.1⟩))
    (g' := fun t : Set.Icc (-1 : ℝ) 1 =>
      SSet.toTop.map SSet.horn₂₀.ι₀₂
        (SSet.stdSimplex.toTopObjIsoI.inv ⟨Set.projIcc (0 : ℝ) 1 zero_le_one (-t.1)⟩))
    (f := fun _ : Set.Icc (-1 : ℝ) 1 => (0 : ℝ))
    (g := fun t => t.1) ?_ ?_ (by fun_prop) continuous_subtype_val ?_
  · fun_prop
  · fun_prop
  · intro t ht
    have ht0 : t.1 = 0 := ht.symm
    have h0 : Set.projIcc (0 : ℝ) 1 zero_le_one t.1 = ⟨0, by norm_num⟩ := by
      rw [ht0, Set.projIcc_left]
    have h0' : Set.projIcc (0 : ℝ) 1 zero_le_one (-t.1) = ⟨0, by norm_num⟩ := by
      rw [ht0, neg_zero, Set.projIcc_left]
    change SSet.toTop.map SSet.horn₂₀.ι₀₁
        (SSet.stdSimplex.toTopObjIsoI.inv ⟨Set.projIcc (0 : ℝ) 1 zero_le_one t.1⟩) =
      SSet.toTop.map SSet.horn₂₀.ι₀₂
        (SSet.stdSimplex.toTopObjIsoI.inv ⟨Set.projIcc (0 : ℝ) 1 zero_le_one (-t.1)⟩)
    rw [h0, h0']
    exact horn_two_zero_glue_zero

noncomputable def hornIcc_from :
    hornIcc ⟶ |(Λ[2, 0] : SSet.{0})| :=
  TopCat.ofHom ⟨hornIcc_to_horn_two_zero, continuous_hornIcc_to_horn_two_zero⟩

lemma toTopObjIsoI_inv_homeomorph
    (x : |(Δ[1] : SSet.{0})|) :
    SSet.stdSimplex.toTopObjIsoI.inv
        (TopCat.I.homeomorph.symm
          (TopCat.I.homeomorph (SSet.stdSimplex.toTopObjIsoI.hom x))) = x := by
  rw [Homeomorph.symm_apply_apply]
  exact congrArg (fun f : _ ⟶ |(Δ[1] : SSet.{0})| => f x)
    SSet.stdSimplex.toTopObjIsoI.hom_inv_id

lemma hornIcc_from_inl (x : |(Δ[1] : SSet.{0})|) :
    hornIcc_from (hornIcc_inl x) = SSet.toTop.map SSet.horn₂₀.ι₀₁ x := by
  let t := TopCat.I.homeomorph (SSet.stdSimplex.toTopObjIsoI.hom x)
  have ht : (0 : ℝ) ≤ (hornIcc_inl x).1 := t.2.1
  have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one (hornIcc_inl x).1 = t :=
    Set.projIcc_of_mem _ t.2
  change hornIcc_to_horn_two_zero (hornIcc_inl x) = SSet.toTop.map SSet.horn₂₀.ι₀₁ x
  rw [hornIcc_to_horn_two_zero, if_pos ht, hproj]
  exact congrArg (SSet.toTop.map SSet.horn₂₀.ι₀₁) (toTopObjIsoI_inv_homeomorph x)

lemma hornIcc_from_inr (x : |(Δ[1] : SSet.{0})|) :
    hornIcc_from (hornIcc_inr x) = SSet.toTop.map SSet.horn₂₀.ι₀₂ x := by
  let t := TopCat.I.homeomorph (SSet.stdSimplex.toTopObjIsoI.hom x)
  change hornIcc_to_horn_two_zero (hornIcc_inr x) = SSet.toTop.map SSet.horn₂₀.ι₀₂ x
  by_cases h0 : (t : ℝ) = 0
  · have ht : (0 : ℝ) ≤ (hornIcc_inr x).1 := by
      change (0 : ℝ) ≤ -(t : ℝ)
      simp [h0]
    have hproj0 : Set.projIcc (0 : ℝ) 1 zero_le_one (hornIcc_inr x).1 =
        ⟨0, by norm_num⟩ := by
      change Set.projIcc (0 : ℝ) 1 zero_le_one (-(t : ℝ)) = _
      simp [h0, Set.projIcc_left]
    have hx0 : SSet.stdSimplex.toTopObjIsoI.hom x = 0 :=
      TopCat.I.homeomorph.injective (by
        simpa [TopCat.I.homeomorph_zero] using h0)
    rw [hornIcc_to_horn_two_zero, if_pos ht, hproj0]
    have hx := toTopObjIsoI_inv_homeomorph x
    rw [hx0] at hx
    have hx' : SSet.stdSimplex.toTopObjIsoI.inv (0 : TopCat.I.{0}) = x := by
      simpa [TopCat.I.homeomorph_zero] using hx
    have hI0 : (⟨(⟨0, by norm_num⟩ : unitInterval)⟩ : TopCat.I.{0}) = 0 :=
      ULift.ext _ _ (Subtype.ext rfl)
    rw [hI0]
    exact horn_two_zero_glue_zero.trans
      (congrArg (SSet.toTop.map SSet.horn₂₀.ι₀₂) hx')
  · have hneg : ¬ (0 : ℝ) ≤ (hornIcc_inr x).1 := by
      change ¬ (0 : ℝ) ≤ -(t : ℝ)
      have : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm h0)
      exact not_le.mpr (neg_neg_iff_pos.mpr this)
    have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one (-(hornIcc_inr x).1) = t := by
      change Set.projIcc (0 : ℝ) 1 zero_le_one (-(-(t : ℝ))) = t
      rw [neg_neg]
      exact Set.projIcc_of_mem _ t.2
    rw [hornIcc_to_horn_two_zero, if_neg hneg, hproj]
    exact congrArg (SSet.toTop.map SSet.horn₂₀.ι₀₂) (toTopObjIsoI_inv_homeomorph x)

lemma horn_two_zero_toIcc_from :
    horn_two_zero_toIcc ≫ hornIcc_from = 𝟙 _ := by
  apply toTop_horn₂₀_isPushout.hom_ext
  · have h := toTop_horn₂₀_isPushout.inl_desc hornIcc_inl hornIcc_inr
      hornIcc_inl_comp_δ
    change (SSet.toTop.map SSet.horn₂₀.ι₀₁ ≫ horn_two_zero_toIcc) ≫ hornIcc_from =
      SSet.toTop.map SSet.horn₂₀.ι₀₁ ≫ 𝟙 _
    rw [horn_two_zero_toIcc, h, Category.comp_id]
    ext x
    exact hornIcc_from_inl x
  · have h := toTop_horn₂₀_isPushout.inr_desc hornIcc_inl hornIcc_inr
      hornIcc_inl_comp_δ
    change (SSet.toTop.map SSet.horn₂₀.ι₀₂ ≫ horn_two_zero_toIcc) ≫ hornIcc_from =
      SSet.toTop.map SSet.horn₂₀.ι₀₂ ≫ 𝟙 _
    rw [horn_two_zero_toIcc, h, Category.comp_id]
    ext x
    exact hornIcc_from_inr x

lemma horn_two_zero_toIcc_inl (x : |(Δ[1] : SSet.{0})|) :
    horn_two_zero_toIcc (SSet.toTop.map SSet.horn₂₀.ι₀₁ x) = hornIcc_inl x := by
  have h := toTop_horn₂₀_isPushout.inl_desc hornIcc_inl hornIcc_inr
    hornIcc_inl_comp_δ
  exact congrArg (fun f : _ ⟶ hornIcc => f x) (by
    change SSet.toTop.map SSet.horn₂₀.ι₀₁ ≫ horn_two_zero_toIcc = hornIcc_inl
    rwa [horn_two_zero_toIcc])

lemma horn_two_zero_toIcc_inr (x : |(Δ[1] : SSet.{0})|) :
    horn_two_zero_toIcc (SSet.toTop.map SSet.horn₂₀.ι₀₂ x) = hornIcc_inr x := by
  have h := toTop_horn₂₀_isPushout.inr_desc hornIcc_inl hornIcc_inr
    hornIcc_inl_comp_δ
  exact congrArg (fun f : _ ⟶ hornIcc => f x) (by
    change SSet.toTop.map SSet.horn₂₀.ι₀₂ ≫ horn_two_zero_toIcc = hornIcc_inr
    rwa [horn_two_zero_toIcc])

lemma toTopObjIsoI_hom_inv (y : TopCat.I.{0}) :
    SSet.stdSimplex.toTopObjIsoI.hom (SSet.stdSimplex.toTopObjIsoI.inv y) = y :=
  congrArg (fun f : _ ⟶ TopCat.I.{0} => f y)
    SSet.stdSimplex.toTopObjIsoI.inv_hom_id

lemma hornIcc_from_toIcc :
    hornIcc_from ≫ horn_two_zero_toIcc = 𝟙 _ := by
  ext t
  change (horn_two_zero_toIcc (hornIcc_to_horn_two_zero t)).1 = t.1
  by_cases ht : (0 : ℝ) ≤ t.1
  · have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one t.1 = ⟨t.1, ht, t.2.2⟩ :=
      Set.projIcc_of_mem _ ⟨ht, t.2.2⟩
    rw [hornIcc_to_horn_two_zero, if_pos ht, horn_two_zero_toIcc_inl, hproj]
    simp [hornIcc_inl]
    rfl
  · have hneg : ¬ (0 : ℝ) ≤ t.1 := ht
    have htmem : (-t.1) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt (neg_pos.mpr (not_le.mp hneg)),
        (neg_le_neg t.2.1).trans (by norm_num)⟩
    have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one (-t.1) = ⟨-t.1, htmem⟩ :=
      Set.projIcc_of_mem _ htmem
    rw [hornIcc_to_horn_two_zero, if_neg hneg, horn_two_zero_toIcc_inr, hproj]
    simp [hornIcc_inr, TopCat.I.homeomorph]
    exact neg_neg t.1

/-- Geometric realization of the two-edge horn is homeomorphic to `[-1, 1]`. -/
noncomputable def homeomorph_horn_two_zero_Icc :
    |(Λ[2, 0] : SSet.{0})| ≃ₜ Set.Icc (-1 : ℝ) 1 :=
  TopCat.homeoOfIso
    { hom := horn_two_zero_toIcc
      inv := hornIcc_from
      hom_inv_id := horn_two_zero_toIcc_from
      inv_hom_id := hornIcc_from_toIcc }

/-- The realization of `Λ[2, 0]` is contractible: it is two intervals glued
at a common endpoint, hence homeomorphic to a closed interval. -/
instance realization_horn_two_zero_contractible :
    ContractibleSpace |(Λ[2, 0] : SSet.{0})| := by
  letI : ContractibleSpace (Set.Icc (-1 : ℝ) 1) :=
    (convex_Icc (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  exact homeomorph_horn_two_zero_Icc.contractibleSpace

/-- The canonical adjunction-unit chain map is a quasi-isomorphism on every
representable simplex. -/
instance simplicialSingularComparison_stdSimplex_quasiIso
    (R : ModuleCat.{0} k) (n : ℕ) :
    QuasiIso (simplicialSingularComparison R (SSet.stdSimplex.obj ⦋n⦌)) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : i = 0
  · subst i
    let unit := sSetTopAdj.unit.app (SSet.stdSimplex.obj ⦋n⦌)
    have hnat := sset_homology₀ε_natural unit R
    change IsIso (homologyMap (SSet.chainComplexMap unit R) 0)
    letI : IsIso (((SSet.toTop ⋙ TopCat.toSSet).obj
        (SSet.stdSimplex.obj ⦋n⦌)).homology₀ε R) := by
      change IsIso ((TopCat.toSSet.obj |SSet.stdSimplex.obj ⦋n⦌|).homology₀ε R)
      infer_instance
    haveI : IsIso (homologyMap (SSet.chainComplexMap unit R) 0 ≫
        ((SSet.toTop ⋙ TopCat.toSSet).obj
          (SSet.stdSimplex.obj ⦋n⦌)).homology₀ε R) := by
      rw [hnat]
      change IsIso ((SSet.stdSimplex.obj ⦋n⦌).homology₀ε R)
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (((SSet.toTop ⋙ TopCat.toSSet).obj
        (SSet.stdSimplex.obj ⦋n⦌)).homology₀ε R)
  · apply IsZero.isIso
      (isZero_stdSimplex_homology R n i hi)
    exact isZero_singularHomology_of_contractible R hi

/-- If `X` is connected, `|X|` is contractible, and the simplicial homology
of `X` vanishes in positive degree, then the canonical comparison is a
quasi-isomorphism. -/
lemma simplicialSingularComparison_quasiIso_of_contractible
    (R : ModuleCat.{0} k) (X : SSet.{0})
    [X.IsConnected] [ContractibleSpace |X|]
    (hpos : ∀ n, n ≠ 0 → IsZero (X.homology R n)) :
    QuasiIso (simplicialSingularComparison R X) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : i = 0
  · subst i
    let unit := sSetTopAdj.unit.app X
    have hnat := sset_homology₀ε_natural unit R
    change IsIso (homologyMap (SSet.chainComplexMap unit R) 0)
    letI : IsIso (((SSet.toTop ⋙ TopCat.toSSet).obj X).homology₀ε R) := by
      change IsIso ((TopCat.toSSet.obj |X|).homology₀ε R)
      infer_instance
    haveI : IsIso (homologyMap (SSet.chainComplexMap unit R) 0 ≫
        ((SSet.toTop ⋙ TopCat.toSSet).obj X).homology₀ε R) := by
      rw [hnat]
      change IsIso (X.homology₀ε R)
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (((SSet.toTop ⋙ TopCat.toSSet).obj X).homology₀ε R)
  · apply IsZero.isIso (hpos i hi)
    exact isZero_singularHomology_of_contractible R hi

/-- The canonical comparison is a quasi-isomorphism on the two-edge horn. -/
instance simplicialSingularComparison_horn_two_zero_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso (simplicialSingularComparison R (Λ[2, 0] : SSet.{0})) :=
  simplicialSingularComparison_quasiIso_of_contractible R _
    (isZero_horn_two_zero_homology R)

instance normalizedSimplicialSingularComparison_horn_two_zero_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso
      (normalizedSimplicialSingularComparison R (Λ[2, 0] : SSet.{0})) :=
  (normalizedSimplicialSingularComparison_quasiIso_iff R _).2 inferInstance

/-- The normalized comparison is consequently a quasi-isomorphism on every
representable simplex. -/
instance normalizedSimplicialSingularComparison_stdSimplex_quasiIso
    (R : ModuleCat.{0} k) (n : ℕ) :
    QuasiIso
      (normalizedSimplicialSingularComparison R (SSet.stdSimplex.obj ⦋n⦌)) :=
  (normalizedSimplicialSingularComparison_quasiIso_iff R _).2 inferInstance

/-- The comparison is a quasi-isomorphism for a simplicial set isomorphic
to one on which it is already a quasi-isomorphism. -/
lemma simplicialSingularComparison_quasiIso_of_iso
    (R : ModuleCat.{0} k) {X Y : SSet.{0}} (f : X ⟶ Y) [IsIso f]
    [QuasiIso (simplicialSingularComparison R X)] :
    QuasiIso (simplicialSingularComparison R Y) := by
  let F := (SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R
  haveI : IsIso (SSet.toTop.map f) := inferInstance
  haveI : IsIso (TopCat.toSSet.map (SSet.toTop.map f)) := inferInstance
  refine quasiIso_of_arrow_mk_iso
    (simplicialSingularComparison R X)
    (simplicialSingularComparison R Y)
    (Arrow.isoMk (F.mapIso (asIso f))
      (F.mapIso (asIso (TopCat.toSSet.map (SSet.toTop.map f)))) ?_)
  simpa [F, SSet.chainComplexMap] using
    simplicialSingularComparison_naturality R f

/-- Each closed face of `Δ[2]` is isomorphic to `Δ[1]`, so the comparison
is a quasi-isomorphism on every edge of `∂Δ[2]`. -/
instance simplicialSingularComparison_boundaryTwoFace_quasiIso
    (R : ModuleCat.{0} k) (i : Fin 3) :
    QuasiIso
      (simplicialSingularComparison R
        (SSet.stdSimplex.face ({i}ᶜ : Finset (Fin 3)) : SSet.{0})) :=
  simplicialSingularComparison_quasiIso_of_iso R
    (SSet.stdSimplex.faceSingletonComplIso (n := 1) i).hom

/-- The two remaining faces are the horn, so the comparison is a
quasi-isomorphism there as well. -/
instance simplicialSingularComparison_boundaryTwoRemaining_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso
      (simplicialSingularComparison R
        (boundaryTwoRemainingFaces : SSet.{0})) := by
  rw [boundaryTwoRemainingFaces_eq_horn]
  infer_instance

/-- Each vertex face of `Δ[n]` is isomorphic to `Δ[0]`, so the comparison
is a quasi-isomorphism there. -/
instance simplicialSingularComparison_faceSingleton_quasiIso
    (R : ModuleCat.{0} k) {n : ℕ} (i : Fin (n + 1)) :
    QuasiIso
      (simplicialSingularComparison R
        (SSet.stdSimplex.face ({i} : Finset (Fin (n + 1))) : SSet.{0})) :=
  simplicialSingularComparison_quasiIso_of_iso R
    (SSet.stdSimplex.faceSingletonIso i).hom

/-- The two endpoints of the last edge of `∂Δ[2]`. -/
abbrev boundaryTwoVertices :
    (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex :=
  SSet.stdSimplex.face ({1} : Finset (Fin 3)) ⊔
    SSet.stdSimplex.face ({2} : Finset (Fin 3))

lemma face_one_le_boundaryTwoFirstFace :
    SSet.stdSimplex.face ({1} : Finset (Fin 3)) ≤ boundaryTwoFirstFace := by
  rw [SSet.stdSimplex.face_le_face_iff]
  decide

lemma face_two_le_boundaryTwoFirstFace :
    SSet.stdSimplex.face ({2} : Finset (Fin 3)) ≤ boundaryTwoFirstFace := by
  rw [SSet.stdSimplex.face_le_face_iff]
  decide

/-- The inclusion of a vertex face into `Δ[n]` is the constant simplex at
that vertex. -/
lemma faceSingletonIso_hom_comp_ι {n : ℕ} (i : Fin (n + 1)) :
    (SSet.stdSimplex.faceSingletonIso i).hom ≫
      (SSet.stdSimplex.face ({i} : Finset (Fin (n + 1)))).ι =
    SSet.const (SSet.stdSimplex.obj₀Equiv.symm i) := by
  apply (SSet.yonedaEquiv (X := SSet.stdSimplex.obj ⦋n⦌) (n := ⦋0⦌)).injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const]
  set x := SSet.yonedaEquiv (SSet.stdSimplex.faceSingletonIso i).hom
  have hx : x.val = SSet.stdSimplex.obj₀Equiv.symm i := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    have mem := x.property
    rw [SSet.stdSimplex.mem_face_iff] at mem
    have : x.val 0 = i := by
      simpa using mem 0
    simpa [SSet.stdSimplex.obj₀Equiv] using this
  exact hx

/-- `δ₁ ≫ δ₀ : Δ[0] ⟶ Δ[2]` is the vertex `1`. -/
lemma δ_one_comp_δ_zero_eq_const_one :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1) := by
  rw [SSet.stdSimplex.δ_one_eq_const, SSet.const_comp]
  congr 1

/-- `δ₀ ≫ δ₀ : Δ[0] ⟶ Δ[2]` is the vertex `2`. -/
lemma δ_zero_comp_δ_zero_eq_const_two :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm 2) := by
  rw [SSet.stdSimplex.δ_zero_eq_const, SSet.const_comp]
  congr 1

/-- `δ₀ ≫ δ₂ : Δ[0] ⟶ Δ[2]` is the vertex `1`. -/
lemma δ_zero_comp_δ_two_eq_const_one :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1) := by
  rw [SSet.stdSimplex.δ_zero_eq_const, SSet.const_comp]
  congr 1

/-- `δ₀ ≫ δ₁ : Δ[0] ⟶ Δ[2]` is the vertex `2`. -/
lemma δ_zero_comp_δ_one_eq_const_two :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.stdSimplex.δ (1 : Fin 3) =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm 2) := by
  rw [SSet.stdSimplex.δ_zero_eq_const, SSet.const_comp]
  congr 1

/-- Vertex 1 of the last edge is the `δ₁` endpoint of `Δ[1]`. -/
lemma lastEdge_vertex_one :
    (SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
      SSet.Subcomplex.homOfLE face_one_le_boundaryTwoFirstFace =
    SSet.stdSimplex.δ (1 : Fin 2) ≫
      (SSet.stdSimplex.faceSingletonComplIso (n := 1) (0 : Fin 3)).hom := by
  rw [← cancel_mono (boundaryTwoFirstFace.ι)]
  have hι :
      SSet.Subcomplex.homOfLE face_one_le_boundaryTwoFirstFace ≫
        boundaryTwoFirstFace.ι =
      (SSet.stdSimplex.face ({1} : Finset (Fin 3))).ι := rfl
  rw [Category.assoc, hι, Category.assoc,
    SSet.stdSimplex.faceSingletonComplIso_hom_ι,
    faceSingletonIso_hom_comp_ι, δ_one_comp_δ_zero_eq_const_one]

/-- Vertex 2 of the last edge is the `δ₀` endpoint of `Δ[1]`. -/
lemma lastEdge_vertex_two :
    (SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
      SSet.Subcomplex.homOfLE face_two_le_boundaryTwoFirstFace =
    SSet.stdSimplex.δ (0 : Fin 2) ≫
      (SSet.stdSimplex.faceSingletonComplIso (n := 1) (0 : Fin 3)).hom := by
  rw [← cancel_mono (boundaryTwoFirstFace.ι)]
  have hι :
      SSet.Subcomplex.homOfLE face_two_le_boundaryTwoFirstFace ≫
        boundaryTwoFirstFace.ι =
      (SSet.stdSimplex.face ({2} : Finset (Fin 3))).ι := rfl
  rw [Category.assoc, hι, Category.assoc,
    SSet.stdSimplex.faceSingletonComplIso_hom_ι,
    faceSingletonIso_hom_comp_ι, δ_zero_comp_δ_zero_eq_const_two]

/-- The free endpoint of the first horn edge realises as `+1` on `[-1, 1]`. -/
lemma hornIcc_inl_δ_zero :
    SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) ≫ hornIcc_inl =
      TopCat.const (⟨1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) := by
  ext x
  have hx : SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) x) = 1 := by
    simpa using congrArg (fun f : _ ⟶ TopCat.I.{0} => f x)
      toTop_map_δ_zero_comp_toTopObjIsoI
  simp [hornIcc_inl, hx, TopCat.I.homeomorph_one]
  rfl

/-- The free endpoint of the second horn edge realises as `-1` on `[-1, 1]`. -/
lemma hornIcc_inr_δ_zero :
    SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) ≫ hornIcc_inr =
      TopCat.const (⟨-1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) := by
  ext x
  have hx : SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) x) = 1 := by
    simpa using congrArg (fun f : _ ⟶ TopCat.I.{0} => f x)
      toTop_map_δ_zero_comp_toTopObjIsoI
  simp [hornIcc_inr, hx, TopCat.I.homeomorph_one]
  rfl

/-- Vertex 1 of the horn realises as `+1` on `[-1, 1]`. -/
lemma horn_two_zero_toIcc_δ_zero_inl :
    SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) ≫
      SSet.toTop.map SSet.horn₂₀.ι₀₁ ≫ horn_two_zero_toIcc =
      TopCat.const (⟨1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) := by
  have h := toTop_horn₂₀_isPushout.inl_desc hornIcc_inl hornIcc_inr
    hornIcc_inl_comp_δ
  have h' : SSet.toTop.map SSet.horn₂₀.ι₀₁ ≫ horn_two_zero_toIcc = hornIcc_inl := by
    change SSet.toTop.map SSet.horn₂₀.ι₀₁ ≫ horn_two_zero_toIcc = hornIcc_inl
    rwa [horn_two_zero_toIcc]
  rw [h', hornIcc_inl_δ_zero]

/-- Vertex 2 of the horn realises as `-1` on `[-1, 1]`. -/
lemma horn_two_zero_toIcc_δ_zero_inr :
    SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) ≫
      SSet.toTop.map SSet.horn₂₀.ι₀₂ ≫ horn_two_zero_toIcc =
      TopCat.const (⟨-1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) := by
  have h := toTop_horn₂₀_isPushout.inr_desc hornIcc_inl hornIcc_inr
    hornIcc_inl_comp_δ
  have h' : SSet.toTop.map SSet.horn₂₀.ι₀₂ ≫ horn_two_zero_toIcc = hornIcc_inr := by
    change SSet.toTop.map SSet.horn₂₀.ι₀₂ ≫ horn_two_zero_toIcc = hornIcc_inr
    rwa [horn_two_zero_toIcc]
  rw [h', hornIcc_inr_δ_zero]

/-- Realization of the last edge of `∂Δ[2]` is the unit interval. -/
noncomputable def lastEdgeIsoI :
    |(boundaryTwoFirstFace : SSet.{0})| ≅ TopCat.I.{0} :=
  (SSet.toTop.mapIso
    (SSet.stdSimplex.faceSingletonComplIso (n := 1) (0 : Fin 3)).symm).trans
    SSet.stdSimplex.toTopObjIsoI

/-- Vertex 1 of the last edge realises as `0 ∈ I`. -/
lemma lastEdgeIsoI_vertex_one :
    SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE face_one_le_boundaryTwoFirstFace) ≫
      lastEdgeIsoI.hom =
    TopCat.const (0 : TopCat.I.{0}) := by
  rw [lastEdge_vertex_one, lastEdgeIsoI, Iso.trans_hom, SSet.toTop.map_comp]
  change SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      SSet.toTop.map
        (SSet.stdSimplex.faceSingletonComplIso (n := 1) (0 : Fin 3)).hom ≫
      SSet.toTop.map
        (SSet.stdSimplex.faceSingletonComplIso (n := 1) (0 : Fin 3)).inv ≫
      SSet.stdSimplex.toTopObjIsoI.hom =
    TopCat.const (0 : TopCat.I.{0})
  have hcancel :
      SSet.toTop.map
          (SSet.stdSimplex.faceSingletonComplIso (n := 1) (0 : Fin 3)).hom ≫
        SSet.toTop.map
          (SSet.stdSimplex.faceSingletonComplIso (n := 1) (0 : Fin 3)).inv =
        𝟙 _ := by
    rw [← SSet.toTop.map_comp, Iso.hom_inv_id, SSet.toTop.map_id]
  conv_lhs =>
    enter [2]
    rw [← Category.assoc, hcancel, Category.id_comp]
  rw [toTop_map_δ_one_comp_toTopObjIsoI]

/-- Vertex 2 of the last edge realises as `1 ∈ I`. -/
lemma lastEdgeIsoI_vertex_two :
    SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE face_two_le_boundaryTwoFirstFace) ≫
      lastEdgeIsoI.hom =
    TopCat.const (1 : TopCat.I.{0}) := by
  rw [lastEdge_vertex_two, lastEdgeIsoI, Iso.trans_hom, SSet.toTop.map_comp]
  change SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) ≫
      SSet.toTop.map
        (SSet.stdSimplex.faceSingletonComplIso (n := 1) (0 : Fin 3)).hom ≫
      SSet.toTop.map
        (SSet.stdSimplex.faceSingletonComplIso (n := 1) (0 : Fin 3)).inv ≫
      SSet.stdSimplex.toTopObjIsoI.hom =
    TopCat.const (1 : TopCat.I.{0})
  have hcancel :
      SSet.toTop.map
          (SSet.stdSimplex.faceSingletonComplIso (n := 1) (0 : Fin 3)).hom ≫
        SSet.toTop.map
          (SSet.stdSimplex.faceSingletonComplIso (n := 1) (0 : Fin 3)).inv =
        𝟙 _ := by
    rw [← SSet.toTop.map_comp, Iso.hom_inv_id, SSet.toTop.map_id]
  conv_lhs =>
    enter [2]
    rw [← Category.assoc, hcancel, Category.id_comp]
  rw [toTop_map_δ_zero_comp_toTopObjIsoI]

/-! ### The circle obtained from the last-edge decomposition -/

/-- A concrete circle of circumference three. -/
abbrev boundaryCircle : TopCat.{0} :=
  TopCat.of (AddCircle (3 : ℝ))

/-- Map the horn coordinate `[-1, 1]` to the arc `[0, 2]` of the circle. -/
def hornIccToBoundaryCircle : hornIcc ⟶ boundaryCircle :=
  TopCat.ofHom
    { toFun := fun t => ((t.1 + 1 : ℝ) : AddCircle (3 : ℝ))
      continuous_toFun :=
        (AddCircle.continuous_mk' (3 : ℝ)).comp
          (continuous_subtype_val.add continuous_const) }

/-- Map the last-edge coordinate `I` to the complementary arc `[2, 3]`. -/
def unitIntervalToBoundaryCircle : TopCat.I.{0} ⟶ boundaryCircle :=
  TopCat.ofHom
    { toFun := fun t =>
        ((2 + (TopCat.I.homeomorph t : ℝ) : ℝ) : AddCircle (3 : ℝ))
      continuous_toFun :=
        (AddCircle.continuous_mk' (3 : ℝ)).comp
          (continuous_const.add
            (continuous_subtype_val.comp TopCat.I.homeomorph.continuous)) }

/-- The horn as the first closed arc of the concrete circle. -/
noncomputable def hornToBoundaryCircle :
    |(Λ[2, 0] : SSet.{0})| ⟶ boundaryCircle :=
  horn_two_zero_toIcc ≫ hornIccToBoundaryCircle

/-- The last edge as the complementary closed arc of the concrete circle. -/
noncomputable def lastEdgeToBoundaryCircle :
    |(boundaryTwoFirstFace : SSet.{0})| ⟶ boundaryCircle :=
  lastEdgeIsoI.hom ≫ unitIntervalToBoundaryCircle

lemma hornIccToBoundaryCircle_one :
    (TopCat.const (⟨1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) :
      |(Δ[0] : SSet.{0})| ⟶ hornIcc) ≫
      hornIccToBoundaryCircle =
    (TopCat.const ((2 : ℝ) : AddCircle (3 : ℝ)) :
      |(Δ[0] : SSet.{0})| ⟶ boundaryCircle) := by
  ext x
  change (((1 : ℝ) + 1 : ℝ) : AddCircle (3 : ℝ)) = (2 : ℝ)
  norm_num

lemma hornIccToBoundaryCircle_neg_one :
    (TopCat.const (⟨-1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) :
      |(Δ[0] : SSet.{0})| ⟶ hornIcc) ≫
      hornIccToBoundaryCircle =
    (TopCat.const (0 : AddCircle (3 : ℝ)) :
      |(Δ[0] : SSet.{0})| ⟶ boundaryCircle) := by
  ext x
  change (((-1 : ℝ) + 1 : ℝ) : AddCircle (3 : ℝ)) = 0
  norm_num

lemma unitIntervalToBoundaryCircle_zero :
    (TopCat.const (0 : TopCat.I.{0}) :
      |(Δ[0] : SSet.{0})| ⟶ TopCat.I.{0}) ≫ unitIntervalToBoundaryCircle =
      (TopCat.const ((2 : ℝ) : AddCircle (3 : ℝ)) :
        |(Δ[0] : SSet.{0})| ⟶ boundaryCircle) := by
  ext x
  change
    ((2 + (TopCat.I.homeomorph (0 : TopCat.I.{0}) : ℝ) : ℝ) :
      AddCircle (3 : ℝ)) = (2 : ℝ)
  simp

lemma unitIntervalToBoundaryCircle_one :
    (TopCat.const (1 : TopCat.I.{0}) :
      |(Δ[0] : SSet.{0})| ⟶ TopCat.I.{0}) ≫ unitIntervalToBoundaryCircle =
      (TopCat.const (0 : AddCircle (3 : ℝ)) :
        |(Δ[0] : SSet.{0})| ⟶ boundaryCircle) := by
  ext x
  change
    ((2 + (TopCat.I.homeomorph (1 : TopCat.I.{0}) : ℝ) : ℝ) :
      AddCircle (3 : ℝ)) = 0
  rw [TopCat.I.homeomorph_one]
  norm_num

lemma face_one_le_boundaryTwoRemainingFaces :
    SSet.stdSimplex.face ({1} : Finset (Fin 3)) ≤
      boundaryTwoRemainingFaces := by
  apply le_sup_of_le_right
  rw [SSet.stdSimplex.face_le_face_iff]
  decide

lemma face_two_le_boundaryTwoRemainingFaces :
    SSet.stdSimplex.face ({2} : Finset (Fin 3)) ≤
      boundaryTwoRemainingFaces := by
  apply le_sup_of_le_left
  rw [SSet.stdSimplex.face_le_face_iff]
  decide

/-- The identification of the two remaining faces with `Λ[2,0]`. -/
noncomputable def boundaryTwoRemainingFacesIsoHorn :
    (boundaryTwoRemainingFaces : SSet.{0}) ≅ (Λ[2, 0] : SSet.{0}) :=
  SSet.Subcomplex.eqToIso boundaryTwoRemainingFaces_eq_horn

lemma boundaryTwoRemainingFacesIsoHorn_hom_ι :
    boundaryTwoRemainingFacesIsoHorn.hom ≫ Λ[2, 0].ι =
      boundaryTwoRemainingFaces.ι := by
  change
    SSet.Subcomplex.homOfLE boundaryTwoRemainingFaces_eq_horn.le ≫
      Λ[2, 0].ι = boundaryTwoRemainingFaces.ι
  rfl

/-- Vertex 1 of the horn is the free endpoint of its first edge. -/
lemma horn_vertex_one :
    (SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
      SSet.Subcomplex.homOfLE face_one_le_boundaryTwoRemainingFaces ≫
      boundaryTwoRemainingFacesIsoHorn.hom =
    SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.horn₂₀.ι₀₁ := by
  rw [← cancel_mono Λ[2, 0].ι]
  have hι :
      SSet.Subcomplex.homOfLE face_one_le_boundaryTwoRemainingFaces ≫
        boundaryTwoRemainingFaces.ι =
      (SSet.stdSimplex.face ({1} : Finset (Fin 3))).ι := rfl
  rw [Category.assoc, Category.assoc,
    boundaryTwoRemainingFacesIsoHorn_hom_ι, hι, Category.assoc,
    SSet.horn.ι_ι, faceSingletonIso_hom_comp_ι,
    δ_zero_comp_δ_two_eq_const_one]

/-- Vertex 2 of the horn is the free endpoint of its second edge. -/
lemma horn_vertex_two :
    (SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
      SSet.Subcomplex.homOfLE face_two_le_boundaryTwoRemainingFaces ≫
      boundaryTwoRemainingFacesIsoHorn.hom =
    SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.horn₂₀.ι₀₂ := by
  rw [← cancel_mono Λ[2, 0].ι]
  have hι :
      SSet.Subcomplex.homOfLE face_two_le_boundaryTwoRemainingFaces ≫
        boundaryTwoRemainingFaces.ι =
      (SSet.stdSimplex.face ({2} : Finset (Fin 3))).ι := rfl
  rw [Category.assoc, Category.assoc,
    boundaryTwoRemainingFacesIsoHorn_hom_ι, hι, Category.assoc,
    SSet.horn.ι_ι, faceSingletonIso_hom_comp_ι,
    δ_zero_comp_δ_one_eq_const_two]

/-- The two vertex faces form a coproduct square under the empty
subcomplex. -/
lemma boundaryTwoVertices_isPushout :
    IsPushout
      (SSet.Subcomplex.homOfLE
        (bot_le :
          (⊥ : (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) ≤
            SSet.stdSimplex.face ({1} : Finset (Fin 3))))
      (SSet.Subcomplex.homOfLE
        (bot_le :
          (⊥ : (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) ≤
            SSet.stdSimplex.face ({2} : Finset (Fin 3))))
      (SSet.Subcomplex.homOfLE
        (le_sup_left :
          SSet.stdSimplex.face ({1} : Finset (Fin 3)) ≤ boundaryTwoVertices))
      (SSet.Subcomplex.homOfLE
        (le_sup_right :
          SSet.stdSimplex.face ({2} : Finset (Fin 3)) ≤ boundaryTwoVertices)) :=
  SSet.Subcomplex.BicartSq.isPushout
    ({ sup_eq := rfl
       inf_eq := face_one_inf_face_two } :
      SSet.Subcomplex.BicartSq
        (⊥ : (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex)
        (SSet.stdSimplex.face ({1} : Finset (Fin 3)))
        (SSet.stdSimplex.face ({2} : Finset (Fin 3)))
        boundaryTwoVertices)

/-- Realization preserves the coproduct decomposition of the two vertices. -/
lemma toTop_boundaryTwoVertices_isPushout :
    IsPushout
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (bot_le :
            (⊥ : (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) ≤
              SSet.stdSimplex.face ({1} : Finset (Fin 3)))))
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (bot_le :
            (⊥ : (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) ≤
              SSet.stdSimplex.face ({2} : Finset (Fin 3)))))
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_left :
            SSet.stdSimplex.face ({1} : Finset (Fin 3)) ≤ boundaryTwoVertices)))
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_right :
            SSet.stdSimplex.face ({2} : Finset (Fin 3)) ≤ boundaryTwoVertices))) :=
  boundaryTwoVertices_isPushout.map SSet.toTop

/-- The two-edge horn, transported from `boundaryTwoRemainingFaces`, as the
first arc of the concrete circle. -/
noncomputable def boundaryTwoRemainingFacesToBoundaryCircle :
    |(boundaryTwoRemainingFaces : SSet.{0})| ⟶ boundaryCircle :=
  SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom ≫
    hornToBoundaryCircle

lemma lastEdgeToBoundaryCircle_vertex_one :
    SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE face_one_le_boundaryTwoFirstFace) ≫
      lastEdgeToBoundaryCircle =
    (TopCat.const ((2 : ℝ) : AddCircle (3 : ℝ)) :
      |(Δ[0] : SSet.{0})| ⟶ boundaryCircle) := by
  rw [lastEdgeToBoundaryCircle, ← Category.assoc,
    lastEdgeIsoI_vertex_one, unitIntervalToBoundaryCircle_zero]

lemma lastEdgeToBoundaryCircle_vertex_two :
    SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE face_two_le_boundaryTwoFirstFace) ≫
      lastEdgeToBoundaryCircle =
    (TopCat.const (0 : AddCircle (3 : ℝ)) :
      |(Δ[0] : SSet.{0})| ⟶ boundaryCircle) := by
  rw [lastEdgeToBoundaryCircle, ← Category.assoc,
    lastEdgeIsoI_vertex_two, unitIntervalToBoundaryCircle_one]

lemma boundaryTwoRemainingFacesToBoundaryCircle_vertex_one :
    SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE face_one_le_boundaryTwoRemainingFaces) ≫
      boundaryTwoRemainingFacesToBoundaryCircle =
    (TopCat.const ((2 : ℝ) : AddCircle (3 : ℝ)) :
      |(Δ[0] : SSet.{0})| ⟶ boundaryCircle) := by
  rw [boundaryTwoRemainingFacesToBoundaryCircle, hornToBoundaryCircle]
  rw [← Category.assoc, ← SSet.toTop.map_comp]
  simp only [Category.assoc]
  rw [horn_vertex_one]
  have h := congrArg
    (fun f : |(Δ[0] : SSet.{0})| ⟶ hornIcc =>
      f ≫ hornIccToBoundaryCircle)
    horn_two_zero_toIcc_δ_zero_inl
  exact (by
    simpa only [SSet.toTop.map_comp, Category.assoc] using
      h.trans hornIccToBoundaryCircle_one)

lemma boundaryTwoRemainingFacesToBoundaryCircle_vertex_two :
    SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE face_two_le_boundaryTwoRemainingFaces) ≫
      boundaryTwoRemainingFacesToBoundaryCircle =
    (TopCat.const (0 : AddCircle (3 : ℝ)) :
      |(Δ[0] : SSet.{0})| ⟶ boundaryCircle) := by
  rw [boundaryTwoRemainingFacesToBoundaryCircle, hornToBoundaryCircle]
  rw [← Category.assoc, ← SSet.toTop.map_comp]
  simp only [Category.assoc]
  rw [horn_vertex_two]
  have h := congrArg
    (fun f : |(Δ[0] : SSet.{0})| ⟶ hornIcc =>
      f ≫ hornIccToBoundaryCircle)
    horn_two_zero_toIcc_δ_zero_inr
  exact (by
    simpa only [SSet.toTop.map_comp, Category.assoc] using
      h.trans hornIccToBoundaryCircle_neg_one)

lemma boundaryTwoVertices_le_firstFace :
    boundaryTwoVertices ≤ boundaryTwoFirstFace :=
  sup_le face_one_le_boundaryTwoFirstFace face_two_le_boundaryTwoFirstFace

lemma boundaryTwoVertices_le_remainingFaces :
    boundaryTwoVertices ≤ boundaryTwoRemainingFaces :=
  sup_le face_one_le_boundaryTwoRemainingFaces
    face_two_le_boundaryTwoRemainingFaces

lemma faceOne_boundaryCircle_arc_agreement :
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE face_one_le_boundaryTwoFirstFace) ≫
      lastEdgeToBoundaryCircle =
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE face_one_le_boundaryTwoRemainingFaces) ≫
      boundaryTwoRemainingFacesToBoundaryCircle := by
  apply (cancel_epi
    (SSet.toTop.map (SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom)).1
  calc
    _ = SSet.toTop.map
          ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
            SSet.Subcomplex.homOfLE face_one_le_boundaryTwoFirstFace) ≫
          lastEdgeToBoundaryCircle := by
      rw [SSet.toTop.map_comp, Category.assoc]
    _ = (TopCat.const ((2 : ℝ) : AddCircle (3 : ℝ)) :
          |(Δ[0] : SSet.{0})| ⟶ boundaryCircle) :=
      lastEdgeToBoundaryCircle_vertex_one
    _ = SSet.toTop.map
          ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
            SSet.Subcomplex.homOfLE face_one_le_boundaryTwoRemainingFaces) ≫
          boundaryTwoRemainingFacesToBoundaryCircle :=
      boundaryTwoRemainingFacesToBoundaryCircle_vertex_one.symm
    _ = _ := by
      rw [SSet.toTop.map_comp, Category.assoc]

lemma faceTwo_boundaryCircle_arc_agreement :
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE face_two_le_boundaryTwoFirstFace) ≫
      lastEdgeToBoundaryCircle =
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE face_two_le_boundaryTwoRemainingFaces) ≫
      boundaryTwoRemainingFacesToBoundaryCircle := by
  apply (cancel_epi
    (SSet.toTop.map (SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom)).1
  calc
    _ = SSet.toTop.map
          ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
            SSet.Subcomplex.homOfLE face_two_le_boundaryTwoFirstFace) ≫
          lastEdgeToBoundaryCircle := by
      rw [SSet.toTop.map_comp, Category.assoc]
    _ = (TopCat.const (0 : AddCircle (3 : ℝ)) :
          |(Δ[0] : SSet.{0})| ⟶ boundaryCircle) :=
      lastEdgeToBoundaryCircle_vertex_two
    _ = SSet.toTop.map
          ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
            SSet.Subcomplex.homOfLE face_two_le_boundaryTwoRemainingFaces) ≫
          boundaryTwoRemainingFacesToBoundaryCircle :=
      boundaryTwoRemainingFacesToBoundaryCircle_vertex_two.symm
    _ = _ := by
      rw [SSet.toTop.map_comp, Category.assoc]

/-- The two circle arcs agree on the two-vertex intersection. -/
lemma boundaryTwoVertices_boundaryCircle_arc_agreement :
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_firstFace) ≫
      lastEdgeToBoundaryCircle =
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_remainingFaces) ≫
      boundaryTwoRemainingFacesToBoundaryCircle := by
  apply toTop_boundaryTwoVertices_isPushout.hom_ext
  · simp only [← Category.assoc, ← SSet.toTop.map_comp]
    exact faceOne_boundaryCircle_arc_agreement
  · simp only [← Category.assoc, ← SSet.toTop.map_comp]
    exact faceTwo_boundaryCircle_arc_agreement

/-- The actual last-edge/horn intersection identified with its two vertex
faces. -/
noncomputable def boundaryTwoIntersectionIsoVertices :
    ((boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces :
      (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0}) ≅
      (boundaryTwoVertices : SSet.{0}) :=
  SSet.Subcomplex.eqToIso boundaryTwoFirstFace_inf

lemma boundaryTwoIntersectionIsoVertices_inv_comp_first :
    boundaryTwoIntersectionIsoVertices.inv ≫
      SSet.Subcomplex.homOfLE
        (inf_le_left :
          boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
            boundaryTwoFirstFace) =
    SSet.Subcomplex.homOfLE boundaryTwoVertices_le_firstFace := by
  ext n x
  rfl

lemma boundaryTwoIntersectionIsoVertices_inv_comp_remaining :
    boundaryTwoIntersectionIsoVertices.inv ≫
      SSet.Subcomplex.homOfLE
        (inf_le_right :
          boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
            boundaryTwoRemainingFaces) =
    SSet.Subcomplex.homOfLE boundaryTwoVertices_le_remainingFaces := by
  ext n x
  rfl

/-- The last edge and horn circle maps agree on their actual intersection. -/
lemma boundaryTwo_boundaryCircle_arc_agreement :
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (inf_le_left :
            boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
              boundaryTwoFirstFace)) ≫
      lastEdgeToBoundaryCircle =
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (inf_le_right :
            boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
              boundaryTwoRemainingFaces)) ≫
      boundaryTwoRemainingFacesToBoundaryCircle := by
  apply (cancel_epi
    (SSet.toTop.map boundaryTwoIntersectionIsoVertices.inv)).1
  calc
    _ = SSet.toTop.map
          (boundaryTwoIntersectionIsoVertices.inv ≫
            SSet.Subcomplex.homOfLE inf_le_left) ≫
          lastEdgeToBoundaryCircle := by
      rw [SSet.toTop.map_comp, Category.assoc]
    _ = SSet.toTop.map
          (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_firstFace) ≫
          lastEdgeToBoundaryCircle := by
      rw [boundaryTwoIntersectionIsoVertices_inv_comp_first]
    _ = SSet.toTop.map
          (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_remainingFaces) ≫
          boundaryTwoRemainingFacesToBoundaryCircle :=
      boundaryTwoVertices_boundaryCircle_arc_agreement
    _ = SSet.toTop.map
          (boundaryTwoIntersectionIsoVertices.inv ≫
            SSet.Subcomplex.homOfLE inf_le_right) ≫
          boundaryTwoRemainingFacesToBoundaryCircle := by
      rw [boundaryTwoIntersectionIsoVertices_inv_comp_remaining]
    _ = _ := by
      rw [SSet.toTop.map_comp, Category.assoc]

/-- The map from the last-edge pushout to the concrete circle. -/
noncomputable def boundaryTwoSupToBoundaryCircle :
    |((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
      (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0})| ⟶
      boundaryCircle :=
  toTop_boundaryTwo_isPushout.desc
    lastEdgeToBoundaryCircle
    boundaryTwoRemainingFacesToBoundaryCircle
    boundaryTwo_boundaryCircle_arc_agreement

/-- The boundary subcomplex identified with its last-edge decomposition. -/
noncomputable def boundaryTwoIsoSup :
    boundaryTwoSSet ≅
      ((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
        (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0}) :=
  SSet.Subcomplex.eqToIso boundary_two_eq_face_sup

/-- The canonical piecewise-linear map from `|∂Δ[2]|` to a concrete
additive circle. -/
noncomputable def boundaryTwoToBoundaryCircle :
    |boundaryTwoSSet| ⟶ boundaryCircle :=
  SSet.toTop.map boundaryTwoIsoSup.hom ≫ boundaryTwoSupToBoundaryCircle

@[reassoc]
lemma boundaryTwoSupToBoundaryCircle_firstFace :
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_left :
            boundaryTwoFirstFace ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)) ≫
      boundaryTwoSupToBoundaryCircle =
    lastEdgeToBoundaryCircle := by
  apply toTop_boundaryTwo_isPushout.inl_desc

@[reassoc]
lemma boundaryTwoSupToBoundaryCircle_remainingFaces :
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_right :
            boundaryTwoRemainingFaces ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)) ≫
      boundaryTwoSupToBoundaryCircle =
    boundaryTwoRemainingFacesToBoundaryCircle := by
  apply toTop_boundaryTwo_isPushout.inr_desc

lemma lastEdgeIsoI_inv_zero :
    (TopCat.const (0 : TopCat.I.{0}) :
      |(Δ[0] : SSet.{0})| ⟶ TopCat.I.{0}) ≫ lastEdgeIsoI.inv =
    SSet.toTop.map
      ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
        SSet.Subcomplex.homOfLE face_one_le_boundaryTwoFirstFace) := by
  have h := congrArg
    (fun f : |(Δ[0] : SSet.{0})| ⟶ TopCat.I.{0} => f ≫ lastEdgeIsoI.inv)
    lastEdgeIsoI_vertex_one
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

lemma lastEdgeIsoI_inv_one :
    (TopCat.const (1 : TopCat.I.{0}) :
      |(Δ[0] : SSet.{0})| ⟶ TopCat.I.{0}) ≫ lastEdgeIsoI.inv =
    SSet.toTop.map
      ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
        SSet.Subcomplex.homOfLE face_two_le_boundaryTwoFirstFace) := by
  have h := congrArg
    (fun f : |(Δ[0] : SSet.{0})| ⟶ TopCat.I.{0} => f ≫ lastEdgeIsoI.inv)
    lastEdgeIsoI_vertex_two
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

lemma hornIcc_from_one :
    (TopCat.const (⟨1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) :
      |(Δ[0] : SSet.{0})| ⟶ hornIcc) ≫ hornIcc_from =
    SSet.toTop.map
      (SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.horn₂₀.ι₀₁) := by
  have h := congrArg
    (fun f : |(Δ[0] : SSet.{0})| ⟶ hornIcc => f ≫ hornIcc_from)
    horn_two_zero_toIcc_δ_zero_inl
  simpa only [SSet.toTop.map_comp, Category.assoc,
    horn_two_zero_toIcc_from, Category.comp_id] using h.symm

lemma hornIcc_from_neg_one :
    (TopCat.const (⟨-1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) :
      |(Δ[0] : SSet.{0})| ⟶ hornIcc) ≫ hornIcc_from =
    SSet.toTop.map
      (SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.horn₂₀.ι₀₂) := by
  have h := congrArg
    (fun f : |(Δ[0] : SSet.{0})| ⟶ hornIcc => f ≫ hornIcc_from)
    horn_two_zero_toIcc_δ_zero_inr
  simpa only [SSet.toTop.map_comp, Category.assoc,
    horn_two_zero_toIcc_from, Category.comp_id] using h.symm

/-- Put the unit interval back into the last-edge summand of the pushout. -/
noncomputable def unitIntervalToBoundaryTwoSup :
    TopCat.I.{0} ⟶
      |((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
        (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0})| :=
  lastEdgeIsoI.inv ≫
    SSet.toTop.map
      (SSet.Subcomplex.homOfLE
        (le_sup_left :
          boundaryTwoFirstFace ≤
            boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))

/-- Put `[-1,1]` back into the horn summand of the pushout. -/
noncomputable def hornIccToBoundaryTwoSup :
    hornIcc ⟶
      |((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
        (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0})| :=
  hornIcc_from ≫ SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv ≫
    SSet.toTop.map
      (SSet.Subcomplex.homOfLE
        (le_sup_right :
          boundaryTwoRemainingFaces ≤
            boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))

lemma horn_vertex_one_comp_iso_inv :
    (SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.horn₂₀.ι₀₁) ≫
      boundaryTwoRemainingFacesIsoHorn.inv =
    (SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
      SSet.Subcomplex.homOfLE face_one_le_boundaryTwoRemainingFaces := by
  have h := congrArg
    (fun f : (Δ[0] : SSet.{0}) ⟶ (Λ[2, 0] : SSet.{0}) =>
      f ≫ boundaryTwoRemainingFacesIsoHorn.inv)
    horn_vertex_one
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

lemma horn_vertex_two_comp_iso_inv :
    (SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.horn₂₀.ι₀₂) ≫
      boundaryTwoRemainingFacesIsoHorn.inv =
    (SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
      SSet.Subcomplex.homOfLE face_two_le_boundaryTwoRemainingFaces := by
  have h := congrArg
    (fun f : (Δ[0] : SSet.{0}) ⟶ (Λ[2, 0] : SSet.{0}) =>
      f ≫ boundaryTwoRemainingFacesIsoHorn.inv)
    horn_vertex_two
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

/-- At vertex 1, the last-edge coordinate `0` and horn coordinate `1`
give the same point of the pushout. -/
lemma unitIntervalToBoundaryTwoSup_zero :
    (TopCat.const (0 : TopCat.I.{0}) :
      |(Δ[0] : SSet.{0})| ⟶ TopCat.I.{0}) ≫
      unitIntervalToBoundaryTwoSup =
    (TopCat.const (⟨1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) :
      |(Δ[0] : SSet.{0})| ⟶ hornIcc) ≫
      hornIccToBoundaryTwoSup := by
  rw [unitIntervalToBoundaryTwoSup, hornIccToBoundaryTwoSup,
    ← Category.assoc, lastEdgeIsoI_inv_zero,
    ← Category.assoc, hornIcc_from_one]
  simp only [Category.assoc, ← SSet.toTop.map_comp]
  have hv := congrArg
    (fun f : (Δ[0] : SSet.{0}) ⟶
        (boundaryTwoRemainingFaces : SSet.{0}) =>
      f ≫ SSet.Subcomplex.homOfLE
        (le_sup_right :
          boundaryTwoRemainingFaces ≤
            boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))
    horn_vertex_one_comp_iso_inv
  simp only [Category.assoc] at hv
  rw [hv]
  congr 1

/-- At vertex 2, the last-edge coordinate `1` and horn coordinate `-1`
give the same point of the pushout. -/
lemma unitIntervalToBoundaryTwoSup_one :
    (TopCat.const (1 : TopCat.I.{0}) :
      |(Δ[0] : SSet.{0})| ⟶ TopCat.I.{0}) ≫
      unitIntervalToBoundaryTwoSup =
    (TopCat.const (⟨-1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) :
      |(Δ[0] : SSet.{0})| ⟶ hornIcc) ≫
      hornIccToBoundaryTwoSup := by
  rw [unitIntervalToBoundaryTwoSup, hornIccToBoundaryTwoSup,
    ← Category.assoc, lastEdgeIsoI_inv_one,
    ← Category.assoc, hornIcc_from_neg_one]
  simp only [Category.assoc, ← SSet.toTop.map_comp]
  have hv := congrArg
    (fun f : (Δ[0] : SSet.{0}) ⟶
        (boundaryTwoRemainingFaces : SSet.{0}) =>
      f ≫ SSet.Subcomplex.homOfLE
        (le_sup_right :
          boundaryTwoRemainingFaces ≤
            boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))
    horn_vertex_two_comp_iso_inv
  simp only [Category.assoc] at hv
  rw [hv]
  congr 1

/-- A path through the two pushout arcs, parametrized by `[0,3]` and
extended continuously to all of `ℝ` using interval projections. -/
noncomputable def boundaryCircleLiftPath (x : ℝ) :
    |((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
      (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0})| :=
  if x ≤ 2 then
    hornIccToBoundaryTwoSup
      (Set.projIcc (-1 : ℝ) 1 (by norm_num) (x - 1))
  else
    unitIntervalToBoundaryTwoSup
      (TopCat.I.homeomorph.symm
        (Set.projIcc (0 : ℝ) 1 zero_le_one (x - 2)))

lemma continuous_boundaryCircleLiftPath :
    Continuous boundaryCircleLiftPath := by
  refine Continuous.if_le
    (f' := fun x : ℝ =>
      hornIccToBoundaryTwoSup
        (Set.projIcc (-1 : ℝ) 1 (by norm_num) (x - 1)))
    (g' := fun x : ℝ =>
      unitIntervalToBoundaryTwoSup
        (TopCat.I.homeomorph.symm
          (Set.projIcc (0 : ℝ) 1 zero_le_one (x - 2))))
    (f := fun x : ℝ => x) (g := fun _ => (2 : ℝ))
    ?_ ?_ continuous_id continuous_const ?_
  · fun_prop
  · fun_prop
  · intro x hx
    have hx2 : x = 2 := hx
    subst x
    have hpHorn :
        Set.projIcc (-1 : ℝ) 1 (by norm_num) (2 - 1) =
          ⟨1, by norm_num⟩ := by
      norm_num [Set.projIcc_right]
    have hpEdge :
        Set.projIcc (0 : ℝ) 1 zero_le_one (2 - 2) =
          ⟨0, by norm_num⟩ := by
      norm_num [Set.projIcc_left]
    change
      hornIccToBoundaryTwoSup
          (Set.projIcc (-1 : ℝ) 1 (by norm_num) (2 - 1)) =
        unitIntervalToBoundaryTwoSup
          (TopCat.I.homeomorph.symm
            (Set.projIcc (0 : ℝ) 1 zero_le_one (2 - 2)))
    rw [hpHorn, hpEdge]
    have h := congrArg
      (fun f : |(Δ[0] : SSet.{0})| ⟶
          |((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
            (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0})| =>
        f (default : |(Δ[0] : SSet.{0})|))
      unitIntervalToBoundaryTwoSup_zero
    simpa using h.symm

lemma boundaryCircleLiftPath_zero_eq_three :
    boundaryCircleLiftPath 0 = boundaryCircleLiftPath 3 := by
  have hpHorn :
      Set.projIcc (-1 : ℝ) 1 (by norm_num) (0 - 1) =
        ⟨-1, by norm_num⟩ := by
    norm_num [Set.projIcc_left]
  have hpEdge :
      Set.projIcc (0 : ℝ) 1 zero_le_one (3 - 2) =
        ⟨1, by norm_num⟩ := by
    norm_num [Set.projIcc_right]
  rw [boundaryCircleLiftPath, if_pos (by norm_num), hpHorn,
    boundaryCircleLiftPath, if_neg (by norm_num), hpEdge]
  have h := congrArg
    (fun f : |(Δ[0] : SSet.{0})| ⟶
        |((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
          (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0})| =>
      f (default : |(Δ[0] : SSet.{0})|))
    unitIntervalToBoundaryTwoSup_one
  simpa using h.symm

/-- The inverse circle map obtained by traversing the horn and last edge. -/
noncomputable def boundaryCircleToBoundaryTwoSup :
    boundaryCircle ⟶
      |((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
        (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0})| := by
  letI : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩
  exact TopCat.ofHom
    { toFun := AddCircle.liftIco (3 : ℝ) 0 boundaryCircleLiftPath
      continuous_toFun :=
        AddCircle.liftIco_zero_continuous boundaryCircleLiftPath_zero_eq_three
          continuous_boundaryCircleLiftPath.continuousOn }

lemma boundaryCircleToBoundaryTwoSup_hornIcc
    (t : Set.Icc (-1 : ℝ) 1) :
    boundaryCircleToBoundaryTwoSup (hornIccToBoundaryCircle t) =
      hornIccToBoundaryTwoSup t := by
  letI : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩
  have htIco : t.1 + 1 ∈ Set.Ico (0 : ℝ) 3 :=
    ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
  change
    AddCircle.liftIco (3 : ℝ) 0 boundaryCircleLiftPath
        ((t.1 + 1 : ℝ) : AddCircle (3 : ℝ)) =
      hornIccToBoundaryTwoSup t
  rw [AddCircle.liftIco_zero_coe_apply htIco, boundaryCircleLiftPath,
    if_pos (by linarith [t.2.2])]
  have hval : t.1 + 1 - 1 = t.1 := by ring
  have hp :
      Set.projIcc (-1 : ℝ) 1 (by norm_num) (t.1 + 1 - 1) = t := by
    rw [hval]
    exact Set.projIcc_of_mem _ t.2
  rw [hp]

lemma boundaryCircleToBoundaryTwoSup_unitInterval
    (t : TopCat.I.{0}) :
    boundaryCircleToBoundaryTwoSup (unitIntervalToBoundaryCircle t) =
      unitIntervalToBoundaryTwoSup t := by
  letI : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩
  let u := TopCat.I.homeomorph t
  by_cases h1 : (u : ℝ) = 1
  · have ht : t = 1 := by
      apply TopCat.I.homeomorph.injective
      apply Subtype.ext
      simpa [u, TopCat.I.homeomorph_one] using h1
    subst t
    have hcircle := congrArg
      (fun f : |(Δ[0] : SSet.{0})| ⟶ boundaryCircle =>
        boundaryCircleToBoundaryTwoSup
          (f (default : |(Δ[0] : SSet.{0})|)))
      unitIntervalToBoundaryCircle_one
    have hglue := congrArg
      (fun f : |(Δ[0] : SSet.{0})| ⟶
          |((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
            (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0})| =>
        f (default : |(Δ[0] : SSet.{0})|))
      unitIntervalToBoundaryTwoSup_one
    change
      boundaryCircleToBoundaryTwoSup
          (unitIntervalToBoundaryCircle (1 : TopCat.I.{0})) =
        unitIntervalToBoundaryTwoSup (1 : TopCat.I.{0})
    have hcircle' :
        boundaryCircleToBoundaryTwoSup
            (unitIntervalToBoundaryCircle (1 : TopCat.I.{0})) =
          boundaryCircleToBoundaryTwoSup (0 : AddCircle (3 : ℝ)) := by
      simpa using hcircle
    rw [hcircle']
    change
      AddCircle.liftIco (3 : ℝ) 0 boundaryCircleLiftPath
          ((0 : ℝ) : AddCircle (3 : ℝ)) =
        unitIntervalToBoundaryTwoSup (1 : TopCat.I.{0})
    rw [AddCircle.liftIco_zero_coe_apply
      (p := (3 : ℝ)) (x := (0 : ℝ)) (by norm_num)]
    rw [boundaryCircleLiftPath, if_pos (by norm_num)]
    have hp :
        Set.projIcc (-1 : ℝ) 1 (by norm_num) (0 - 1) =
          ⟨-1, by norm_num⟩ := by
      norm_num [Set.projIcc_left]
    rw [hp]
    simpa using hglue.symm
  · have hu_lt : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 h1
    have hxIco : 2 + (u : ℝ) ∈ Set.Ico (0 : ℝ) 3 :=
      ⟨by linarith [u.2.1], by linarith⟩
    change
      AddCircle.liftIco (3 : ℝ) 0 boundaryCircleLiftPath
          ((2 + (u : ℝ) : ℝ) : AddCircle (3 : ℝ)) =
        unitIntervalToBoundaryTwoSup t
    rw [AddCircle.liftIco_zero_coe_apply hxIco, boundaryCircleLiftPath]
    by_cases h0 : (u : ℝ) = 0
    · have ht : t = 0 := by
        apply TopCat.I.homeomorph.injective
        apply Subtype.ext
        simpa [u, TopCat.I.homeomorph_zero] using h0
      subst t
      rw [if_pos (by simp [u])]
      have hp :
          Set.projIcc (-1 : ℝ) 1 (by norm_num)
              (2 + (u : ℝ) - 1) =
            ⟨1, by norm_num⟩ := by
        rw [h0]
        norm_num [Set.projIcc_right]
      rw [hp]
      have hglue := congrArg
        (fun f : |(Δ[0] : SSet.{0})| ⟶
            |((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
              (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0})| =>
          f (default : |(Δ[0] : SSet.{0})|))
        unitIntervalToBoundaryTwoSup_zero
      simpa using hglue.symm
    · have hu_pos : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm h0)
      rw [if_neg (by linarith)]
      have hp :
          Set.projIcc (0 : ℝ) 1 zero_le_one
              (2 + (u : ℝ) - 2) = u := by
        have hval : 2 + (u : ℝ) - 2 = (u : ℝ) := by ring
        rw [hval]
        exact Set.projIcc_of_mem _ u.2
      rw [hp, Homeomorph.symm_apply_apply]

lemma lastEdgeToBoundaryCircle_comp_inverse :
    lastEdgeToBoundaryCircle ≫ boundaryCircleToBoundaryTwoSup =
    SSet.toTop.map
      (SSet.Subcomplex.homOfLE
        (le_sup_left :
          boundaryTwoFirstFace ≤
            boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)) := by
  ext x
  change
    boundaryCircleToBoundaryTwoSup
        (unitIntervalToBoundaryCircle (lastEdgeIsoI.hom x)) =
      SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_left :
            boundaryTwoFirstFace ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)) x
  rw [boundaryCircleToBoundaryTwoSup_unitInterval]
  change
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_left :
            boundaryTwoFirstFace ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))
      (lastEdgeIsoI.inv (lastEdgeIsoI.hom x)) =
    _
  have hx := congrArg
    (fun f : |(boundaryTwoFirstFace : SSet.{0})| ⟶
        |(boundaryTwoFirstFace : SSet.{0})| => f x)
    lastEdgeIsoI.hom_inv_id
  have hx' : lastEdgeIsoI.inv (lastEdgeIsoI.hom x) = x := by
    change (lastEdgeIsoI.hom ≫ lastEdgeIsoI.inv) x = x
    exact hx
  rw [hx']

lemma boundaryTwoRemainingFacesToBoundaryCircle_comp_inverse :
    boundaryTwoRemainingFacesToBoundaryCircle ≫
      boundaryCircleToBoundaryTwoSup =
    SSet.toTop.map
      (SSet.Subcomplex.homOfLE
        (le_sup_right :
          boundaryTwoRemainingFaces ≤
            boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)) := by
  ext x
  change
    boundaryCircleToBoundaryTwoSup
        (hornIccToBoundaryCircle
          (horn_two_zero_toIcc
            (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom x))) =
      SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_right :
            boundaryTwoRemainingFaces ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)) x
  rw [boundaryCircleToBoundaryTwoSup_hornIcc]
  change
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_right :
            boundaryTwoRemainingFaces ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))
      (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv
        (hornIcc_from
          (horn_two_zero_toIcc
            (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom x)))) =
      _
  have hHorn := congrArg
    (fun f : |(Λ[2, 0] : SSet.{0})| ⟶ |(Λ[2, 0] : SSet.{0})| =>
      f (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom x))
    horn_two_zero_toIcc_from
  have hHorn' :
      hornIcc_from
          (horn_two_zero_toIcc
            (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom x)) =
        SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom x := by
    simpa using hHorn
  rw [hHorn']
  have hIsoCat :
      SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom ≫
        SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv = 𝟙 _ := by
    rw [← SSet.toTop.map_comp, Iso.hom_inv_id, SSet.toTop.map_id]
  have hIso := congrArg
    (fun f : |(boundaryTwoRemainingFaces : SSet.{0})| ⟶
        |(boundaryTwoRemainingFaces : SSet.{0})| => f x)
    hIsoCat
  have hIso' :
      SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv
          (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom x) = x := by
    change
      (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom ≫
          SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv) x = x
    exact hIso
  rw [hIso']

/-- The circle map followed by its path inverse is the identity on the
last-edge pushout. -/
lemma boundaryTwoSupToBoundaryCircle_comp_inverse :
    boundaryTwoSupToBoundaryCircle ≫ boundaryCircleToBoundaryTwoSup = 𝟙 _ := by
  apply toTop_boundaryTwo_isPushout.hom_ext
  · rw [boundaryTwoSupToBoundaryCircle_firstFace_assoc,
      lastEdgeToBoundaryCircle_comp_inverse, Category.comp_id]
  · rw [boundaryTwoSupToBoundaryCircle_remainingFaces_assoc,
      boundaryTwoRemainingFacesToBoundaryCircle_comp_inverse, Category.comp_id]

lemma boundaryTwoSupToBoundaryCircle_unitInterval
    (t : TopCat.I.{0}) :
    boundaryTwoSupToBoundaryCircle (unitIntervalToBoundaryTwoSup t) =
      unitIntervalToBoundaryCircle t := by
  have hFace := congrArg
    (fun f :
        |(boundaryTwoFirstFace : SSet.{0})| ⟶ boundaryCircle =>
      f (lastEdgeIsoI.inv t))
    boundaryTwoSupToBoundaryCircle_firstFace
  change
    boundaryTwoSupToBoundaryCircle
        (SSet.toTop.map
          (SSet.Subcomplex.homOfLE
            (le_sup_left :
              boundaryTwoFirstFace ≤
                boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))
          (lastEdgeIsoI.inv t)) =
      unitIntervalToBoundaryCircle t
  rw [show boundaryTwoSupToBoundaryCircle
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_left :
            boundaryTwoFirstFace ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))
        (lastEdgeIsoI.inv t)) =
      lastEdgeToBoundaryCircle (lastEdgeIsoI.inv t) by simpa using hFace]
  change unitIntervalToBoundaryCircle
      (lastEdgeIsoI.hom (lastEdgeIsoI.inv t)) =
    unitIntervalToBoundaryCircle t
  have ht := congrArg
    (fun f : TopCat.I.{0} ⟶ TopCat.I.{0} => f t)
    lastEdgeIsoI.inv_hom_id
  rw [show lastEdgeIsoI.hom (lastEdgeIsoI.inv t) = t by
    change (lastEdgeIsoI.inv ≫ lastEdgeIsoI.hom) t = t
    exact ht]

lemma boundaryTwoSupToBoundaryCircle_hornIcc
    (t : Set.Icc (-1 : ℝ) 1) :
    boundaryTwoSupToBoundaryCircle (hornIccToBoundaryTwoSup t) =
      hornIccToBoundaryCircle t := by
  have hFace := congrArg
    (fun f :
        |(boundaryTwoRemainingFaces : SSet.{0})| ⟶ boundaryCircle =>
      f (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv
        (hornIcc_from t)))
    boundaryTwoSupToBoundaryCircle_remainingFaces
  change
    boundaryTwoSupToBoundaryCircle
        (SSet.toTop.map
          (SSet.Subcomplex.homOfLE
            (le_sup_right :
              boundaryTwoRemainingFaces ≤
                boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))
          (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv
            (hornIcc_from t))) =
      hornIccToBoundaryCircle t
  rw [show boundaryTwoSupToBoundaryCircle
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE
          (le_sup_right :
            boundaryTwoRemainingFaces ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))
        (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv
          (hornIcc_from t))) =
      boundaryTwoRemainingFacesToBoundaryCircle
        (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv
          (hornIcc_from t)) by simpa using hFace]
  change
    hornIccToBoundaryCircle
      (horn_two_zero_toIcc
        (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom
          (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv
            (hornIcc_from t)))) =
      hornIccToBoundaryCircle t
  have hIsoCat :
      SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv ≫
        SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom = 𝟙 _ := by
    rw [← SSet.toTop.map_comp, Iso.inv_hom_id, SSet.toTop.map_id]
  have hIso := congrArg
    (fun f : |(Λ[2, 0] : SSet.{0})| ⟶ |(Λ[2, 0] : SSet.{0})| =>
      f (hornIcc_from t))
    hIsoCat
  have hIso' :
      SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom
          (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv
            (hornIcc_from t)) =
        hornIcc_from t := by
    change
      (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.inv ≫
        SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom)
          (hornIcc_from t) = hornIcc_from t
    exact hIso
  rw [hIso']
  have ht := congrArg (fun f : hornIcc ⟶ hornIcc => f t)
    hornIcc_from_toIcc
  rw [show horn_two_zero_toIcc (hornIcc_from t) = t by
    change (hornIcc_from ≫ horn_two_zero_toIcc) t = t
    exact ht]

/-- The path inverse followed by the circle map is the identity. -/
lemma boundaryCircleToBoundaryTwoSup_comp_boundaryTwoSupToBoundaryCircle :
    boundaryCircleToBoundaryTwoSup ≫ boundaryTwoSupToBoundaryCircle = 𝟙 _ := by
  ext y
  letI : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩
  let x := AddCircle.equivIco (3 : ℝ) 0 y
  have hxIco : (x : ℝ) ∈ Set.Ico (0 : ℝ) 3 := by
    simpa using x.2
  have hy : (((x : ℝ) : AddCircle (3 : ℝ))) = y :=
    AddCircle.coe_equivIco
  change
    boundaryTwoSupToBoundaryCircle
        (boundaryCircleToBoundaryTwoSup y) = y
  rw [← hy]
  change
    boundaryTwoSupToBoundaryCircle
        (AddCircle.liftIco (3 : ℝ) 0 boundaryCircleLiftPath
          (((x : ℝ) : AddCircle (3 : ℝ)))) =
      (((x : ℝ) : AddCircle (3 : ℝ)))
  rw [AddCircle.liftIco_zero_coe_apply hxIco, boundaryCircleLiftPath]
  by_cases hx2 : (x : ℝ) ≤ 2
  · rw [if_pos hx2, boundaryTwoSupToBoundaryCircle_hornIcc]
    have hmem : (x : ℝ) - 1 ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hxIco.1], by linarith⟩
    have hp :
        Set.projIcc (-1 : ℝ) 1 (by norm_num) ((x : ℝ) - 1) =
          ⟨(x : ℝ) - 1, hmem⟩ :=
      Set.projIcc_of_mem _ hmem
    rw [hp]
    change ((((x : ℝ) - 1) + 1 : ℝ) : AddCircle (3 : ℝ)) =
      ((x : ℝ) : AddCircle (3 : ℝ))
    congr 1
    ring
  · rw [if_neg hx2, boundaryTwoSupToBoundaryCircle_unitInterval]
    have hmem : (x : ℝ) - 2 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith, by linarith [hxIco.2]⟩
    have hp :
        Set.projIcc (0 : ℝ) 1 zero_le_one ((x : ℝ) - 2) =
          ⟨(x : ℝ) - 2, hmem⟩ :=
      Set.projIcc_of_mem _ hmem
    rw [hp]
    change
      ((2 + (TopCat.I.homeomorph.{0}
        (TopCat.I.homeomorph.{0}.symm ⟨(x : ℝ) - 2, hmem⟩) : ℝ) : ℝ) :
          AddCircle (3 : ℝ)) =
        ((x : ℝ) : AddCircle (3 : ℝ))
    rw [Homeomorph.apply_symm_apply]
    change ((2 + ((x : ℝ) - 2) : ℝ) : AddCircle (3 : ℝ)) =
      ((x : ℝ) : AddCircle (3 : ℝ))
    congr 1
    ring

/-- The last-edge pushout is isomorphic to the concrete additive circle. -/
noncomputable def boundaryTwoSupIsoBoundaryCircle :
    |((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces :
      (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0})| ≅
      boundaryCircle where
  hom := boundaryTwoSupToBoundaryCircle
  inv := boundaryCircleToBoundaryTwoSup
  hom_inv_id := boundaryTwoSupToBoundaryCircle_comp_inverse
  inv_hom_id :=
    boundaryCircleToBoundaryTwoSup_comp_boundaryTwoSupToBoundaryCircle

/-- Geometric realization of `∂Δ[2]` is homeomorphic to an additive circle. -/
noncomputable def homeomorph_boundaryTwo_addCircle :
    |boundaryTwoSSet| ≃ₜ AddCircle (3 : ℝ) :=
  TopCat.homeoOfIso
    ((SSet.toTop.mapIso boundaryTwoIsoSup).trans
      boundaryTwoSupIsoBoundaryCircle)

/-! ## A reusable attachment step -/

/-- The short-exact gluing step for the simplicial--singular comparison.

If simplicial chains and singular chains form compatible short exact
sequences, and the comparison is a quasi-isomorphism on the first two
terms, then it is a quasi-isomorphism on the glued third term.  In an
attachment induction, the remaining geometric work is therefore exactly
to construct these two short exact sequences and the compatibility
squares. -/
theorem simplicialSingularComparison_quasiIso_of_shortExact
    (R : ModuleCat.{0} k) (X₁ X₂ X₃ : SSet.{0})
    (a : X₁.chainComplex R ⟶ X₂.chainComplex R)
    (b : X₂.chainComplex R ⟶ X₃.chainComplex R)
    (a' : singularChainsOfRealization R X₁ ⟶
      singularChainsOfRealization R X₂)
    (b' : singularChainsOfRealization R X₂ ⟶
      singularChainsOfRealization R X₃)
    (hab : a ≫ b = 0) (hab' : a' ≫ b' = 0)
    (h₁ : simplicialSingularComparison R X₁ ≫ a' =
      a ≫ simplicialSingularComparison R X₂)
    (h₂ : simplicialSingularComparison R X₂ ≫ b' =
      b ≫ simplicialSingularComparison R X₃)
    (hsource : (ShortComplex.mk a b hab).ShortExact)
    (htarget : (ShortComplex.mk a' b' hab').ShortExact)
    [QuasiIso (simplicialSingularComparison R X₁)]
    [QuasiIso (simplicialSingularComparison R X₂)] :
    QuasiIso (simplicialSingularComparison R X₃) := by
  let S := ShortComplex.mk a b hab
  let T := ShortComplex.mk a' b' hab'
  let φ : S ⟶ T := ShortComplex.Hom.mk
    (simplicialSingularComparison R X₁)
    (simplicialSingularComparison R X₂)
    (simplicialSingularComparison R X₃) h₁ h₂
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    φ hsource htarget inferInstance inferInstance

/-! ## The zero-simplex base case -/

/-- The realization of the standard zero-simplex is terminal. -/
def isTerminal_toTop_stdSimplex_zero :
    CategoryTheory.Limits.IsTerminal |(SSet.stdSimplex.obj ⦋0⦌)| :=
  (TopCat.isTerminalPUnit.ofIso
      (TopCat.isoOfHomeo
        (Homeomorph.homeomorphOfUnique
          (SimplexCategory.toTop.obj ⦋0⦌) PUnit)).symm).ofIso
    (SSet.toTopSimplex.app ⦋0⦌).symm

/-- The adjunction unit is an isomorphism on the standard zero-simplex. -/
noncomputable instance isIso_sSetTopAdj_unit_stdSimplex_zero :
    IsIso (sSetTopAdj.unit.app (SSet.stdSimplex.obj ⦋0⦌)) := by
  let hsource := SSet.stdSimplex.isTerminalObj₀
  let htarget :=
    isTerminal_toTop_stdSimplex_zero.isTerminalObj
      TopCat.toSSet |(SSet.stdSimplex.obj ⦋0⦌)|
  let e := hsource.uniqueUpToIso htarget
  have h :
      sSetTopAdj.unit.app (SSet.stdSimplex.obj ⦋0⦌) = e.hom :=
    htarget.hom_ext _ _
  rw [h]
  infer_instance

/-- On the zero-simplex, the chain comparison is itself an isomorphism. -/
noncomputable instance (R : ModuleCat.{0} k) :
    IsIso (simplicialSingularComparison R (SSet.stdSimplex.obj ⦋0⦌)) := by
  letI : IsIso (sSetTopAdj.unit.app (SSet.stdSimplex.obj ⦋0⦌)) :=
    isIso_sSetTopAdj_unit_stdSimplex_zero
  change IsIso
    (((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map
      (sSetTopAdj.unit.app (SSet.stdSimplex.obj ⦋0⦌)))
  exact Functor.map_isIso _ _

/-- The simplicial--singular comparison is a quasi-isomorphism for the
standard zero-simplex. -/
instance (R : ModuleCat.{0} k) :
    QuasiIso
      (simplicialSingularComparison R (SSet.stdSimplex.obj ⦋0⦌)) :=
  quasiIso_of_isIso _

/-! ## The disconnected two-vertex base case -/

/-- The realization of the empty subcomplex is initial. -/
def isInitial_toTop_boundaryTwoBot :
    IsInitial
      |((⊥ : (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) : SSet.{0})| :=
  SSet.Subcomplex.isInitialBot.isInitialObj SSet.toTop

/-- The two realized vertices, labelled by `Bool`. -/
noncomputable def boundaryTwoVerticesToBool :
    |(boundaryTwoVertices : SSet.{0})| ⟶ TopCat.of Bool :=
  toTop_boundaryTwoVertices_isPushout.desc
    (TopCat.const false) (TopCat.const true)
    (isInitial_toTop_boundaryTwoBot.hom_ext _ _)

noncomputable def boundaryTwoVertexOnePoint :
    |(boundaryTwoVertices : SSet.{0})| :=
  SSet.toTop.map
    ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
      SSet.Subcomplex.homOfLE
        (le_sup_left :
          SSet.stdSimplex.face ({1} : Finset (Fin 3)) ≤ boundaryTwoVertices))
    (default : |(Δ[0] : SSet.{0})|)

noncomputable def boundaryTwoVertexTwoPoint :
    |(boundaryTwoVertices : SSet.{0})| :=
  SSet.toTop.map
    ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
      SSet.Subcomplex.homOfLE
        (le_sup_right :
          SSet.stdSimplex.face ({2} : Finset (Fin 3)) ≤ boundaryTwoVertices))
    (default : |(Δ[0] : SSet.{0})|)

/-- The inverse labelling map from the discrete two-point space. -/
noncomputable def boolToBoundaryTwoVertices :
    TopCat.of Bool ⟶ |(boundaryTwoVertices : SSet.{0})| :=
  TopCat.ofHom
    { toFun := fun b => if b then boundaryTwoVertexTwoPoint
        else boundaryTwoVertexOnePoint
      continuous_toFun := continuous_of_discreteTopology }

lemma boundaryTwoVerticesToBool_vertex_one :
    SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE
            (le_sup_left :
              SSet.stdSimplex.face ({1} : Finset (Fin 3)) ≤
                boundaryTwoVertices)) ≫
      boundaryTwoVerticesToBool =
    (TopCat.const false :
      |(Δ[0] : SSet.{0})| ⟶ TopCat.of Bool) := by
  unfold boundaryTwoVerticesToBool
  rw [SSet.toTop.map_comp]
  simp only [Category.assoc]
  rw [
    toTop_boundaryTwoVertices_isPushout.inl_desc]
  ext
  rfl

lemma boundaryTwoVerticesToBool_vertex_two :
    SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE
            (le_sup_right :
              SSet.stdSimplex.face ({2} : Finset (Fin 3)) ≤
                boundaryTwoVertices)) ≫
      boundaryTwoVerticesToBool =
    (TopCat.const true :
      |(Δ[0] : SSet.{0})| ⟶ TopCat.of Bool) := by
  unfold boundaryTwoVerticesToBool
  rw [SSet.toTop.map_comp]
  simp only [Category.assoc]
  rw [
    toTop_boundaryTwoVertices_isPushout.inr_desc]
  ext
  rfl

lemma boolToBoundaryTwoVertices_comp_boundaryTwoVerticesToBool :
    boolToBoundaryTwoVertices ≫ boundaryTwoVerticesToBool = 𝟙 _ := by
  ext b
  cases b
  · change boundaryTwoVerticesToBool boundaryTwoVertexOnePoint = false
    have h := congrArg
      (fun f : |(Δ[0] : SSet.{0})| ⟶ TopCat.of Bool =>
        f (default : |(Δ[0] : SSet.{0})|))
      boundaryTwoVerticesToBool_vertex_one
    simpa [boundaryTwoVertexOnePoint] using h
  · change boundaryTwoVerticesToBool boundaryTwoVertexTwoPoint = true
    have h := congrArg
      (fun f : |(Δ[0] : SSet.{0})| ⟶ TopCat.of Bool =>
        f (default : |(Δ[0] : SSet.{0})|))
      boundaryTwoVerticesToBool_vertex_two
    simpa [boundaryTwoVertexTwoPoint] using h

lemma toTop_stdSimplex_zero_eq_default
    (x : |(Δ[0] : SSet.{0})|) : x = default := by
  have h := isTerminal_toTop_stdSimplex_zero.hom_ext
    (TopCat.const x : TopCat.of PUnit ⟶ |(Δ[0] : SSet.{0})|)
    (TopCat.const default : TopCat.of PUnit ⟶ |(Δ[0] : SSet.{0})|)
  simpa using congrArg
    (fun f : TopCat.of PUnit ⟶ |(Δ[0] : SSet.{0})| => f PUnit.unit) h

lemma boundaryTwoVerticesToBool_comp_boolToBoundaryTwoVertices :
    boundaryTwoVerticesToBool ≫ boolToBoundaryTwoVertices = 𝟙 _ := by
  apply toTop_boundaryTwoVertices_isPushout.hom_ext
  · rw [← cancel_epi
      (SSet.toTop.map
        (SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom)]
    simp only [← Category.assoc]
    rw [← SSet.toTop.map_comp]
    rw [boundaryTwoVerticesToBool_vertex_one]
    ext x
    change boundaryTwoVertexOnePoint =
      SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE le_sup_left) x
    rw [toTop_stdSimplex_zero_eq_default x]
    rfl
  · rw [← cancel_epi
      (SSet.toTop.map
        (SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom)]
    simp only [← Category.assoc]
    rw [← SSet.toTop.map_comp]
    rw [boundaryTwoVerticesToBool_vertex_two]
    ext x
    change boundaryTwoVertexTwoPoint =
      SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE le_sup_right) x
    rw [toTop_stdSimplex_zero_eq_default x]
    rfl

/-- The two-vertex realization is a discrete two-point space. -/
noncomputable def homeomorph_boundaryTwoVertices_bool :
    |(boundaryTwoVertices : SSet.{0})| ≃ₜ Bool :=
  TopCat.homeoOfIso
    { hom := boundaryTwoVerticesToBool
      inv := boolToBoundaryTwoVertices
      hom_inv_id := boundaryTwoVerticesToBool_comp_boolToBoundaryTwoVertices
      inv_hom_id := boolToBoundaryTwoVertices_comp_boundaryTwoVerticesToBool }

/-- The constant simplicial set on the two-element type. -/
abbrev boolSSet : SSet.{0} :=
  (Functor.const SimplexCategoryᵒᵖ).obj Bool

/-- Label the two vertex components simplicially. -/
noncomputable def boundaryTwoVerticesToBoolSSet :
    (boundaryTwoVertices : SSet.{0}) ⟶ boolSSet :=
  boundaryTwoVertices_isPushout.desc
    (SSet.const false) (SSet.const true)
    (SSet.Subcomplex.isInitialBot.hom_ext _ _)

lemma boundaryTwoVerticesToBoolSSet_face_one :
    SSet.Subcomplex.homOfLE
        (le_sup_left :
          SSet.stdSimplex.face ({1} : Finset (Fin 3)) ≤ boundaryTwoVertices) ≫
      boundaryTwoVerticesToBoolSSet =
    SSet.const false := by
  exact boundaryTwoVertices_isPushout.inl_desc _ _ _

lemma boundaryTwoVerticesToBoolSSet_face_two :
    SSet.Subcomplex.homOfLE
        (le_sup_right :
          SSet.stdSimplex.face ({2} : Finset (Fin 3)) ≤ boundaryTwoVertices) ≫
      boundaryTwoVerticesToBoolSSet =
    SSet.const true := by
  exact boundaryTwoVertices_isPushout.inr_desc _ _ _

noncomputable def boundaryTwoVertexOneSimplex :
    (boundaryTwoVertices : SSet.{0}) _⦋0⦌ :=
  (((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
      SSet.Subcomplex.homOfLE le_sup_left).app _)
    (SSet.stdSimplex.obj₀Equiv.symm 0)

noncomputable def boundaryTwoVertexTwoSimplex :
    (boundaryTwoVertices : SSet.{0}) _⦋0⦌ :=
  (((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
      SSet.Subcomplex.homOfLE le_sup_right).app _)
    (SSet.stdSimplex.obj₀Equiv.symm 0)

/-- Reinsert a Boolean-labelled constant simplex as the corresponding
vertex of `boundaryTwoVertices`. -/
noncomputable def boolSSetToBoundaryTwoVertices :
    boolSSet ⟶ (boundaryTwoVertices : SSet.{0}) where
  app n := TypeCat.ofHom (fun b => by
    change Bool at b
    exact if b then
        (SSet.const (X := boolSSet) boundaryTwoVertexTwoSimplex).app n b
      else
        (SSet.const (X := boolSSet) boundaryTwoVertexOneSimplex).app n b)
  naturality X Y f := by
    ext b
    change Bool at b
    cases b
    · have h := congrArg
        (fun g => g false)
        ((SSet.const (X := boolSSet)
          boundaryTwoVertexOneSimplex).naturality f)
      simpa using h
    · have h := congrArg
        (fun g => g true)
        ((SSet.const (X := boolSSet)
          boundaryTwoVertexTwoSimplex).naturality f)
      simpa using h

lemma boolSSetToBoundaryTwoVertices_comp_boundaryTwoVerticesToBoolSSet :
    boolSSetToBoundaryTwoVertices ≫ boundaryTwoVerticesToBoolSSet = 𝟙 _ := by
  have h₁ :
      SSet.const boundaryTwoVertexOneSimplex ≫
          boundaryTwoVerticesToBoolSSet =
        (SSet.const false : boolSSet ⟶ boolSSet) := by
    rw [SSet.const_comp]
    congr 1
    have h := congrArg
      (fun f : (SSet.stdSimplex.face
          ({1} : Finset (Fin 3)) : SSet.{0}) ⟶ boolSSet =>
        f.app _ (((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom.app _)
          (SSet.stdSimplex.obj₀Equiv.symm 0)))
      boundaryTwoVerticesToBoolSSet_face_one
    simpa [boundaryTwoVertexOneSimplex] using h
  have h₂ :
      SSet.const boundaryTwoVertexTwoSimplex ≫
          boundaryTwoVerticesToBoolSSet =
        (SSet.const true : boolSSet ⟶ boolSSet) := by
    rw [SSet.const_comp]
    congr 1
    have h := congrArg
      (fun f : (SSet.stdSimplex.face
          ({2} : Finset (Fin 3)) : SSet.{0}) ⟶ boolSSet =>
        f.app _ (((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom.app _)
          (SSet.stdSimplex.obj₀Equiv.symm 0)))
      boundaryTwoVerticesToBoolSSet_face_two
    simpa [boundaryTwoVertexTwoSimplex] using h
  ext n b
  cases b
  · change
      ((SSet.const (X := boolSSet) boundaryTwoVertexOneSimplex ≫
          boundaryTwoVerticesToBoolSSet).app n) false =
        (((𝟙 boolSSet) : boolSSet ⟶ boolSSet).app n) false
    rw [h₁]
    rfl
  · change
      ((SSet.const (X := boolSSet) boundaryTwoVertexTwoSimplex ≫
          boundaryTwoVerticesToBoolSSet).app n) true =
        (((𝟙 boolSSet) : boolSSet ⟶ boolSSet).app n) true
    rw [h₂]
    rfl

lemma boundaryTwoVerticesToBoolSSet_comp_boolSSetToBoundaryTwoVertices :
    boundaryTwoVerticesToBoolSSet ≫ boolSSetToBoundaryTwoVertices = 𝟙 _ := by
  apply boundaryTwoVertices_isPushout.hom_ext
  · rw [← Category.assoc, boundaryTwoVerticesToBoolSSet_face_one]
    rw [Category.comp_id]
    have hconst :
        (SSet.const false :
            (SSet.stdSimplex.face
              ({1} : Finset (Fin 3)) : SSet.{0}) ⟶ boolSSet) ≫
          boolSSetToBoundaryTwoVertices =
        SSet.const boundaryTwoVertexOneSimplex := by
      rw [SSet.const_comp]
      congr 1
    rw [hconst]
    rw [← cancel_mono boundaryTwoVertices.ι,
      SSet.Subcomplex.homOfLE_ι, SSet.const_comp]
    rw [← cancel_epi
      (SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom]
    rw [SSet.comp_const, faceSingletonIso_hom_comp_ι]
    congr 1
  · rw [← Category.assoc, boundaryTwoVerticesToBoolSSet_face_two]
    rw [Category.comp_id]
    have hconst :
        (SSet.const true :
            (SSet.stdSimplex.face
              ({2} : Finset (Fin 3)) : SSet.{0}) ⟶ boolSSet) ≫
          boolSSetToBoundaryTwoVertices =
        SSet.const boundaryTwoVertexTwoSimplex := by
      rw [SSet.const_comp]
      congr 1
    rw [hconst]
    rw [← cancel_mono boundaryTwoVertices.ι,
      SSet.Subcomplex.homOfLE_ι, SSet.const_comp]
    rw [← cancel_epi
      (SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom]
    rw [SSet.comp_const, faceSingletonIso_hom_comp_ι]
    congr 1

/-- The two-vertex simplicial set is the constant simplicial set on `Bool`. -/
noncomputable def boundaryTwoVerticesIsoBoolSSet :
    (boundaryTwoVertices : SSet.{0}) ≅ boolSSet where
  hom := boundaryTwoVerticesToBoolSSet
  inv := boolSSetToBoundaryTwoVertices
  hom_inv_id := boundaryTwoVerticesToBoolSSet_comp_boolSSetToBoundaryTwoVertices
  inv_hom_id := boolSSetToBoundaryTwoVertices_comp_boundaryTwoVerticesToBoolSSet

noncomputable instance boundaryTwoVertices_totallyDisconnectedSpace :
    TotallyDisconnectedSpace |(boundaryTwoVertices : SSet.{0})| :=
  homeomorph_boundaryTwoVertices_bool.symm.totallyDisconnectedSpace

/-- Identify the singular simplicial set of the realized two vertices with
the same constant Boolean simplicial set. -/
noncomputable def singularBoundaryTwoVerticesIsoBoolSSet :
    TopCat.toSSet.obj |(boundaryTwoVertices : SSet.{0})| ≅ boolSSet :=
  (TopCat.toSSet.mapIso
      (TopCat.isoOfHomeo homeomorph_boundaryTwoVertices_bool)).trans
    (TopCat.toSSetIsoConst (TopCat.of Bool))

lemma singularBoundaryTwoVerticesIsoBoolSSet_app_zero
    (q : (TopCat.toSSet.obj |(boundaryTwoVertices : SSet.{0})|) _⦋0⦌) :
    singularBoundaryTwoVerticesIsoBoolSSet.hom.app _ q =
      homeomorph_boundaryTwoVertices_bool
        (TopCat.toSSetObj₀Equiv q) := by
  dsimp [singularBoundaryTwoVerticesIsoBoolSSet,
    TopCat.toSSetIsoConst]
  change homeomorph_boundaryTwoVertices_bool
      ((TopCat.toSSetObjEquiv _ _ q) (Classical.arbitrary _)) =
    homeomorph_boundaryTwoVertices_bool
      ((TopCat.toSSetObjEquiv _ _ q) default)
  rw [Subsingleton.elim (Classical.arbitrary _) default]

lemma toSSetObj₀Equiv_unit_app
    (X : SSet.{0}) (x : X _⦋0⦌) :
    TopCat.toSSetObj₀Equiv
        ((sSetTopAdj.unit.app X).app _ x) =
      SSet.toTop.map (SSet.yonedaEquiv.symm x)
        (default : |(Δ[0] : SSet.{0})|) := by
  let f : (Δ[0] : SSet.{0}) ⟶ X := SSet.yonedaEquiv.symm x
  have h :
      f ≫ sSetTopAdj.unit.app X =
        SSet.const (TopCat.toSSetObj₀Equiv.symm
          (SSet.toTop.map f (default : |(Δ[0] : SSet.{0})|))) := by
    calc
      f ≫ sSetTopAdj.unit.app X =
          f ≫ (sSetTopAdj.homEquiv X |X|) (𝟙 |X|) := by
            rw [Adjunction.homEquiv_unit]
            simp
      _ = (sSetTopAdj.homEquiv Δ[0] |X|)
          (SSet.toTop.map f ≫ 𝟙 |X|) :=
        (sSetTopAdj.homEquiv_naturality_left f (𝟙 |X|)).symm
      _ = (sSetTopAdj.homEquiv Δ[0] |X|)
          (SSet.toTop.map f) := by simp
      _ = _ := sSetTopAdj_homEquiv_stdSimplex_zero _
  have hx := congrArg
    (fun g : (Δ[0] : SSet.{0}) ⟶ TopCat.toSSet.obj |X| =>
      g.app _ (SSet.stdSimplex.obj₀Equiv.symm 0)) h
  have hx' := congrArg TopCat.toSSetObj₀Equiv hx
  simpa [f] using hx'

lemma boundaryTwoVertices_unit_comp_bool :
    sSetTopAdj.unit.app (boundaryTwoVertices : SSet.{0}) ≫
      singularBoundaryTwoVerticesIsoBoolSSet.hom =
    boundaryTwoVerticesIsoBoolSSet.hom := by
  apply boundaryTwoVertices_isPushout.hom_ext
  · change
      SSet.Subcomplex.homOfLE le_sup_left ≫
          sSetTopAdj.unit.app (boundaryTwoVertices : SSet.{0}) ≫
          singularBoundaryTwoVerticesIsoBoolSSet.hom =
        SSet.Subcomplex.homOfLE le_sup_left ≫
          boundaryTwoVerticesToBoolSSet
    rw [boundaryTwoVerticesToBoolSSet_face_one]
    rw [← cancel_epi
      (SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom]
    apply (SSet.yonedaEquiv (X := boolSSet) (n := ⦋0⦌)).injective
    change
      (singularBoundaryTwoVerticesIsoBoolSSet.hom.app _)
        ((sSetTopAdj.unit.app (boundaryTwoVertices : SSet.{0})).app _
          boundaryTwoVertexOneSimplex) = false
    rw [singularBoundaryTwoVerticesIsoBoolSSet_app_zero]
    rw [toSSetObj₀Equiv_unit_app]
    have hg :
        SSet.yonedaEquiv.symm boundaryTwoVertexOneSimplex =
          (SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
            SSet.Subcomplex.homOfLE le_sup_left := by
      change
        (SSet.yonedaEquiv
          (X := (boundaryTwoVertices : SSet.{0})) (n := ⦋0⦌)).symm
            ((SSet.yonedaEquiv
              (X := (boundaryTwoVertices : SSet.{0})) (n := ⦋0⦌))
              ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
                SSet.Subcomplex.homOfLE le_sup_left)) =
          _
      exact Equiv.symm_apply_apply _ _
    rw [hg]
    change boundaryTwoVerticesToBool boundaryTwoVertexOnePoint = false
    have h := congrArg
      (fun f : |(Δ[0] : SSet.{0})| ⟶ TopCat.of Bool =>
        f (default : |(Δ[0] : SSet.{0})|))
      boundaryTwoVerticesToBool_vertex_one
    simpa [boundaryTwoVertexOnePoint] using h
  · change
      SSet.Subcomplex.homOfLE le_sup_right ≫
          sSetTopAdj.unit.app (boundaryTwoVertices : SSet.{0}) ≫
          singularBoundaryTwoVerticesIsoBoolSSet.hom =
        SSet.Subcomplex.homOfLE le_sup_right ≫
          boundaryTwoVerticesToBoolSSet
    rw [boundaryTwoVerticesToBoolSSet_face_two]
    rw [← cancel_epi
      (SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom]
    apply (SSet.yonedaEquiv (X := boolSSet) (n := ⦋0⦌)).injective
    change
      (singularBoundaryTwoVerticesIsoBoolSSet.hom.app _)
        ((sSetTopAdj.unit.app (boundaryTwoVertices : SSet.{0})).app _
          boundaryTwoVertexTwoSimplex) = true
    rw [singularBoundaryTwoVerticesIsoBoolSSet_app_zero]
    rw [toSSetObj₀Equiv_unit_app]
    have hg :
        SSet.yonedaEquiv.symm boundaryTwoVertexTwoSimplex =
          (SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
            SSet.Subcomplex.homOfLE le_sup_right := by
      change
        (SSet.yonedaEquiv
          (X := (boundaryTwoVertices : SSet.{0})) (n := ⦋0⦌)).symm
            ((SSet.yonedaEquiv
              (X := (boundaryTwoVertices : SSet.{0})) (n := ⦋0⦌))
              ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
                SSet.Subcomplex.homOfLE le_sup_right)) =
          _
      exact Equiv.symm_apply_apply _ _
    rw [hg]
    change boundaryTwoVerticesToBool boundaryTwoVertexTwoPoint = true
    have h := congrArg
      (fun f : |(Δ[0] : SSet.{0})| ⟶ TopCat.of Bool =>
        f (default : |(Δ[0] : SSet.{0})|))
      boundaryTwoVerticesToBool_vertex_two
    simpa [boundaryTwoVertexTwoPoint] using h

/-- The adjunction unit is an isomorphism for the disconnected pair of
vertices. -/
noncomputable instance isIso_sSetTopAdj_unit_boundaryTwoVertices :
    IsIso (sSetTopAdj.unit.app (boundaryTwoVertices : SSet.{0})) := by
  letI : IsIso
      (sSetTopAdj.unit.app (boundaryTwoVertices : SSet.{0}) ≫
        singularBoundaryTwoVerticesIsoBoolSSet.hom) := by
    rw [boundaryTwoVertices_unit_comp_bool]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (sSetTopAdj.unit.app (boundaryTwoVertices : SSet.{0}))
    singularBoundaryTwoVerticesIsoBoolSSet.hom

/-- The canonical simplicial--singular comparison is a quasi-isomorphism
on the two endpoints of the last edge. -/
noncomputable instance simplicialSingularComparison_boundaryTwoVertices_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso
      (simplicialSingularComparison R (boundaryTwoVertices : SSet.{0})) := by
  letI : IsIso
      (simplicialSingularComparison R
        (boundaryTwoVertices : SSet.{0})) := by
    change IsIso
      (((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map
        (sSetTopAdj.unit.app (boundaryTwoVertices : SSet.{0})))
    exact Functor.map_isIso _ _
  exact quasiIso_of_isIso _

/-- The same base case, transported to the actual edge--horn
intersection. -/
noncomputable instance
    simplicialSingularComparison_boundaryTwoIntersection_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso
      (simplicialSingularComparison R
        ((boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces : _) :
          SSet.{0})) := by
  rw [boundaryTwoFirstFace_inf]
  infer_instance

