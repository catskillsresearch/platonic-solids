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

