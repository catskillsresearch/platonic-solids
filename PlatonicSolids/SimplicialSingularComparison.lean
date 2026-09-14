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
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Analysis.Convex.Contractible
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

/-- A map into a zero object is an epimorphism. -/
lemma epi_of_isZero_target {C : Type*} [Category* C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) (hY : IsZero Y) : Epi f :=
  ⟨fun _ _ _ => hY.eq_of_src _ _⟩

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

