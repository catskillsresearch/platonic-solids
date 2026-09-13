/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Separation.Lemmas

/-!
Singular homology lemmas that Mathlib does not package: homotopy
equivalences and homeomorphisms induce homology isomorphisms,
contractible spaces have the homology of a point, `H₀(Sⁿ) ≅ R` for
`n ≥ 1`, and the full calculation of `H_*(S⁰)`.

The pair and Mayer–Vietoris sequences of singular chains are in
`PlatonicSolids/RelativeHomology.lean` and
`PlatonicSolids/MayerVietoris.lean`. Barycentric subdivision and the
open-cover quasi-isomorphism are in `PlatonicSolids/SingularExcision/`.
The calculation `H_n(S^n) ≅ R` for `n > 0` is in
`PlatonicSolids/SphereSingularHomology.lean`. The
paper’s `χ(S³) = 0` is obtained from the cellular calculation in
`PlatonicSolids/Sphere3Homology.lean`.
-/

open AlgebraicTopology CategoryTheory Limits HomologicalComplex
open scoped ContinuousMap Topology

universe v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Preadditive C]
  [CategoryWithHomology C]

/-- Homotopic continuous maps induce equal singular-homology maps. -/
lemma singularHomologyMap_eq_of_homotopic
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (h : f.hom.Homotopic g.hom)
    (R : C) (n : ℕ) :
    homologyMap (((singularChainComplexFunctor C).obj R).map f) n =
      homologyMap (((singularChainComplexFunctor C).obj R).map g) n :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor h.some R n

/-- A homotopy equivalence of spaces induces a homotopy equivalence of
singular chain complexes. -/
noncomputable def singularChainHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (R : C) :
    HomotopyEquiv
      (((singularChainComplexFunctor C).obj R).obj (.of X))
      (((singularChainComplexFunctor C).obj R).obj (.of Y)) where
  hom := ((singularChainComplexFunctor C).obj R).map (TopCat.ofHom e.toFun)
  inv := ((singularChainComplexFunctor C).obj R).map (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    have H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 _) := by
      simpa [TopCat.ofHom_comp, TopCat.ofHom_id] using e.left_inv.some
    simpa [Functor.map_comp, Functor.map_id] using
      H.singularChainComplexFunctorObjMap R
  homotopyInvHomId := by
    have H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 _) := by
      simpa [TopCat.ofHom_comp, TopCat.ofHom_id] using e.right_inv.some
    simpa [Functor.map_comp, Functor.map_id] using
      H.singularChainComplexFunctorObjMap R

/-- Homotopy equivalent spaces have isomorphic singular homology. -/
noncomputable def singularHomologyIso_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (.of X) ≅
      ((singularHomologyFunctor C n).obj R).obj (.of Y) :=
  (singularChainHomotopyEquiv e R).toHomologyIso n

/-- Homeomorphic spaces have isomorphic singular homology. -/
noncomputable def singularHomologyIso_of_homeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (.of X) ≅
      ((singularHomologyFunctor C n).obj R).obj (.of Y) :=
  singularHomologyIso_of_homotopyEquiv e.toHomotopyEquiv R n

/-- A point has vanishing singular homology in positive degree. -/
lemma isZero_singularHomology_unit (R : C) {n : ℕ} (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj (.of Unit)) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R (.of Unit) hn

/-- A contractible space has vanishing singular homology in positive degree. -/
lemma isZero_singularHomology_of_contractible
    {X : Type} [TopologicalSpace X] [ContractibleSpace X]
    (R : C) {n : ℕ} (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj (.of X)) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  exact (isZero_singularHomology_unit R hn).of_iso
    (singularHomologyIso_of_homotopyEquiv e R n)

/-- Path-connectedness transfers along a homotopy equivalence. -/
lemma pathConnectedSpace_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) :
    PathConnectedSpace X :=
  ⟨⟨e.invFun (Classical.arbitrary Y)⟩, fun x₁ x₂ =>
    ⟨(e.left_inv.some.evalAt x₁).symm.trans
      (((PathConnectedSpace.somePath (e.toFun x₁) (e.toFun x₂)).map
          e.invFun.continuous).trans
        (e.left_inv.some.evalAt x₂))⟩⟩

/-- The augmentation `H₀(X) → R` is natural. -/
lemma singularHomology₀ε_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (R : C) :
    homologyMap (((singularChainComplexFunctor C).obj R).map f) 0 ≫
      Y.singularHomology₀ε R =
    X.singularHomology₀ε R := by
  let SX := TopCat.toSSet.obj X
  let SY := TopCat.toSSet.obj Y
  let sf := TopCat.toSSet.map f
  let φ := SSet.chainComplexMap sf R
  let KX := SX.chainComplex R
  let KY := SY.chainComplex R
  apply (cancel_epi (KX.homologyπ 0)).1
  apply (cancel_epi (ChainComplex.cycles₀Iso KX).inv).1
  apply SSet.chainComplex_hom_ext
  intro x
  have hx :
      KX.liftCycles (SX.ιChainComplex x) 0 (by simp) (by simp) =
        SX.ιChainComplex x ≫ (ChainComplex.cycles₀Iso KX).inv := by
    rw [← cancel_mono (KX.iCycles 0)]
    simp [ChainComplex.cycles₀Iso]
    exact (Category.comp_id _).symm
  have hnat := HomologicalComplex.homologyπ_naturality (φ := φ) (i := 0)
  have hcycle := HomologicalComplex.liftCycles_comp_cyclesMap
    (k := SX.ιChainComplex x) (j := 0) (hj := by simp) (hk := by simp) φ
  have hf : SX.ιChainComplex x ≫ φ.f 0 = SY.ιChainComplex (sf.app _ x) :=
    SSet.ι_chainComplexMap_f (X := SX) (Y := SY) (f := sf) (R := R) x
  have hY := SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε SY R (sf.app _ x)
  have hX := SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε SX R x
  have lhs :
      SX.ιChainComplex x ≫ (ChainComplex.cycles₀Iso KX).inv ≫
        KX.homologyπ 0 ≫ homologyMap φ 0 ≫ Y.singularHomology₀ε R = 𝟙 R := by
    rw [← Category.assoc, ← hx, reassoc_of% hnat, reassoc_of% hcycle]
    exact (congrArg (fun t =>
      KY.liftCycles t 0 (by simp) (by simp) ≫
        KY.homologyπ 0 ≫ Y.singularHomology₀ε R) hf).trans hY
  have rhs :
      SX.ιChainComplex x ≫ (ChainComplex.cycles₀Iso KX).inv ≫
        KX.homologyπ 0 ≫ X.singularHomology₀ε R = 𝟙 R := by
    rw [← Category.assoc, ← hx]
    exact hX
  exact lhs.trans rhs.symm

/-- Path-connected spaces have `H₀ ≅ R` via the augmentation. -/
noncomputable def singularHomology₀Iso_pathConnected
    (X : TopCat.{0}) [PathConnectedSpace X] (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ R :=
  asIso (X.singularHomology₀ε R)

/-- A map of path-connected spaces induces an isomorphism on `H₀`. -/
instance singularHomology₀_map_isIso
    {X Y : TopCat.{0}} [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y) (R : C) :
    IsIso (homologyMap (((singularChainComplexFunctor C).obj R).map f) 0) := by
  have h := singularHomology₀ε_natural f R
  let eX := singularHomology₀Iso_pathConnected X R
  let eY := singularHomology₀Iso_pathConnected Y R
  refine ⟨eY.hom ≫ eX.inv, ?_, ?_⟩
  · erw [← Category.assoc, h, eX.hom_inv_id]; rfl
  · have hf : homologyMap (((singularChainComplexFunctor C).obj R).map f) 0 =
        eX.hom ≫ eY.inv := by
      refine (cancel_mono eY.hom).mp ?_
      erw [h, Category.assoc, eY.inv_hom_id, Category.comp_id]
      rfl
    calc
      (eY.hom ≫ eX.inv) ≫
          homologyMap (((singularChainComplexFunctor C).obj R).map f) 0 =
          (eY.hom ≫ eX.inv) ≫ eX.hom ≫ eY.inv := by
        rw [hf]; rfl
      _ = eY.hom ≫ (eX.inv ≫ eX.hom) ≫ eY.inv := by
        simp [Category.assoc]
      _ = eY.hom ≫ (𝟙 R) ≫ eY.inv := by
        rw [eX.inv_hom_id]
      _ = eY.hom ≫ eY.inv := by
        simp
      _ = 𝟙 _ := eY.hom_inv_id

/-- The unit sphere in Euclidean dimension `n+1 ≥ 2` is path-connected. -/
instance pathConnectedSpace_sphere_euclidean
    {n : ℕ} [NeZero n] :
    PathConnectedSpace (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  refine isPathConnected_sphere ?_ 0 (by norm_num)
  have : (1 : ℕ) < n + 1 := Nat.lt_add_of_pos_left (NeZero.pos n)
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by
    simp
  rw [← Module.finrank_eq_rank, hfin]
  exact_mod_cast this

/-- `H₀(Sⁿ; R) ≅ R` for `n ≥ 1`. -/
noncomputable def singularHomology₀_sphere
    {n : ℕ} [NeZero n] (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj
        (.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ≅ R :=
  singularHomology₀Iso_pathConnected _ R

/-- `S⁰ ⊂ ℝ` is the two-point set `{±1}`. -/
lemma sphere_real_eq : (Metric.sphere (0 : ℝ) 1 : Set ℝ) = {1, -1} := by
  ext x
  simp [mem_sphere_iff_norm, Real.norm_eq_abs, abs_eq]

instance : TotallyDisconnectedSpace ↥(Metric.sphere (0 : ℝ) 1) := by
  refine totallyDisconnectedSpace_subtype_iff.2
    (Set.Countable.isTotallyDisconnected ?_)
  rw [sphere_real_eq]
  exact ((Set.finite_singleton (-1 : ℝ)).insert 1).countable

/-- `Hₙ(S⁰; R) = 0` for `n > 0`. -/
lemma isZero_singularHomology_sphere0 (R : C) {n : ℕ} (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj
      (.of ↥(Metric.sphere (0 : ℝ) 1))) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R _ hn

/-- `H₀(S⁰; R) ≅ R ⊕ R`. -/
noncomputable def singularHomology₀_sphere0 (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj (.of ↥(Metric.sphere (0 : ℝ) 1)) ≅
      ∐ fun _ : ↥(Metric.sphere (0 : ℝ) 1) ↦ R :=
  singularHomologyFunctorZeroOfTotallyDisconnectedSpace C R
    (.of ↥(Metric.sphere (0 : ℝ) 1))

/-- The closed unit disk is contractible, hence has vanishing positive
singular homology. -/
lemma isZero_singularHomology_closedBall
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : C) {n : ℕ} (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj
      (.of ↥(Metric.closedBall (0 : E) 1))) := by
  have : ContractibleSpace ↥(Metric.closedBall (0 : E) 1) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  exact isZero_singularHomology_of_contractible R hn
