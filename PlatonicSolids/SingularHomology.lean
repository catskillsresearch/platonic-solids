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
`PlatonicSolids/MayerVietoris.lean`. Barycentric subdivision of
singular chains is in `PlatonicSolids/SingularExcision/`; the
open-cover quasi-isomorphism for the stereographic charts is not
finished, so this file does not identify `Hₙ(Sⁿ)` for `n > 0`. The
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

/-- Path-connected spaces have `H₀ ≅ R` via the augmentation. -/
noncomputable def singularHomology₀Iso_pathConnected
    (X : TopCat.{0}) [PathConnectedSpace X] (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ R :=
  asIso (X.singularHomology₀ε R)

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
