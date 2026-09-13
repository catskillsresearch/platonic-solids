/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.DirectSum.Basic
import PlatonicSolids.SingularExcision.Algebra
import PlatonicSolids.SingularExcision.BarycentricGeometry
import PlatonicSolids.SingularExcision.CoverChains
import PlatonicSolids.SingularExcision.ModuleSupport
import PlatonicSolids.SingularExcision.SingularChains

/-!
Small singular chains for a two-set open cover.

Coefficients stay in `ModuleCat` so that finite coproduct support is
available; the geometric smallness lemmas are coefficient-independent.
-/

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Set
open scoped DirectSum Simplicial Topology

namespace SingularExcision

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- If a singular simplex has image in `A`, it is a simplex of `landsIn A`. -/
lemma mem_landsIn_of_image_subset {n : SimplexCategoryᵒᵖ}
    (s : (TopCat.toSSet.obj (.of Y)).obj n) {A : Set Y}
    (h : Set.range ((TopCat.of Y).toSSetObjEquiv n s) ⊆ A) :
    ∃ τ, (subtypeSingularSetMap A).app n τ = s := by
  let fY := (TopCat.of Y).toSSetObjEquiv n s
  let f : C(TopCat.of (stdSimplex ℝ (Fin (n.unop.len + 1))),
      TopCat.of ↥A) :=
    ⟨fun x => ⟨fY x, h ⟨x, rfl⟩⟩, fY.continuous.subtype_mk _⟩
  refine ⟨((TopCat.of ↥A).toSSetObjEquiv n).symm f, ?_⟩
  apply ((TopCat.of Y).toSSetObjEquiv n).injective
  ext x
  rw [subtypeSingularSetMap_toSSetObjEquiv, Equiv.apply_symm_apply]
  rfl

/-- A simplex of `landsIn A` has image contained in `A`. -/
lemma image_subset_of_mem_landsIn {n : SimplexCategoryᵒᵖ}
    {s : (TopCat.toSSet.obj (.of Y)).obj n} {A : Set Y}
    (h : s ∈ (landsIn A).obj n) :
    Set.range ((TopCat.of Y).toSSetObjEquiv n s) ⊆ A := by
  obtain ⟨τ, rfl⟩ := h
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  rw [subtypeSingularSetMap_toSSetObjEquiv]
  exact ((TopCat.of ↥A).toSSetObjEquiv n τ x).property

/-- Image in `A` or `B` means the simplex is small for the pair. -/
lemma mem_small_of_image_subset_left_or_right {n : SimplexCategoryᵒᵖ}
    (s : (TopCat.toSSet.obj (.of Y)).obj n) {A B : Set Y}
    (h : Set.range ((TopCat.of Y).toSSetObjEquiv n s) ⊆ A ∨
      Set.range ((TopCat.of Y).toSSetObjEquiv n s) ⊆ B) :
    s ∈ (small A B).obj n := by
  change s ∈ (landsIn A).obj n ∪ (landsIn B).obj n
  rcases h with hA | hB
  · obtain ⟨τ, hτ⟩ := mem_landsIn_of_image_subset s hA
    exact Or.inl ⟨τ, hτ⟩
  · obtain ⟨τ, hτ⟩ := mem_landsIn_of_image_subset s hB
    exact Or.inr ⟨τ, hτ⟩

/-- A small simplex has image in `A` or in `B`. -/
lemma image_subset_left_or_right_of_mem_small {n : SimplexCategoryᵒᵖ}
    {s : (TopCat.toSSet.obj (.of Y)).obj n} {A B : Set Y}
    (h : s ∈ (small A B).obj n) :
    Set.range ((TopCat.of Y).toSSetObjEquiv n s) ⊆ A ∨
      Set.range ((TopCat.of Y).toSSetObjEquiv n s) ⊆ B := by
  rcases (show s ∈ (landsIn A).obj n ∪ (landsIn B).obj n by
      simpa [small, Subfunctor.max_obj] using h) with hA | hB
  · exact Or.inl (image_subset_of_mem_landsIn hA)
  · exact Or.inr (image_subset_of_mem_landsIn hB)

/-- After enough barycentric subdivisions, every affine piece of a
singular simplex is small for a two-set open cover. -/
lemma eventual_small_pieces_of_openCover
    {n : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), Y))
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : A ∪ B = univ) :
    ∃ N : ℕ, ∀ τ ∈ ((PlatonicSolids.SingularExcision.subdivideStd
        (q := n) n)^[N]
        (PlatonicSolids.SingularExcision.simplex
          (PlatonicSolids.SingularExcision.idSimplex n))).support,
      σ '' Set.range τ.realize ⊆ A ∨
        σ '' Set.range τ.realize ⊆ B :=
  PlatonicSolids.SingularExcision.exists_subdivideStd_iterate_image_subset_left_or_right
    σ hA hB hAB

/-- Reparametrized pieces of a sufficiently subdivided singular simplex
are small simplices. -/
lemma eventual_small_reparametrize_of_openCover
    {n : ℕ} (s : (TopCat.toSSet.obj (.of Y)) _⦋n⦌)
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : A ∪ B = univ) :
    ∃ N : ℕ, ∀ τ ∈ ((PlatonicSolids.SingularExcision.subdivideStd
        (q := n) n)^[N]
        (PlatonicSolids.SingularExcision.simplex
          (PlatonicSolids.SingularExcision.idSimplex n))).support,
      PlatonicSolids.SingularExcision.reparametrizeSingularSimplex s τ ∈
        (small A B).obj (.op (.mk n)) := by
  obtain ⟨N, hN⟩ :=
    eventual_small_pieces_of_openCover
      ((TopCat.of Y).toSSetObjEquiv _ s) hA hB hAB
  refine ⟨N, fun τ hτ => ?_⟩
  refine mem_small_of_image_subset_left_or_right _ ?_
  have himg :
      Set.range ((TopCat.of Y).toSSetObjEquiv _
          (PlatonicSolids.SingularExcision.reparametrizeSingularSimplex s τ)) =
        ((TopCat.of Y).toSSetObjEquiv _ s) '' Set.range τ.realize := by
    rw [PlatonicSolids.SingularExcision.reparametrizeSingularSimplex_toContinuousMap]
    simp [ContinuousMap.coe_comp, Set.range_comp]
  simpa [himg] using hN τ hτ

/-- Reparametrizing a small simplex keeps it small: the image of a piece
is contained in the image of the parent. -/
lemma reparametrize_mem_small_of_mem_small {p q : ℕ}
    {A B : Set Y}
    (s : (TopCat.toSSet.obj (.of Y)) _⦋q⦌)
    (σ : PlatonicSolids.SingularExcision.AffineSimplex
      (stdSimplex ℝ (Fin (q + 1))) p)
    (hs : s ∈ (small A B).obj (.op (.mk q))) :
    PlatonicSolids.SingularExcision.reparametrizeSingularSimplex s σ ∈
      (small A B).obj (.op (.mk p)) := by
  refine mem_small_of_image_subset_left_or_right _ ?_
  have himg :
      Set.range ((TopCat.of Y).toSSetObjEquiv _
          (PlatonicSolids.SingularExcision.reparametrizeSingularSimplex s σ)) =
        ((TopCat.of Y).toSSetObjEquiv _ s) '' Set.range σ.realize := by
    rw [PlatonicSolids.SingularExcision.reparametrizeSingularSimplex_toContinuousMap]
    simp [ContinuousMap.coe_comp, Set.range_comp]
  rw [himg]
  rcases image_subset_left_or_right_of_mem_small hs with hA | hB
  · exact Or.inl ((Set.image_subset_range _ _).trans hA)
  · exact Or.inr ((Set.image_subset_range _ _).trans hB)

end

/-! ## Module coefficients: total chains and the small retract -/

noncomputable section

open Classical

variable {k : Type} [Ring k] (R : ModuleCat.{0} k)
variable [HasCoproducts.{0} (ModuleCat.{0} k)]

/-- Underlying abelian group of singular `n`-chains. -/
abbrev singularChainType (X : TopCat.{0}) (n : ℕ) : Type :=
  ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj X).X n : Type)

instance (X : TopCat.{0}) (n : ℕ) : AddCommGroup (singularChainType R X n) :=
  inferInstance

/-- Direct sum of all singular chain groups. -/
abbrev TotalSingularChains (X : TopCat.{0}) : Type :=
  DirectSum ℕ (singularChainType R X)

instance (X : TopCat.{0}) : AddCommGroup (TotalSingularChains R X) :=
  inferInstance

noncomputable def dApply (X : TopCat.{0}) (n : ℕ) :
    singularChainType R X (n + 1) →+ singularChainType R X n :=
  AddMonoidHom.mk'
    (fun x =>
      ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj X).d
        (n + 1) n).hom x)
    (by intro x y; simp [map_add])

noncomputable def SApply (X : TopCat.{0}) (n : ℕ) :
    singularChainType R X n →+ singularChainType R X n :=
  AddMonoidHom.mk'
    (fun x =>
      (PlatonicSolids.SingularExcision.singularSubdivisionHom R X n).hom x)
    (by intro x y; simp [map_add])

noncomputable def HApply (X : TopCat.{0}) (n : ℕ) :
    singularChainType R X n →+ singularChainType R X (n + 1) :=
  AddMonoidHom.mk'
    (fun x =>
      (PlatonicSolids.SingularExcision.singularPrismHom R X n).hom x)
    (by intro x y; simp [map_add])

noncomputable def dTotal (X : TopCat.{0}) :
    TotalSingularChains R X →+ TotalSingularChains R X :=
  DirectSum.toAddMonoid fun n =>
    match n with
    | 0 => 0
    | n + 1 => (DirectSum.of (singularChainType R X) n).comp (dApply R X n)

noncomputable def STotal (X : TopCat.{0}) :
    TotalSingularChains R X →+ TotalSingularChains R X :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (singularChainType R X) n).comp (SApply R X n)

noncomputable def HTotal (X : TopCat.{0}) :
    TotalSingularChains R X →+ TotalSingularChains R X :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (singularChainType R X) (n + 1)).comp (HApply R X n)

lemma dTotal_of_zero (X : TopCat.{0})
    (y : singularChainType R X 0) :
    dTotal R X (DirectSum.of (singularChainType R X) 0 y) = 0 :=
  DirectSum.toAddMonoid_of _ 0 y

lemma dTotal_of_succ (X : TopCat.{0}) (n : ℕ)
    (y : singularChainType R X (n + 1)) :
    dTotal R X (DirectSum.of (singularChainType R X) (n + 1) y) =
      DirectSum.of (singularChainType R X) n (dApply R X n y) :=
  DirectSum.toAddMonoid_of _ (n + 1) y

lemma STotal_of (X : TopCat.{0}) (n : ℕ)
    (y : singularChainType R X n) :
    STotal R X (DirectSum.of (singularChainType R X) n y) =
      DirectSum.of (singularChainType R X) n (SApply R X n y) :=
  DirectSum.toAddMonoid_of _ n y

lemma HTotal_of (X : TopCat.{0}) (n : ℕ)
    (y : singularChainType R X n) :
    HTotal R X (DirectSum.of (singularChainType R X) n y) =
      DirectSum.of (singularChainType R X) (n + 1) (HApply R X n y) :=
  DirectSum.toAddMonoid_of _ n y

lemma SApply_dApply (X : TopCat.{0}) (n : ℕ)
    (y : singularChainType R X (n + 1)) :
    SApply R X n (dApply R X n y) = dApply R X n (SApply R X (n + 1) y) := by
  have h :=
    (PlatonicSolids.SingularExcision.singularSubdivision R X).comm (n + 1) n
  calc
    SApply R X n (dApply R X n y) =
        ModuleCat.Hom.hom
          ((PlatonicSolids.SingularExcision.singularSubdivision R X).f n)
          (ModuleCat.Hom.hom
            ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj X).d
              (n + 1) n) y) :=
      rfl
    _ = ModuleCat.Hom.hom
          ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj X).d
              (n + 1) n ≫
            (PlatonicSolids.SingularExcision.singularSubdivision R X).f n) y :=
      (ModuleCat.comp_apply _ _ _).symm
    _ = ModuleCat.Hom.hom
          ((PlatonicSolids.SingularExcision.singularSubdivision R X).f (n + 1) ≫
            ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj X).d
              (n + 1) n)) y := by
      rw [← h]
    _ = dApply R X n (SApply R X (n + 1) y) := by
      rw [ModuleCat.comp_apply]; rfl

lemma homotopyApply_zero (X : TopCat.{0})
    (y : singularChainType R X 0) :
    y - SApply R X 0 y = dApply R X 0 (HApply R X 0 y) := by
  have hS := PlatonicSolids.SingularExcision.singularSubdivisionHom_zero R X
  have hT := PlatonicSolids.SingularExcision.singularPrismHom_zero R X
  simp [SApply, HApply, dApply, hS, hT]

lemma homotopyApply_succ (X : TopCat.{0}) (n : ℕ)
    (y : singularChainType R X (n + 1)) :
    y - SApply R X (n + 1) y =
      HApply R X n (dApply R X n y) +
        dApply R X (n + 1) (HApply R X (n + 1) y) := by
  have hcomm :=
    (PlatonicSolids.SingularExcision.singularPrismHomotopy R X).comm (n + 1)
  have hdNext :
      dNext (n + 1)
          (PlatonicSolids.SingularExcision.singularPrismHomotopy R X).hom =
        ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj X).d
            (n + 1) n) ≫
          PlatonicSolids.SingularExcision.singularPrismHom R X n := by
    rw [Homotopy.dNext_succ_chainComplex]
    simp [PlatonicSolids.SingularExcision.singularPrismHomotopy]
  have hprevD :
      prevD (n + 1)
          (PlatonicSolids.SingularExcision.singularPrismHomotopy R X).hom =
        PlatonicSolids.SingularExcision.singularPrismHom R X (n + 1) ≫
          ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj X).d
            (n + 2) (n + 1)) := by
    rw [Homotopy.prevD_chainComplex]
    simp [PlatonicSolids.SingularExcision.singularPrismHomotopy]
  have hfun :=
    congrArg (fun f : _ ⟶ _ => ModuleCat.Hom.hom f y) hcomm
  rw [hdNext, hprevD] at hfun
  simp [SApply, HApply, dApply, ModuleCat.hom_add, ModuleCat.comp_apply] at hfun ⊢
  rw [sub_eq_iff_eq_add]
  simpa [add_assoc, add_left_comm, add_comm] using hfun

lemma homotopyApply (X : TopCat.{0}) (n : ℕ)
    (y : singularChainType R X n) :
    y - SApply R X n y =
      (match n with
        | 0 => 0
        | m + 1 => HApply R X m (dApply R X m y)) +
      dApply R X n (HApply R X n y) := by
  cases n with
  | zero =>
      simpa using homotopyApply_zero R X y
  | succ m =>
      simpa using homotopyApply_succ R X m y

/-- Ungraded subdivision data on the total singular chain group. -/
noncomputable def subdivisionData_singular (X : TopCat.{0}) :
    SubdivisionData (TotalSingularChains R X) where
  d := dTotal R X
  S := STotal R X
  H := HTotal R X
  S_comm := by
    intro x
    refine DirectSum.induction_on x ?_ ?_ ?_
    · simp
    · intro n y
      match n with
      | 0 =>
          simp [dTotal_of_zero, STotal_of]
      | n + 1 =>
          simp [dTotal_of_succ, STotal_of, SApply_dApply]
    · intro a b ha hb
      simp [map_add, ha, hb]
  homotopy := by
    intro x
    refine DirectSum.induction_on x ?_ ?_ ?_
    · simp
    · intro n y
      have h := homotopyApply R X n y
      match n with
      | 0 =>
          simp [dTotal_of_zero, STotal_of, HTotal_of,
            PlatonicSolids.SingularExcision.singularPrismHom_zero,
            PlatonicSolids.SingularExcision.singularSubdivisionHom_zero,
            HApply, SApply]
      | n + 1 =>
          simp [dTotal_of_succ, STotal_of, HTotal_of]
          have h' := congrArg (DirectSum.of (singularChainType R X) (n + 1)) h
          simpa [map_add, map_sub, add_comm] using h'
    · intro a b ha hb
      simp only [map_add]
      have hsum : a + b - (STotal R X a + STotal R X b) =
          (a - STotal R X a) + (b - STotal R X b) := by abel
      rw [hsum, ha, hb]
      abel

variable {Y : Type} [TopologicalSpace Y]

/-- A degree-`n` chain is small when it is in the image of the
small-subcomplex inclusion. -/
def isSmallChain {A B : Set Y} {n : ℕ}
    (x : singularChainType R (.of Y) n) : Prop :=
  ∃ y : ((small A B : SSet).chainComplex R).X n,
    ModuleCat.Hom.hom ((SSet.chainComplexMap (small A B).ι R).f n) y = x

lemma isSmallChain_zero {A B : Set Y} {n : ℕ} :
    isSmallChain (R := R) (A := A) (B := B) (n := n) 0 :=
  ⟨0, map_zero _⟩

lemma isSmallChain_add {A B : Set Y} {n : ℕ}
    {x₁ x₂ : singularChainType R (.of Y) n}
    (h₁ : isSmallChain (R := R) (A := A) (B := B) x₁)
    (h₂ : isSmallChain (R := R) (A := A) (B := B) x₂) :
    isSmallChain (R := R) (A := A) (B := B) (x₁ + x₂) := by
  obtain ⟨y₁, hy₁⟩ := h₁
  obtain ⟨y₂, hy₂⟩ := h₂
  refine ⟨y₁ + y₂, ?_⟩
  rw [map_add, hy₁, hy₂]
  exact rfl

lemma isSmallChain_neg {A B : Set Y} {n : ℕ}
    {x : singularChainType R (.of Y) n}
    (h : isSmallChain (R := R) (A := A) (B := B) x) :
    isSmallChain (R := R) (A := A) (B := B) (-x) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨-y, ?_⟩
  rw [map_neg, hy]
  exact rfl

/-- The small-chain subgroup of the total singular chain group. -/
def smallChainsSubgroup (A B : Set Y) :
    AddSubgroup (TotalSingularChains R (.of Y)) where
  carrier := { x | ∀ n, isSmallChain (R := R) (A := A) (B := B) (x n) }
  zero_mem' := fun n => by
    convert isSmallChain_zero (R := R) (A := A) (B := B) (n := n)
  add_mem' hx hy n := isSmallChain_add (R := R) (hx n) (hy n)
  neg_mem' hx n := isSmallChain_neg (R := R) (hx n)

lemma isSmallChain_d {A B : Set Y} {n : ℕ}
    {x : singularChainType R (.of Y) (n + 1)}
    (hx : isSmallChain (R := R) (A := A) (B := B) x) :
    isSmallChain (R := R) (A := A) (B := B) (dApply R (.of Y) n x) := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨((small A B : SSet).chainComplex R).d (n + 1) n y, ?_⟩
  have hcomm := (SSet.chainComplexMap (small A B).ι R).comm (n + 1) n
  calc
    ModuleCat.Hom.hom ((SSet.chainComplexMap (small A B).ι R).f n)
        (((small A B : SSet).chainComplex R).d (n + 1) n y) =
        ModuleCat.Hom.hom
          (((small A B : SSet).chainComplex R).d (n + 1) n ≫
            (SSet.chainComplexMap (small A B).ι R).f n) y :=
      (ModuleCat.comp_apply _ _ _).symm
    _ = ModuleCat.Hom.hom
          ((SSet.chainComplexMap (small A B).ι R).f (n + 1) ≫
            ((TopCat.toSSet.obj (.of Y)).chainComplex R).d (n + 1) n) y := by
      rw [← hcomm]
    _ = dApply R (.of Y) n x := by
      rw [ModuleCat.comp_apply, hy]
      rfl

/-- The inclusion of a small simplex, as an ambient chain, is small. -/
lemma isSmallChain_ι {A B : Set Y} {n : ℕ}
    (s : (TopCat.toSSet.obj (.of Y)) _⦋n⦌)
    (hs : s ∈ (small A B).obj (.op (.mk n))) (r : R) :
    isSmallChain (R := R) (A := A) (B := B)
      (ModuleCat.Hom.hom
        ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R) s) r) := by
  let s' : (small A B : SSet) _⦋n⦌ := ⟨s, hs⟩
  refine ⟨ModuleCat.Hom.hom ((small A B : SSet).ιChainComplex (R := R) s') r, ?_⟩
  have hι :=
    SSet.ι_chainComplexMap_f (X := (small A B : SSet))
      (Y := TopCat.toSSet.obj (.of Y)) (f := (small A B).ι) (R := R) s'
  have happ := congrArg (fun f : _ ⟶ _ => ModuleCat.Hom.hom f r) hι
  have hcomp :
      ModuleCat.Hom.hom
          (((small A B : SSet).ιChainComplex (R := R) s') ≫
            (SSet.chainComplexMap (small A B).ι R).f n) r =
        ModuleCat.Hom.hom ((SSet.chainComplexMap (small A B).ι R).f n)
          (ModuleCat.Hom.hom ((small A B : SSet).ιChainComplex (R := R) s') r) := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  calc
    ModuleCat.Hom.hom ((SSet.chainComplexMap (small A B).ι R).f n)
        (ModuleCat.Hom.hom ((small A B : SSet).ιChainComplex (R := R) s') r) =
        ModuleCat.Hom.hom
          (((small A B : SSet).ιChainComplex (R := R) s') ≫
            (SSet.chainComplexMap (small A B).ι R).f n) r :=
      hcomp.symm
    _ = ModuleCat.Hom.hom
          ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R)
            ((small A B).ι.app (.op (.mk n)) s')) r :=
      happ
    _ = ModuleCat.Hom.hom
          ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R) s) r := by
      congr 2

lemma SApply_ι {X : TopCat.{0}} {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) (r : R) :
    SApply R X n
        (ModuleCat.Hom.hom ((TopCat.toSSet.obj X).ιChainComplex (R := R) s) r) =
      ModuleCat.Hom.hom
        (PlatonicSolids.SingularExcision.singularSubdivideGenerator R s) r := by
  have h :=
    PlatonicSolids.SingularExcision.ι_singularSubdivisionHom (R := R) (X := X) s
  have happ := congrArg (fun f : _ ⟶ _ => ModuleCat.Hom.hom f r) h
  have hcomp :
      ModuleCat.Hom.hom
          (((TopCat.toSSet.obj X).ιChainComplex (R := R) s) ≫
            PlatonicSolids.SingularExcision.singularSubdivisionHom R X n) r =
        SApply R X n
          (ModuleCat.Hom.hom
            ((TopCat.toSSet.obj X).ιChainComplex (R := R) s) r) := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]; rfl
  exact hcomp.symm.trans happ

lemma HApply_ι {X : TopCat.{0}} {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) (r : R) :
    HApply R X n
        (ModuleCat.Hom.hom ((TopCat.toSSet.obj X).ιChainComplex (R := R) s) r) =
      ModuleCat.Hom.hom
        (PlatonicSolids.SingularExcision.singularPrismGenerator R s) r := by
  have h :=
    PlatonicSolids.SingularExcision.ι_singularPrismHom (R := R) (X := X) s
  have happ := congrArg (fun f : _ ⟶ _ => ModuleCat.Hom.hom f r) h
  have hcomp :
      ModuleCat.Hom.hom
          (((TopCat.toSSet.obj X).ιChainComplex (R := R) s) ≫
            PlatonicSolids.SingularExcision.singularPrismHom R X n) r =
        HApply R X n
          (ModuleCat.Hom.hom
            ((TopCat.toSSet.obj X).ιChainComplex (R := R) s) r) := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]; rfl
  exact hcomp.symm.trans happ

lemma isSmallChain_nsmul {A B : Set Y} {n : ℕ}
    {x : singularChainType R (.of Y) n} (m : ℕ)
    (hx : isSmallChain (R := R) (A := A) (B := B) x) :
    isSmallChain (R := R) (A := A) (B := B) (m • x) := by
  induction m with
  | zero =>
      simpa using isSmallChain_zero (R := R) (A := A) (B := B) (n := n)
  | succ m ih =>
      rw [succ_nsmul]
      exact isSmallChain_add (R := R) ih hx

lemma isSmallChain_zsmul {A B : Set Y} {n : ℕ}
    {x : singularChainType R (.of Y) n} (z : ℤ)
    (hx : isSmallChain (R := R) (A := A) (B := B) x) :
    isSmallChain (R := R) (A := A) (B := B) (z • x) := by
  cases z with
  | ofNat m =>
      simpa using isSmallChain_nsmul (R := R) m hx
  | negSucc m =>
      simpa [negSucc_zsmul] using
        isSmallChain_neg (R := R)
          (isSmallChain_nsmul (R := R) (m + 1) hx)

lemma isSmallChain_realizeAffine {A B : Set Y} {p q : ℕ}
    (s : (TopCat.toSSet.obj (.of Y)) _⦋q⦌)
    (c : PlatonicSolids.SingularExcision.AffineChain
      (stdSimplex ℝ (Fin (q + 1))) p)
    (hc : ∀ τ ∈ c.support,
      PlatonicSolids.SingularExcision.reparametrizeSingularSimplex s τ ∈
        (small A B).obj (.op (.mk p)))
    (r : R) :
    isSmallChain (R := R) (A := A) (B := B)
      (ModuleCat.Hom.hom
        (PlatonicSolids.SingularExcision.realizeAffineChain R s c) r) := by
  induction c using Finsupp.induction with
  | zero =>
      simpa [PlatonicSolids.SingularExcision.realizeAffineChain_zero] using
        isSmallChain_zero (R := R) (A := A) (B := B) (n := p)
  | single_add τ z c hτ hz ih =>
      have hx :
          ModuleCat.Hom.hom
              (PlatonicSolids.SingularExcision.realizeAffineChain R s
                (Finsupp.single τ z + c)) r =
            z • ModuleCat.Hom.hom
              (PlatonicSolids.SingularExcision.realizeAffineSimplex R s τ) r +
            ModuleCat.Hom.hom
              (PlatonicSolids.SingularExcision.realizeAffineChain R s c) r := by
        rw [map_add, PlatonicSolids.SingularExcision.realizeAffineChain_single]
        simp [ModuleCat.hom_add, LinearMap.map_smul]
      rw [hx]
      refine isSmallChain_add (R := R) ?_
        (ih fun ρ hρ => hc ρ (by
          have hne : ρ ≠ τ := fun e => hτ (e ▸ hρ)
          simp [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, hne] at hρ ⊢
          exact hρ))
      have hτs := hc τ (by
        simpa [Finsupp.mem_support_iff, Finsupp.add_apply,
          Finsupp.notMem_support_iff.mp hτ] using hz)
      have hgen := isSmallChain_ι (R := R) (A := A) (B := B)
        (PlatonicSolids.SingularExcision.reparametrizeSingularSimplex s τ)
        hτs r
      simpa [PlatonicSolids.SingularExcision.realizeAffineSimplex] using
        isSmallChain_zsmul (R := R) z hgen

lemma isSmallChain_S_generator {A B : Set Y} {n : ℕ}
    {s : (TopCat.toSSet.obj (.of Y)) _⦋n⦌}
    (hs : s ∈ (small A B).obj (.op (.mk n))) (r : R) :
    isSmallChain (R := R) (A := A) (B := B)
      (SApply R (.of Y) n
        (ModuleCat.Hom.hom
          ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R) s) r)) := by
  rw [SApply_ι]
  exact isSmallChain_realizeAffine (R := R) (A := A) (B := B) s
    (PlatonicSolids.SingularExcision.standardSubdivision n)
    (fun τ _ => reparametrize_mem_small_of_mem_small s τ hs) r

lemma isSmallChain_H_generator {A B : Set Y} {n : ℕ}
    {s : (TopCat.toSSet.obj (.of Y)) _⦋n⦌}
    (hs : s ∈ (small A B).obj (.op (.mk n))) (r : R) :
    isSmallChain (R := R) (A := A) (B := B)
      (HApply R (.of Y) n
        (ModuleCat.Hom.hom
          ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R) s) r)) := by
  rw [HApply_ι]
  exact isSmallChain_realizeAffine (R := R) (A := A) (B := B) s
    (PlatonicSolids.SingularExcision.standardPrism n)
    (fun τ _ => reparametrize_mem_small_of_mem_small s τ hs) r

lemma realizeAffineChain_comp_singularSubdivisionHom
    {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (c : PlatonicSolids.SingularExcision.AffineChain
      (stdSimplex ℝ (Fin (q + 1))) p) :
    PlatonicSolids.SingularExcision.realizeAffineChain R s c ≫
        PlatonicSolids.SingularExcision.singularSubdivisionHom R X p =
      PlatonicSolids.SingularExcision.realizeAffineChain R s
        (PlatonicSolids.SingularExcision.subdivideStd (q := q) p c) := by
  induction c using Finsupp.induction with
  | zero =>
      simp [PlatonicSolids.SingularExcision.realizeAffineChain_zero]
  | single_add τ z c hτ hz ih =>
      simp [map_add, Preadditive.add_comp, ih,
        PlatonicSolids.SingularExcision.realizeAffineChain_single,
        Preadditive.zsmul_comp]
      have hσ :
          PlatonicSolids.SingularExcision.realizeAffineSimplex R s τ ≫
              PlatonicSolids.SingularExcision.singularSubdivisionHom R X p =
            PlatonicSolids.SingularExcision.realizeAffineChain R s
              (PlatonicSolids.SingularExcision.subdivideStd (q := q) p
                (PlatonicSolids.SingularExcision.simplex τ)) := by
        rw [PlatonicSolids.SingularExcision.realizeAffineSimplex]
        erw [PlatonicSolids.SingularExcision.ι_singularSubdivisionHom]
        rw [PlatonicSolids.SingularExcision.singularSubdivideGenerator,
          ← PlatonicSolids.SingularExcision.realizeAffineChain_subdivideStd_simplex]
      rw [hσ]
      rw [show Finsupp.single τ z = z • PlatonicSolids.SingularExcision.simplex τ
        by simp [PlatonicSolids.SingularExcision.simplex]]
      simp [map_zsmul]

lemma ι_singularSubdivisionIterate
    {X : TopCat.{0}} {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) (N : ℕ) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) s ≫
        (PlatonicSolids.SingularExcision.singularSubdivisionIterate R X N).f n =
      PlatonicSolids.SingularExcision.realizeAffineChain R s
        ((PlatonicSolids.SingularExcision.subdivideStd (q := n) n)^[N]
          (PlatonicSolids.SingularExcision.simplex
            (PlatonicSolids.SingularExcision.idSimplex n))) := by
  induction N with
  | zero =>
      simp [PlatonicSolids.SingularExcision.singularSubdivisionIterate_zero,
        PlatonicSolids.SingularExcision.realizeAffineChain_simplex,
        PlatonicSolids.SingularExcision.realizeAffineSimplex_id]
      exact Category.comp_id _
  | succ N ih =>
      rw [PlatonicSolids.SingularExcision.singularSubdivisionIterate_f_succ]
      erw [← Category.assoc, ih, realizeAffineChain_comp_singularSubdivisionHom]
      rw [Function.iterate_succ_apply']

lemma eventual_small_generator_of_openCover
    {n : ℕ} (s : (TopCat.toSSet.obj (.of Y)) _⦋n⦌)
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : A ∪ B = univ) (r : R) :
    ∃ N : ℕ, isSmallChain (R := R) (A := A) (B := B)
      (ModuleCat.Hom.hom
        ((PlatonicSolids.SingularExcision.singularSubdivisionIterate
            R (.of Y) N).f n)
        (ModuleCat.Hom.hom
          ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R) s) r)) := by
  obtain ⟨N, hN⟩ :=
    eventual_small_reparametrize_of_openCover s hA hB hAB
  refine ⟨N, ?_⟩
  have hiter := ι_singularSubdivisionIterate (R := R) (X := .of Y) s N
  have hcomp :
      ModuleCat.Hom.hom
          (((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R) s) ≫
            (PlatonicSolids.SingularExcision.singularSubdivisionIterate
              R (.of Y) N).f n) r =
        ModuleCat.Hom.hom
          ((PlatonicSolids.SingularExcision.singularSubdivisionIterate
              R (.of Y) N).f n)
          (ModuleCat.Hom.hom
            ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R) s) r) := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    rfl
  have happ := congrArg (fun f : _ ⟶ _ => ModuleCat.Hom.hom f r) hiter
  have hval :
      ModuleCat.Hom.hom
          ((PlatonicSolids.SingularExcision.singularSubdivisionIterate
              R (.of Y) N).f n)
          (ModuleCat.Hom.hom
            ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R) s) r) =
        ModuleCat.Hom.hom
          (PlatonicSolids.SingularExcision.realizeAffineChain R s
            ((PlatonicSolids.SingularExcision.subdivideStd (q := n) n)^[N]
              (PlatonicSolids.SingularExcision.simplex
                (PlatonicSolids.SingularExcision.idSimplex n)))) r :=
    hcomp.symm.trans happ
  rw [hval]
  exact isSmallChain_realizeAffine (R := R) (A := A) (B := B) s _ hN r

/-- Index type of singular `n`-simplices. -/
abbrev SingularSimplex (X : TopCat.{0}) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X) _⦋n⦌

/-- Degree-`n` singular chains are the coproduct of copies of `R`. -/
lemma singularChain_X_eq (X : TopCat.{0}) (n : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj X).X n) =
      ∐ fun _ : SingularSimplex X n ↦ R :=
  rfl

/-- Small `n`-chains are the coproduct of copies of `R` indexed by small
simplices. -/
lemma smallChain_X_eq (A B : Set Y) (n : ℕ) :
    (((small A B : SSet).chainComplex R).X n) =
      ∐ fun _ : (small A B : SSet) _⦋n⦌ ↦ R :=
  rfl

/-- Every singular `n`-chain is a finite linear combination of generators. -/
lemma singularChain_eq_sum {X : TopCat.{0}} {n : ℕ}
    (x : singularChainType R X n) :
    x = ∑ s ∈ ModuleCat.coprodSupport (fun _ : SingularSimplex X n ↦ R) x,
      ModuleCat.Hom.hom
        ((TopCat.toSSet.obj X).ιChainComplex (R := R) s)
        ((ModuleCat.coprodIsoDirectSum
            (fun _ : SingularSimplex X n ↦ R)).hom x s) := by
  classical
  simpa [SSet.ιChainComplex] using
    ModuleCat.eq_sum_ι_apply_coprodSupport
      (fun _ : SingularSimplex X n ↦ R) x

/-- Every small `n`-chain is a finite linear combination of small generators. -/
lemma smallChain_eq_sum {A B : Set Y} {n : ℕ}
    (y : ((small A B : SSet).chainComplex R).X n) :
    y = ∑ s ∈ ModuleCat.coprodSupport
        (fun _ : (small A B : SSet) _⦋n⦌ ↦ R) y,
      ModuleCat.Hom.hom
        ((small A B : SSet).ιChainComplex (R := R) s)
        ((ModuleCat.coprodIsoDirectSum
            (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s) := by
  classical
  simpa [SSet.ιChainComplex] using
    ModuleCat.eq_sum_ι_apply_coprodSupport
      (fun _ : (small A B : SSet) _⦋n⦌ ↦ R) y

lemma SApply_sum {X : TopCat.{0}} {n : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → singularChainType R X n) :
    SApply R X n (∑ i ∈ s, f i) = ∑ i ∈ s, SApply R X n (f i) :=
  map_sum (SApply R X n) f s

lemma HApply_sum {X : TopCat.{0}} {n : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → singularChainType R X n) :
    HApply R X n (∑ i ∈ s, f i) = ∑ i ∈ s, HApply R X n (f i) :=
  map_sum (HApply R X n) f s

lemma SApply_iterate_sum {X : TopCat.{0}} {n N : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → singularChainType R X n) :
    (SApply R X n)^[N] (∑ i ∈ s, f i) = ∑ i ∈ s, (SApply R X n)^[N] (f i) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply', ih, SApply_sum]
      simp [Function.iterate_succ_apply']

lemma isSmallChain_sum {A B : Set Y} {n : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → singularChainType R (.of Y) n)
    (hf : ∀ i ∈ s, isSmallChain (R := R) (A := A) (B := B) (f i)) :
    isSmallChain (R := R) (A := A) (B := B) (∑ i ∈ s, f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using isSmallChain_zero (R := R) (A := A) (B := B) (n := n)
  · intro i s his ih hf
    rw [Finset.sum_insert his]
    exact isSmallChain_add (R := R)
      (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma SApply_iterate {X : TopCat.{0}} (n N : ℕ)
    (y : singularChainType R X n) :
    (SApply R X n)^[N] y =
      ModuleCat.Hom.hom
        ((PlatonicSolids.SingularExcision.singularSubdivisionIterate R X N).f n)
        y := by
  induction N with
  | zero =>
      simp [PlatonicSolids.SingularExcision.singularSubdivisionIterate_zero]
  | succ N ih =>
      rw [Function.iterate_succ_apply', ih,
        PlatonicSolids.SingularExcision.singularSubdivisionIterate_f_succ]
      rfl

lemma STotal_apply (X : TopCat.{0}) (n : ℕ)
    (x : TotalSingularChains R X) :
    STotal R X x n = SApply R X n (x n) := by
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp
  · intro m y
    rw [STotal_of]
    by_cases h : m = n
    · subst h
      simp [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne m n _ (Ne.symm h),
        DirectSum.of_eq_of_ne m n y (Ne.symm h)]
      simp
  · intro a b ha hb
    simp [map_add, ha, hb]

lemma STotal_iterate_apply (X : TopCat.{0}) (n N : ℕ)
    (x : TotalSingularChains R X) :
    ((STotal R X)^[N] x) n = (SApply R X n)^[N] (x n) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply', STotal_apply, ih,
        Function.iterate_succ_apply']

lemma dTotal_apply (X : TopCat.{0}) (n : ℕ)
    (x : TotalSingularChains R X) :
    dTotal R X x n = dApply R X n (x (n + 1)) := by
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp
  · intro m y
    match m with
    | 0 =>
        rw [dTotal_of_zero,
          DirectSum.of_eq_of_ne 0 (n + 1) y (Nat.succ_ne_zero n)]
        simp
    | m + 1 =>
        rw [dTotal_of_succ]
        by_cases h : m = n
        · subst h
          simp [DirectSum.of_eq_same]
        · rw [DirectSum.of_eq_of_ne m n _ (Ne.symm h),
            DirectSum.of_eq_of_ne (m + 1) (n + 1) y (mt Nat.succ.inj (Ne.symm h))]
          simp
  · intro a b ha hb
    simp [map_add, ha, hb]

lemma HTotal_apply_zero (X : TopCat.{0})
    (x : TotalSingularChains R X) :
    HTotal R X x 0 = 0 := by
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp
  · intro m y
    rw [HTotal_of]
    exact DirectSum.of_eq_of_ne (m + 1) 0 _ (Nat.succ_ne_zero m).symm
  · intro a b ha hb
    simp [map_add, ha, hb]

lemma HTotal_apply_succ (X : TopCat.{0}) (n : ℕ)
    (x : TotalSingularChains R X) :
    HTotal R X x (n + 1) = HApply R X n (x n) := by
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp
  · intro m y
    rw [HTotal_of]
    by_cases h : m = n
    · subst h
      simp [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne (m + 1) (n + 1) _ (mt Nat.succ.inj (Ne.symm h)),
        DirectSum.of_eq_of_ne m n y (Ne.symm h)]
      simp
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- Subdivision preserves smallness of an arbitrary small chain. -/
lemma isSmallChain_S {A B : Set Y} {n : ℕ}
    {x : singularChainType R (.of Y) n}
    (hx : isSmallChain (R := R) (A := A) (B := B) x) :
    isSmallChain (R := R) (A := A) (B := B) (SApply R (.of Y) n x) := by
  classical
  obtain ⟨y, hy⟩ := hx
  have hy_sum := smallChain_eq_sum (R := R) (A := A) (B := B) y
  have hx_sum :
      x = ∑ s ∈ ModuleCat.coprodSupport
          (fun _ : (small A B : SSet) _⦋n⦌ ↦ R) y,
        ModuleCat.Hom.hom
          ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R)
            ((small A B).ι.app _ s))
          ((ModuleCat.coprodIsoDirectSum
              (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s) := by
    have hmap := congrArg
        (ModuleCat.Hom.hom ((SSet.chainComplexMap (small A B).ι R).f n)) hy_sum
    rw [hy] at hmap
    rw [hmap, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hι :=
      SSet.ι_chainComplexMap_f (X := (small A B : SSet))
        (Y := TopCat.toSSet.obj (.of Y)) (f := (small A B).ι) (R := R) s
    have happ :=
      congrArg (fun f : _ ⟶ _ =>
        ModuleCat.Hom.hom f
          ((ModuleCat.coprodIsoDirectSum
              (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s)) hι
    have hcomp :
        ModuleCat.Hom.hom
            (((small A B : SSet).ιChainComplex (R := R) s) ≫
              (SSet.chainComplexMap (small A B).ι R).f n)
            ((ModuleCat.coprodIsoDirectSum
                (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s) =
          ModuleCat.Hom.hom ((SSet.chainComplexMap (small A B).ι R).f n)
            (ModuleCat.Hom.hom ((small A B : SSet).ιChainComplex (R := R) s)
              ((ModuleCat.coprodIsoDirectSum
                  (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s)) := by
      rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact hcomp.symm.trans happ
  rw [hx_sum]
  refine (SApply_sum (R := R) (X := .of Y)
      (ModuleCat.coprodSupport (fun _ : (small A B : SSet) _⦋n⦌ ↦ R) y)
      (fun s => ModuleCat.Hom.hom
        ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R)
          ((small A B).ι.app _ s))
        ((ModuleCat.coprodIsoDirectSum
            (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s))).symm ▸ ?_
  refine isSmallChain_sum (R := R) _ _ fun s _ => ?_
  simpa [SApply_ι] using
    isSmallChain_S_generator (R := R) (A := A) (B := B) s.property
      ((ModuleCat.coprodIsoDirectSum
          (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s)

/-- The prism operator preserves smallness of an arbitrary small chain. -/
lemma isSmallChain_H {A B : Set Y} {n : ℕ}
    {x : singularChainType R (.of Y) n}
    (hx : isSmallChain (R := R) (A := A) (B := B) x) :
    isSmallChain (R := R) (A := A) (B := B) (HApply R (.of Y) n x) := by
  classical
  obtain ⟨y, hy⟩ := hx
  have hy_sum := smallChain_eq_sum (R := R) (A := A) (B := B) y
  have hx_sum :
      x = ∑ s ∈ ModuleCat.coprodSupport
          (fun _ : (small A B : SSet) _⦋n⦌ ↦ R) y,
        ModuleCat.Hom.hom
          ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R)
            ((small A B).ι.app _ s))
          ((ModuleCat.coprodIsoDirectSum
              (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s) := by
    have hmap := congrArg
        (ModuleCat.Hom.hom ((SSet.chainComplexMap (small A B).ι R).f n)) hy_sum
    rw [hy] at hmap
    rw [hmap, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hι :=
      SSet.ι_chainComplexMap_f (X := (small A B : SSet))
        (Y := TopCat.toSSet.obj (.of Y)) (f := (small A B).ι) (R := R) s
    have happ :=
      congrArg (fun f : _ ⟶ _ =>
        ModuleCat.Hom.hom f
          ((ModuleCat.coprodIsoDirectSum
              (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s)) hι
    have hcomp :
        ModuleCat.Hom.hom
            (((small A B : SSet).ιChainComplex (R := R) s) ≫
              (SSet.chainComplexMap (small A B).ι R).f n)
            ((ModuleCat.coprodIsoDirectSum
                (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s) =
          ModuleCat.Hom.hom ((SSet.chainComplexMap (small A B).ι R).f n)
            (ModuleCat.Hom.hom ((small A B : SSet).ιChainComplex (R := R) s)
              ((ModuleCat.coprodIsoDirectSum
                  (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s)) := by
      rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact hcomp.symm.trans happ
  rw [hx_sum]
  refine (HApply_sum (R := R) (X := .of Y)
      (ModuleCat.coprodSupport (fun _ : (small A B : SSet) _⦋n⦌ ↦ R) y)
      (fun s => ModuleCat.Hom.hom
        ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R)
          ((small A B).ι.app _ s))
        ((ModuleCat.coprodIsoDirectSum
            (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s))).symm ▸ ?_
  refine isSmallChain_sum (R := R) _ _ fun s _ => ?_
  simpa [HApply_ι] using
    isSmallChain_H_generator (R := R) (A := A) (B := B) s.property
      ((ModuleCat.coprodIsoDirectSum
          (fun _ : (small A B : SSet) _⦋n⦌ ↦ R)).hom y s)

/-- The small-chain subgroup is invariant under `d`, `S`, and `H`. -/
lemma smallInvariant_of_openCover (A B : Set Y) :
    (subdivisionData_singular R (.of Y)).SmallInvariant
      (smallChainsSubgroup R A B) where
  d_mem := by
    intro x hx n
    change isSmallChain (R := R) (A := A) (B := B) (dTotal R (.of Y) x n)
    rw [dTotal_apply]
    exact isSmallChain_d (R := R) (hx (n + 1))
  S_mem := by
    intro x hx n
    change isSmallChain (R := R) (A := A) (B := B) (STotal R (.of Y) x n)
    rw [STotal_apply]
    exact isSmallChain_S (R := R) (hx n)
  H_mem := by
    intro x hx n
    match n with
    | 0 =>
        change isSmallChain (R := R) (A := A) (B := B)
          (HTotal R (.of Y) x 0)
        rw [HTotal_apply_zero]
        exact isSmallChain_zero (R := R) (A := A) (B := B) (n := 0)
    | n + 1 =>
        change isSmallChain (R := R) (A := A) (B := B)
          (HTotal R (.of Y) x (n + 1))
        rw [HTotal_apply_succ]
        exact isSmallChain_H (R := R) (hx n)

lemma isSmallChain_S_iterate {A B : Set Y} {n : ℕ}
    {x : singularChainType R (.of Y) n} (N : ℕ)
    (hx : isSmallChain (R := R) (A := A) (B := B) x) :
    isSmallChain (R := R) (A := A) (B := B) ((SApply R (.of Y) n)^[N] x) := by
  induction N with
  | zero => simpa
  | succ N ih =>
      rw [Function.iterate_succ_apply']
      exact isSmallChain_S (R := R) ih

lemma eventual_small_generator_iterate_of_openCover
    {n : ℕ} (s : (TopCat.toSSet.obj (.of Y)) _⦋n⦌)
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : A ∪ B = univ) (r : R) :
    ∃ N : ℕ, ∀ N' ≥ N,
      isSmallChain (R := R) (A := A) (B := B)
        ((SApply R (.of Y) n)^[N']
          (ModuleCat.Hom.hom
            ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R) s) r)) := by
  obtain ⟨N, hN⟩ :=
    eventual_small_generator_of_openCover (R := R) s hA hB hAB r
  refine ⟨N, fun N' hN' => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hN'
  rw [hk, Nat.add_comm, Function.iterate_add_apply]
  exact isSmallChain_S_iterate (R := R) k (by
    simpa [SApply_iterate] using hN)

/-- Every finite singular chain becomes small after enough subdivisions. -/
lemma eventual_small_of_degree
    {n : ℕ} (x : singularChainType R (.of Y) n)
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : A ∪ B = univ) :
    ∃ N : ℕ, isSmallChain (R := R) (A := A) (B := B)
      ((SApply R (.of Y) n)^[N] x) := by
  classical
  have hx := singularChain_eq_sum (R := R) x
  let supp := ModuleCat.coprodSupport (fun _ : SingularSimplex (.of Y) n ↦ R) x
  have hgen : ∀ s ∈ supp, ∃ N : ℕ, ∀ N' ≥ N,
      isSmallChain (R := R) (A := A) (B := B)
        ((SApply R (.of Y) n)^[N']
          (ModuleCat.Hom.hom
            ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R) s)
            ((ModuleCat.coprodIsoDirectSum
                (fun _ : SingularSimplex (.of Y) n ↦ R)).hom x s))) :=
    fun s _ =>
      eventual_small_generator_iterate_of_openCover (R := R) s hA hB hAB _
  choose! N hN using hgen
  refine ⟨supp.sup N, ?_⟩
  rw [hx]
  refine (SApply_iterate_sum (R := R) (X := .of Y) supp
      (fun s => ModuleCat.Hom.hom
        ((TopCat.toSSet.obj (.of Y)).ιChainComplex (R := R) s)
        ((ModuleCat.coprodIsoDirectSum
            (fun _ : SingularSimplex (.of Y) n ↦ R)).hom x s))).symm ▸ ?_
  refine isSmallChain_sum (R := R) _ _ fun s hs =>
    hN s hs _ (Finset.le_sup hs)

lemma eventual_small_of_degree_le
    {n : ℕ} (x : singularChainType R (.of Y) n)
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : A ∪ B = univ) :
    ∃ N : ℕ, ∀ N' ≥ N, isSmallChain (R := R) (A := A) (B := B)
      ((SApply R (.of Y) n)^[N'] x) := by
  obtain ⟨N, hN⟩ := eventual_small_of_degree (R := R) x hA hB hAB
  refine ⟨N, fun N' hN' => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hN'
  rw [hk, Nat.add_comm, Function.iterate_add_apply]
  exact isSmallChain_S_iterate (R := R) k hN

lemma eventual_small_of_chain
    (x : TotalSingularChains R (.of Y))
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : A ∪ B = univ) :
    ∃ N : ℕ, (STotal R (.of Y))^[N] x ∈ smallChainsSubgroup R A B := by
  classical
  have hdeg : ∀ n ∈ x.support, ∃ N : ℕ, ∀ N' ≥ N,
      isSmallChain (R := R) (A := A) (B := B)
        ((SApply R (.of Y) n)^[N'] (x n)) :=
    fun n _ => eventual_small_of_degree_le (R := R) (x n) hA hB hAB
  choose! N hN using hdeg
  refine ⟨x.support.sup N, fun n => ?_⟩
  rw [STotal_iterate_apply]
  by_cases hn : n ∈ x.support
  · exact hN n hn _ (Finset.le_sup hn)
  · have hx0 : x n = 0 := DFinsupp.notMem_support_iff.mp hn
    simpa [hx0] using isSmallChain_zero (R := R) (A := A) (B := B) (n := n)

/-- Every homology class of `Y` has a small cycle representative, and
every small boundary is the boundary of a small chain. -/
theorem small_cycles_and_boundaries_singular
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : A ∪ B = univ) :
    (∀ z : TotalSingularChains R (.of Y),
        (subdivisionData_singular R (.of Y)).Cycle z →
      ∃ b ∈ smallChainsSubgroup R A B,
        (subdivisionData_singular R (.of Y)).Cycle b ∧
        (subdivisionData_singular R (.of Y)).Homologous z b) ∧
    (∀ b : TotalSingularChains R (.of Y),
        b ∈ smallChainsSubgroup R A B →
        (subdivisionData_singular R (.of Y)).Cycle b →
        (∃ x, b = (subdivisionData_singular R (.of Y)).d x) →
      ∃ y ∈ smallChainsSubgroup R A B,
        b = (subdivisionData_singular R (.of Y)).d y) :=
  (subdivisionData_singular R (.of Y)).small_cycles_and_boundaries
    (smallChainsSubgroup R A B)
    (smallInvariant_of_openCover (R := R) A B)
    (fun x => eventual_small_of_chain (R := R) x hA hB hAB)

end

end SingularExcision

