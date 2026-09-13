/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.MonoCoprod
import PlatonicSolids.SingularExcision.CoverChains
import PlatonicSolids.SingularExcision.SmallChains

/-!
Open-cover excision: the small-subcomplex inclusion is a
quasi-isomorphism, so an open cover is excisive. The geometric retract
is in `SmallChains`; the triangle `coverComparison = iso.hom ≫ smallι`
identifies the cover comparison with that inclusion.
-/

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Set
open scoped Topology

set_option linter.unusedSectionVars false

namespace SingularExcision

noncomputable section

variable {k : Type} [Ring k] (R : ModuleCat.{0} k)
variable [HasCoproducts.{0} (ModuleCat.{0} k)]
variable [HasPullbacks (ModuleCat.{0} k)]
variable {Y : Type} [TopologicalSpace Y]

open Classical

/-- Ambient singular chains of `Y`. -/
abbrev ambientChains : ChainComplex (ModuleCat.{0} k) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj (.of Y)

/-- Small-subcomplex inclusion on singular chains. -/
def smallι (A B : Set Y) :
    (small A B : SSet).chainComplex R ⟶
      ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj (.of Y) :=
  SSet.chainComplexMap (small A B).ι R

lemma toTotal_cycle_zero (z : singularChainType R (.of Y) 0) :
    (subdivisionData_singular R (.of Y)).Cycle
      (DirectSum.of (singularChainType R (.of Y)) 0 z) :=
  dTotal_of_zero R (.of Y) z

lemma toTotal_cycle_succ {n : ℕ} {z : singularChainType R (.of Y) (n + 1)}
    (hz : dApply R (.of Y) n z = 0) :
    (subdivisionData_singular R (.of Y)).Cycle
      (DirectSum.of (singularChainType R (.of Y)) (n + 1) z) := by
  change dTotal R (.of Y) (DirectSum.of _ (n + 1) z) = 0
  rw [dTotal_of_succ, hz, map_zero]

lemma inclChains_eq_subtypeIso_comp_landsInι (A : Set Y) :
    ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
        (subtypeIncl Y A) =
      (subtypeChainComplexIso (C := ModuleCat.{0} k) R A).hom ≫
        SSet.chainComplexMap (landsIn A).ι R := by
  dsimp [subtypeChainComplexIso, singularChainComplexFunctor,
    SSet.chainComplexMap, subtypeSingularSetIso]
  rw [← Functor.map_comp, subtypeToLandsIn_ι, subtypeSingularSetMap]

lemma landsInι_eq_to_smallι (A B : Set Y) :
    SSet.chainComplexMap (landsIn A).ι R =
      SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_left : landsIn A ≤ small A B)) R ≫
        smallι R A B := by
  change
    ((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map (landsIn A).ι =
      ((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (SSet.Subcomplex.homOfLE (le_sup_left : landsIn A ≤ small A B)) ≫
        ((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map (small A B).ι
  rw [← Functor.map_comp]
  rfl

lemma landsInι_eq_to_smallι_right (A B : Set Y) :
    SSet.chainComplexMap (landsIn B).ι R =
      SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_right : landsIn B ≤ small A B)) R ≫
        smallι R A B := by
  change
    ((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map (landsIn B).ι =
      ((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (SSet.Subcomplex.homOfLE (le_sup_right : landsIn B ≤ small A B)) ≫
        ((SSet.chainComplexFunctor (ModuleCat.{0} k)).obj R).map (small A B).ι
  rw [← Functor.map_comp]
  rfl

/-- The two inclusions of `A` and `B` into `Y`, after transport to
lands-in subcomplexes, factor through `smallι`. -/
lemma coverToX_eq_desc_comp_smallι (A B : Set Y) :
    coverToX (C := ModuleCat.{0} k) R
        (interInclLeft A B) (interInclRight A B)
        (subtypeIncl Y A) (subtypeIncl Y B) (subset_square_comm A B) =
      biprod.desc
          ((subtypeChainComplexIso (C := ModuleCat.{0} k) R A).hom ≫
            SSet.chainComplexMap
              (SSet.Subcomplex.homOfLE (le_sup_left :
                landsIn A ≤ small A B)) R)
          ((subtypeChainComplexIso (C := ModuleCat.{0} k) R B).hom ≫
            SSet.chainComplexMap
              (SSet.Subcomplex.homOfLE (le_sup_right :
                landsIn B ≤ small A B)) R) ≫
        smallι R A B := by
  rw [coverToX]
  rw [inclChains_eq_subtypeIso_comp_landsInι (R := R) A]
  rw [inclChains_eq_subtypeIso_comp_landsInι (R := R) B]
  rw [landsInι_eq_to_smallι (R := R) A B]
  rw [landsInι_eq_to_smallι_right (R := R) A B]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.inl_desc]
    exact (biprod.inl_desc_assoc
      ((subtypeChainComplexIso (C := ModuleCat.{0} k) R A).hom ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_left : landsIn A ≤ small A B)) R)
      ((subtypeChainComplexIso (C := ModuleCat.{0} k) R B).hom ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_right : landsIn B ≤ small A B)) R)
      (smallι R A B)).symm
  · rw [biprod.inr_desc]
    exact (biprod.inr_desc_assoc
      ((subtypeChainComplexIso (C := ModuleCat.{0} k) R A).hom ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_left : landsIn A ≤ small A B)) R)
      ((subtypeChainComplexIso (C := ModuleCat.{0} k) R B).hom ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_right : landsIn B ≤ small A B)) R)
      (smallι R A B)).symm

/-- Abbreviation for the small-pushout legs. -/
abbrev smallInl (A B : Set Y) :=
  (subtypeChainComplexIso (C := ModuleCat.{0} k) R A).hom ≫
    SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (le_sup_left : landsIn A ≤ small A B)) R

abbrev smallInr (A B : Set Y) :=
  (subtypeChainComplexIso (C := ModuleCat.{0} k) R B).hom ≫
    SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (le_sup_right : landsIn B ≤ small A B)) R

lemma mvIncl_eq_pushoutRelation (A B : Set Y) :
    mvIncl (C := ModuleCat.{0} k) R (interInclLeft A B) (interInclRight A B) =
      pushoutRelation
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (interInclLeft A B))
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (interInclRight A B)) :=
  rfl

lemma π_comp_coverChainsIsoSmall_hom (A B : Set Y) :
    cokernel.π (mvIncl (C := ModuleCat.{0} k) R
        (interInclLeft A B) (interInclRight A B)) ≫
      (coverChainsIsoSmall (C := ModuleCat.{0} k) R A B).hom =
    biprod.desc (smallInl (R := R) A B) (smallInr (R := R) A B) := by
  let f := ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
      (interInclLeft A B)
  let g := ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
      (interInclRight A B)
  let sq := subtypeChainsSmallIsPushout (C := ModuleCat.{0} k) R A B
  have hinl := sq.inl_isoIsPushout_inv _ _ (cokernelIsPushout f g)
  have hinr := sq.inr_isoIsPushout_inv _ _ (cokernelIsPushout f g)
  refine biprod.hom_ext' _ _ ?_ ?_
  · refine Eq.trans (Eq.trans ?_ hinl)
      (biprod.inl_desc (smallInl (R := R) A B)
        (smallInr (R := R) A B)).symm
    exact (Category.assoc
      (biprod.inl : _ ⟶
        ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj (.of ↥A) ⊞
          ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj (.of ↥B))
      (cokernel.π (mvIncl (C := ModuleCat.{0} k) R
        (interInclLeft A B) (interInclRight A B)))
      (coverChainsIsoSmall (C := ModuleCat.{0} k) R A B).hom).symm
  · refine Eq.trans (Eq.trans ?_ hinr)
      (biprod.inr_desc (smallInl (R := R) A B)
        (smallInr (R := R) A B)).symm
    exact (Category.assoc
      (biprod.inr : _ ⟶
        ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj (.of ↥A) ⊞
          ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj (.of ↥B))
      (cokernel.π (mvIncl (C := ModuleCat.{0} k) R
        (interInclLeft A B) (interInclRight A B)))
      (coverChainsIsoSmall (C := ModuleCat.{0} k) R A B).hom).symm

lemma coverComparison_eq_iso_comp_smallι (A B : Set Y) :
    coverComparison (C := ModuleCat.{0} k) R
        (interInclLeft A B) (interInclRight A B)
        (subtypeIncl Y A) (subtypeIncl Y B) (subset_square_comm A B) =
      (coverChainsIsoSmall (C := ModuleCat.{0} k) R A B).hom ≫
        smallι R A B := by
  refine (cancel_epi (cokernel.π
      (mvIncl (C := ModuleCat.{0} k) R (interInclLeft A B)
        (interInclRight A B)))).1 ?_
  simp only [coverComparison, cokernel.π_desc]
  rw [coverToX_eq_desc_comp_smallι, ← π_comp_coverChainsIsoSmall_hom]
  exact Category.assoc
    (cokernel.π (mvIncl (C := ModuleCat.{0} k) R
      (interInclLeft A B) (interInclRight A B)))
    (coverChainsIsoSmall (C := ModuleCat.{0} k) R A B).hom
    (smallι R A B)

instance smallι_mono_f (A B : Set Y) (n : ℕ) : Mono ((smallι R A B).f n) := by
  dsimp [smallι, SSet.chainComplexMap, SSet.chainComplexFunctor]
  exact MonoCoprod.mono_map'_of_injective
    (fun _ : (TopCat.toSSet.obj (.of Y)).obj (.op (.mk n)) ↦ R)
    (fun s : (small A B).obj (.op (.mk n)) ↦ (s : _))
    Subtype.val_injective

instance smallι_mono (A B : Set Y) : Mono (smallι R A B) :=
  HomologicalComplex.mono_of_mono_f _ fun n => smallι_mono_f (R := R) A B n

lemma smallι_hom_injective (A B : Set Y) (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom ((smallι R A B).f n)) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

lemma ambient_d_apply {n : ℕ} (z : singularChainType R (.of Y) (n + 1)) :
    ModuleCat.Hom.hom
        ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj (.of Y)).d
          (n + 1) n) z =
      dApply R (.of Y) n z :=
  rfl

lemma of_mem_smallChainsSubgroup {A B : Set Y} {n : ℕ}
    {z : singularChainType R (.of Y) n}
    (hz : isSmallChain (R := R) (A := A) (B := B) z) :
    DirectSum.of (singularChainType R (.of Y)) n z ∈ smallChainsSubgroup R A B := by
  intro m
  by_cases h : m = n
  · subst h
    simpa [DirectSum.of_eq_same] using hz
  · have hm : (DirectSum.of (singularChainType R (.of Y)) n z) m = 0 :=
      DirectSum.of_eq_of_ne n m z h
    simpa [hm] using isSmallChain_zero (R := R) (A := A) (B := B) (n := m)

lemma cycle_component {n : ℕ} {z : TotalSingularChains R (.of Y)}
    (hz : (subdivisionData_singular R (.of Y)).Cycle z) :
    dApply R (.of Y) n (z (n + 1)) = 0 := by
  have h : dTotal R (.of Y) z = 0 := hz
  rw [← dTotal_apply, h]
  simp

lemma homologyπ_eq_zero_iff_boundary
    (K : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ)
    (z : K.cycles n) :
    K.homologyπ n z = 0 ↔
      ∃ x : K.X (n + 1), K.toCycles (n + 1) n x = z := by
  have hex : (ShortComplex.mk (K.toCycles (n + 1) n) (K.homologyπ n)
      (K.toCycles_comp_homologyπ (n + 1) n)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _
      (K.homologyIsCokernel (i := n + 1) (j := n) (ChainComplex.prev ℕ n))
  rw [ShortComplex.moduleCat_exact_iff] at hex
  constructor
  · exact hex z
  · rintro ⟨x, rfl⟩
    exact congrArg (fun f => f x) (K.toCycles_comp_homologyπ (n + 1) n)

lemma iCycles_apply_toCycles
    (K : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ) (x : K.X (n + 1)) :
    ModuleCat.Hom.hom (K.iCycles n) (K.toCycles (n + 1) n x) =
      ModuleCat.Hom.hom (K.d (n + 1) n) x := by
  have hcomp : K.toCycles (n + 1) n ≫ K.iCycles n = K.d (n + 1) n :=
    K.liftCycles_i (K.d (n + 1) n) ((ComplexShape.down ℕ).next n) rfl
      (K.d_comp_d _ _ _)
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hcomp]

lemma iCycles_apply_cyclesMap (A B : Set Y) (n : ℕ)
    (za : ((small A B : SSet).chainComplex R).cycles n) :
    ModuleCat.Hom.hom ((ambientChains (R := R)).iCycles n)
        (cyclesMap (smallι R A B) n za) =
      ModuleCat.Hom.hom ((smallι R A B).f n)
        (ModuleCat.Hom.hom
          (((small A B : SSet).chainComplex R).iCycles n) za) := by
  have hcomp := cyclesMap_i (smallι R A B) n
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hcomp,
    ModuleCat.hom_comp, LinearMap.comp_apply]

lemma iCycles_d_apply (K : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ)
    (z : K.cycles n) :
    ModuleCat.Hom.hom (K.d n ((ComplexShape.down ℕ).next n))
      (ModuleCat.Hom.hom (K.iCycles n) z) = 0 := by
  have hcomp := K.iCycles_d n ((ComplexShape.down ℕ).next n)
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hcomp]
  simp

lemma iCycles_hom_injective (K : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom (K.iCycles n)) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

lemma homologous_degree {z b w : TotalSingularChains R (.of Y)} {n : ℕ}
    (h : z - b = dTotal R (.of Y) w) :
    z n - b n = dApply R (.of Y) n (w (n + 1)) := by
  have hn := congrArg (fun x : TotalSingularChains R (.of Y) => x n) h
  change (z - b) n = dTotal R (.of Y) w n at hn
  rw [dTotal_apply] at hn
  exact hn

lemma cycle_of_iCycles {n : ℕ}
    (z : ((ambientChains (R := R)).cycles n)) :
    (subdivisionData_singular R (.of Y)).Cycle
      (DirectSum.of (singularChainType R (.of Y)) n
        (ModuleCat.Hom.hom ((ambientChains (R := R)).iCycles n) z)) := by
  cases n with
  | zero => exact toTotal_cycle_zero (R := R) _
  | succ n =>
      refine toTotal_cycle_succ (R := R) ?_
      have hz := iCycles_d_apply (ambientChains (R := R)) (n + 1) z
      rw [ChainComplex.next_nat_succ] at hz
      simpa [dApply] using hz

lemma small_cycle_of_iCycles {A B : Set Y} {n : ℕ}
    (z : ((small A B : SSet).chainComplex R).cycles n) :
    (subdivisionData_singular R (.of Y)).Cycle
      (DirectSum.of (singularChainType R (.of Y)) n
        (ModuleCat.Hom.hom ((smallι R A B).f n)
          (ModuleCat.Hom.hom
            (((small A B : SSet).chainComplex R).iCycles n) z))) := by
  cases n with
  | zero => exact toTotal_cycle_zero (R := R) _
  | succ n =>
      refine toTotal_cycle_succ (R := R) ?_
      have hz := iCycles_d_apply ((small A B : SSet).chainComplex R) (n + 1) z
      rw [ChainComplex.next_nat_succ] at hz
      have hcomp := (smallι R A B).comm (n + 1) n
      change ModuleCat.Hom.hom
          ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj (.of Y)).d
            (n + 1) n)
          (ModuleCat.Hom.hom ((smallι R A B).f (n + 1))
            (ModuleCat.Hom.hom
              (((small A B : SSet).chainComplex R).iCycles (n + 1)) z)) = 0
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hcomp,
        ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero]

lemma homologyMap_apply_homologyπ (A B : Set Y) (n : ℕ)
    (za : ((small A B : SSet).chainComplex R).cycles n) :
    ModuleCat.Hom.hom (homologyMap (smallι R A B) n)
        (ModuleCat.Hom.hom
          (((small A B : SSet).chainComplex R).homologyπ n) za) =
      ModuleCat.Hom.hom ((ambientChains (R := R)).homologyπ n)
        (cyclesMap (smallι R A B) n za) := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f za)
    (homologyπ_naturality (smallι R A B) (i := n))
  convert h using 1 <;> rw [ModuleCat.hom_comp, LinearMap.comp_apply]

lemma d_small_of_d_image {A B : Set Y} {n : ℕ}
    (y : ((small A B : SSet).chainComplex R).X (n + 1))
    {z : ((small A B : SSet).chainComplex R).X n}
    (h : ModuleCat.Hom.hom ((smallι R A B).f n)
          (((small A B : SSet).chainComplex R).d (n + 1) n y) =
        ModuleCat.Hom.hom ((smallι R A B).f n) z) :
    ((small A B : SSet).chainComplex R).d (n + 1) n y = z :=
  smallι_hom_injective (R := R) A B n h

lemma smallι_quasiIso {A B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : A ∪ B = univ) :
    QuasiIso (smallι R A B) := by
  refine (quasiIso_iff (smallι R A B)).2 fun n =>
    (quasiIsoAt_iff_isIso_homologyMap (smallι R A B) n).2 ?_
  refine (ConcreteCategory.isIso_iff_bijective
      (homologyMap (smallι R A B) n)).2 ⟨?inj, ?surj⟩
  · intro a b hab
    apply sub_eq_zero.mp
    set c := a - b with hcdef
    have hc : ModuleCat.Hom.hom (homologyMap (smallι R A B) n) c = 0 := by
      simp [c, hab]
    obtain ⟨za, hza⟩ := (ModuleCat.epi_iff_surjective
        (((small A B : SSet).chainComplex R).homologyπ n)).1 inferInstance c
    have hbound :
        ModuleCat.Hom.hom ((ambientChains (R := R)).homologyπ n)
          (cyclesMap (smallι R A B) n za) = 0 := by
      rw [← homologyMap_apply_homologyπ, hza, hc]
    obtain ⟨x, hx⟩ :=
      (homologyπ_eq_zero_iff_boundary (ambientChains (R := R)) n _).1 hbound
    set zsmall :=
      ModuleCat.Hom.hom
        (((small A B : SSet).chainComplex R).iCycles n) za
    set btot := DirectSum.of (singularChainType R (.of Y)) n
      (ModuleCat.Hom.hom ((smallι R A B).f n) zsmall)
    have hbmem : btot ∈ smallChainsSubgroup R A B :=
      of_mem_smallChainsSubgroup (R := R) ⟨zsmall, rfl⟩
    have hbcycle := small_cycle_of_iCycles (R := R) (A := A) (B := B) za
    have hdx :
        ModuleCat.Hom.hom ((ambientChains (R := R)).d (n + 1) n) x =
          ModuleCat.Hom.hom ((smallι R A B).f n) zsmall := by
      have h1 := iCycles_apply_toCycles (ambientChains (R := R)) n x
      have h2 := iCycles_apply_cyclesMap (R := R) A B n za
      rw [hx] at h1
      exact h1.symm.trans h2
    have hbbound : ∃ w, btot = (subdivisionData_singular R (.of Y)).d w :=
      ⟨DirectSum.of (singularChainType R (.of Y)) (n + 1) x, by
        change btot = dTotal R (.of Y)
          (DirectSum.of (singularChainType R (.of Y)) (n + 1) x)
        rw [dTotal_of_succ]
        simp [btot, dApply, hdx]⟩
    obtain ⟨ytot, hymem, hyeq⟩ :=
      (small_cycles_and_boundaries_singular (R := R) hA hB hAB).2
        btot hbmem hbcycle hbbound
    obtain ⟨ypred, hypred⟩ := hymem (n + 1)
    have hdy :
        ModuleCat.Hom.hom ((smallι R A B).f n)
            (((small A B : SSet).chainComplex R).d (n + 1) n ypred) =
          ModuleCat.Hom.hom ((smallι R A B).f n) zsmall := by
      have hb_n : btot n = ModuleCat.Hom.hom ((smallι R A B).f n) zsmall := by
        simp [btot, DirectSum.of_eq_same]
      have hdeg := congrArg (fun w : TotalSingularChains R (.of Y) => w n) hyeq
      have hytot : dApply R (.of Y) n (ytot (n + 1)) =
          ModuleCat.Hom.hom ((smallι R A B).f n) zsmall := by
        have : btot n =
            (subdivisionData_singular R (.of Y)).d ytot n := hdeg
        rw [show (subdivisionData_singular R (.of Y)).d ytot =
            dTotal R (.of Y) ytot from rfl] at this
        rw [dTotal_apply, hb_n] at this
        exact this.symm
      have hcomm := (smallι R A B).comm (n + 1) n
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← hcomm,
        ModuleCat.hom_comp, LinearMap.comp_apply]
      have hypred' :
          ModuleCat.Hom.hom ((smallι R A B).f (n + 1)) ypred = ytot (n + 1) :=
        hypred
      rw [hypred']
      exact hytot
    have hza_eq :
        za = ((small A B : SSet).chainComplex R).toCycles (n + 1) n ypred := by
      refine (iCycles_hom_injective ((small A B : SSet).chainComplex R) n) ?_
      have := d_small_of_d_image (R := R) (A := A) (B := B) ypred hdy
      rw [iCycles_apply_toCycles, this]
    rw [← hza, hza_eq]
    exact congrArg (fun f => ModuleCat.Hom.hom f ypred)
      (((small A B : SSet).chainComplex R).toCycles_comp_homologyπ (n + 1) n)
  · intro h
    obtain ⟨zcyc, hzcyc⟩ := (ModuleCat.epi_iff_surjective
        ((ambientChains (R := R)).homologyπ n)).1 inferInstance h
    set z := ModuleCat.Hom.hom ((ambientChains (R := R)).iCycles n) zcyc
    have hzcycle := cycle_of_iCycles (R := R) zcyc
    obtain ⟨btot, hbmem, hbcycle, hhom⟩ :=
      (small_cycles_and_boundaries_singular (R := R) hA hB hAB).1 _ hzcycle
    obtain ⟨w, hw⟩ := hhom
    obtain ⟨yb, hyb⟩ := hbmem n
    have hycycle :
        ModuleCat.Hom.hom
          (((small A B : SSet).chainComplex R).d n
            ((ComplexShape.down ℕ).next n)) yb = 0 := by
      refine smallι_hom_injective (R := R) A B
          ((ComplexShape.down ℕ).next n) ?_
      rw [map_zero]
      cases n with
      | zero =>
          rw [ChainComplex.next_nat_zero]
          have hcomm := (smallι R A B).comm 0 0
          rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← hcomm,
            ModuleCat.hom_comp, LinearMap.comp_apply]
          simp
      | succ m =>
          rw [ChainComplex.next_nat_succ]
          have hcomm := (smallι R A B).comm (m + 1) m
          rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← hcomm,
            ModuleCat.hom_comp, LinearMap.comp_apply]
          have hyb' :
              ModuleCat.Hom.hom ((smallι R A B).f (m + 1)) yb = btot (m + 1) :=
            hyb
          rw [hyb']
          exact cycle_component (R := R) (n := m) hbcycle
    let ycyc := ((small A B : SSet).chainComplex R).cyclesMk
      (x := yb) (j := (ComplexShape.down ℕ).next n) (hj := rfl)
      (hx := by
        change (forget₂ (ModuleCat.{0} k) Ab).map _ yb = 0
        simpa using hycycle)
    refine ⟨((small A B : SSet).chainComplex R).homologyπ n ycyc, ?_⟩
    rw [← hzcyc, homologyMap_apply_homologyπ]
    have hiycyc :
        ModuleCat.Hom.hom ((ambientChains (R := R)).iCycles n)
            (cyclesMap (smallι R A B) n ycyc) =
          ModuleCat.Hom.hom ((smallι R A B).f n) yb := by
      have hmap := iCycles_apply_cyclesMap (R := R) A B n ycyc
      have hy : ModuleCat.Hom.hom
          (((small A B : SSet).chainComplex R).iCycles n) ycyc = yb := by
        simpa using i_cyclesMk ((small A B : SSet).chainComplex R) yb
          ((ComplexShape.down ℕ).next n) rfl (by
            change (forget₂ (ModuleCat.{0} k) Ab).map _ yb = 0
            simpa using hycycle)
      rw [hmap, hy]
    have hex :
        (ambientChains (R := R)).toCycles (n + 1) n (w (n + 1)) =
          zcyc - cyclesMap (smallι R A B) n ycyc := by
      refine (iCycles_hom_injective (ambientChains (R := R)) n) ?_
      have hdeg := homologous_degree (R := R) (n := n) hw
      rw [iCycles_apply_toCycles, map_sub, hiycyc]
      have hyb' : ModuleCat.Hom.hom ((smallι R A B).f n) yb = btot n := hyb
      rw [hyb']
      simpa [z, DirectSum.of_eq_same, dApply] using hdeg.symm
    have hπ0 :
        (ambientChains (R := R)).homologyπ n
          ((ambientChains (R := R)).toCycles (n + 1) n (w (n + 1))) = 0 :=
      (homologyπ_eq_zero_iff_boundary (ambientChains (R := R)) n _).2
        ⟨w (n + 1), rfl⟩
    have hzero :
        (ambientChains (R := R)).homologyπ n
          (zcyc - cyclesMap (smallι R A B) n ycyc) = 0 := by
      rw [← hex]
      exact hπ0
    rw [map_sub] at hzero
    exact (eq_of_sub_eq_zero hzero).symm

lemma IsExcisiveSubspaces_of_openCover {A B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : A ∪ B = univ) :
    IsExcisiveSubspaces (C := ModuleCat.{0} k) R A B := by
  dsimp [IsExcisiveSubspaces, IsExcisive]
  rw [coverComparison_eq_iso_comp_smallι]
  haveI : QuasiIso (smallι R A B) := smallι_quasiIso (R := R) hA hB hAB
  infer_instance

lemma IsExcisiveSubspaces_puncturedSphere (n : ℕ) :
    IsExcisiveSubspaces (C := ModuleCat.{0} k) R
      (puncturedNorth n) (puncturedSouth n) :=
  IsExcisiveSubspaces_of_openCover (R := R)
    (isOpen_puncturedNorth n) (isOpen_puncturedSouth n) (punctured_cover n)

end

end SingularExcision
