/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import PlatonicSolids.Incidence
import PlatonicSolids.SingularExcision.OpenCoverQI

/-!
Singular `H_n(S^n) ≅ R` for `n > 0` from the stereographic
Mayer-Vietoris cover, after the open-cover quasi-isomorphism. The
intersection of the charts is homotopy-equivalent to `S^{n-1}`; the
connecting map is an isomorphism in positive degrees; `H_1(S^1)` is
identified with `ker epsilon` of the two-point space. The optional Euler
bridge `platonic_solids_3d_of_sphere` takes numeric Betti numbers
`1, 0, 1`, which agree with singular `H_*(S^2)`, and does not change
Palomar compared types.
-/

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Metric Set ContinuousMap
open scoped Topology InnerProductSpace

set_option linter.unusedSectionVars false

variable {k : Type} [Ring k] (R : ModuleCat.{0} k)
variable [HasCoproducts.{0} (ModuleCat.{0} k)]
variable [HasPullbacks (ModuleCat.{0} k)]

noncomputable section

/-! ## Stereographic intersection homotopy-equivalent to a sphere -/

lemma southPole_eq_neg_northPole (n : ℕ) :
    (southPole n : EuclideanSpace ℝ (Fin (n + 1))) =
      (-1 : ℝ) • (northPole n : EuclideanSpace ℝ (Fin (n + 1))) := by
  simp [southPole, northPole]

lemma stereoToFun_north_south (n : ℕ) :
    stereoToFun (northPole n : EuclideanSpace ℝ (Fin (n + 1)))
      (southPole n : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
  have hz :
      ((ℝ ∙ (northPole n : EuclideanSpace ℝ (Fin (n + 1)))).orthogonal).orthogonalProjection
        (southPole n : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
    rw [southPole_eq_neg_northPole, map_smul,
      Submodule.orthogonalProjection_orthogonalComplement_singleton_eq_zero]
    simp
  rw [stereoToFun_apply, hz, smul_zero]

lemma homeoPuncturedNorth_apply (n : ℕ) (x : ↥(puncturedNorth n)) :
    homeoPuncturedNorth n x =
      stereoToFun (northPole n : EuclideanSpace ℝ (Fin (n + 1))) (x : _) := by
  apply Subtype.ext
  dsimp [homeoPuncturedNorth]
  rfl

lemma homeoPuncturedNorth_south (n : ℕ) :
    homeoPuncturedNorth n ⟨southPole n, by
      simpa [puncturedNorth] using (northPole_ne_southPole n).symm⟩ = 0 := by
  rw [homeoPuncturedNorth_apply, stereoToFun_north_south]

lemma homeoPuncturedNorth_symm_zero (n : ℕ) :
    (homeoPuncturedNorth n).symm 0 =
      ⟨southPole n, by simpa [puncturedNorth] using (northPole_ne_southPole n).symm⟩ := by
  apply (homeoPuncturedNorth n).injective
  simp [homeoPuncturedNorth_south]

lemma homeoPuncturedNorth_eq_zero_iff (n : ℕ) (x : ↥(puncturedNorth n)) :
    homeoPuncturedNorth n x = 0 ↔ (x : MetricSphere n) = southPole n := by
  constructor
  · intro hx
    have hx' : x = (homeoPuncturedNorth n).symm 0 := by
      rw [← hx, Homeomorph.symm_apply_apply]
    rw [hx', homeoPuncturedNorth_symm_zero]
  · rintro h
    have hx : x = ⟨southPole n, by
        simpa [puncturedNorth] using (northPole_ne_southPole n).symm⟩ :=
      Subtype.ext h
    rw [hx, homeoPuncturedNorth_south]

/-- Stereographic projection from the north pole identifies `U ∩ V` with
the punctured hyperplane. -/
def homeoPuncturedInter (n : ℕ) :
    ↥(puncturedNorth n ∩ puncturedSouth n) ≃ₜ
      ({0}ᶜ : Set ((ℝ ∙ (northPole n : EuclideanSpace ℝ (Fin (n + 1)))).orthogonal)) where
  toFun p :=
    ⟨homeoPuncturedNorth n ⟨p.1, p.2.1⟩,
      mt (homeoPuncturedNorth_eq_zero_iff n ⟨p.1, p.2.1⟩).1 p.2.2⟩
  invFun w :=
    ⟨(homeoPuncturedNorth n).symm w.1, by
      refine ⟨((homeoPuncturedNorth n).symm w.1).2, ?_⟩
      exact mt (homeoPuncturedNorth_eq_zero_iff n ((homeoPuncturedNorth n).symm w.1)).2
        (by rw [(homeoPuncturedNorth n).apply_symm_apply]; exact w.2)⟩
  left_inv p := by
    ext
    simp
  right_inv w := by
    ext
    simp
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact (homeoPuncturedNorth n).continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _)
  continuous_invFun := by
    rw [continuous_induced_rng]
    convert (continuous_subtype_val.comp
      ((homeoPuncturedNorth n).symm.continuous.comp continuous_subtype_val)) using 1

instance contractibleSpace_Ioi_zero : ContractibleSpace (Ioi (0 : ℝ)) :=
  (convex_Ioi (0 : ℝ)).contractibleSpace nonempty_Ioi

/-- A product with a contractible space is homotopy-equivalent to the first factor. -/
def homotopyEquiv_prod_contractible
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace Y] :
    (X × Y) ≃ₕ X :=
  (ContinuousMap.HomotopyEquiv.prodCongr (ContinuousMap.HomotopyEquiv.refl X)
      (Classical.choice (ContractibleSpace.hequiv_unit Y))).trans
    (Homeomorph.prodUnique X Unit).toHomotopyEquiv

/-- Polar coordinates: the punctured hyperplane is homotopy-equivalent to
its unit sphere. -/
def homotopyEquiv_puncturedHyperplane_sphere (n : ℕ) :
    ({0}ᶜ : Set ((ℝ ∙ (northPole n : EuclideanSpace ℝ (Fin (n + 1)))).orthogonal)) ≃ₕ
      ↥(sphere (0 : ((ℝ ∙ (northPole n : EuclideanSpace ℝ (Fin (n + 1)))).orthogonal)) 1) :=
  (homeomorphUnitSphereProd
      ((ℝ ∙ (northPole n : EuclideanSpace ℝ (Fin (n + 1)))).orthogonal)).toHomotopyEquiv.trans
    homotopyEquiv_prod_contractible

/-- The unit sphere in the polar hyperplane of `S^{n+1}` is homeomorphic to `S^n`. -/
def homeoHyperplaneSphere (n : ℕ) :
    ↥(sphere (0 : ((ℝ ∙ (northPole (n + 1) : EuclideanSpace ℝ (Fin (n + 2)))).orthogonal)) 1) ≃ₜ
      MetricSphere n :=
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = n + 1 + 1) :=
    ⟨by simp⟩
  have hv : (northPole (n + 1) : EuclideanSpace ℝ (Fin (n + 2))) ≠ 0 := by
    simp [northPole]
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (n + 1) hv
  have himg : b.repr.toHomeomorph '' sphere 0 1 =
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    rw [LinearIsometryEquiv.coe_toHomeomorph, LinearIsometryEquiv.image_sphere]
    simp
  (b.repr.toHomeomorph.image (sphere 0 1)).trans (Homeomorph.setCongr himg)

/-- The stereographic intersection of `S^{n+1}` is homotopy-equivalent to `S^n`. -/
def homotopyEquiv_puncturedInter_sphere (n : ℕ) :
    ↥(puncturedNorth (n + 1) ∩ puncturedSouth (n + 1)) ≃ₕ MetricSphere n :=
  (homeoPuncturedInter (n + 1)).toHomotopyEquiv.trans
    ((homotopyEquiv_puncturedHyperplane_sphere (n + 1)).trans
      (homeoHyperplaneSphere n).toHomotopyEquiv)

/-! ## Mayer–Vietoris connecting map, hex discharged -/

/-- Connecting map of the stereographic cover, with excision supplied by
the open-cover quasi-isomorphism. -/
def singularHomology_sphere_mayerVietorisδ (n : ℕ) :
    (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
        (.of (MetricSphere (n + 1)))).homology (n + 1) ⟶
      (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
        (.of ↥(puncturedNorth (n + 1) ∩ puncturedSouth (n + 1)))).homology n :=
  mayerVietorisδ (C := ModuleCat.{0} k) R
    (interInclLeft (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
    (interInclRight (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
    (subtypeIncl (MetricSphere (n + 1)) (puncturedNorth (n + 1)))
    (subtypeIncl (MetricSphere (n + 1)) (puncturedSouth (n + 1)))
    (subset_square_comm _ _)
    (SingularExcision.IsExcisiveSubspaces_puncturedSphere (R := R) (n + 1)) n

lemma isZero_homology_chainBiprod
    {U V : TopCat.{0}} {n : ℕ}
    (hU : IsZero (((singularHomologyFunctor (ModuleCat.{0} k) n).obj R).obj U))
    (hV : IsZero (((singularHomologyFunctor (ModuleCat.{0} k) n).obj R).obj V)) :
    IsZero (((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj U ⊞
        ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj V)).homology n) := by
  let KU := ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj U
  let KV := ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj V
  change IsZero ((KU ⊞ KV).homology n)
  rw [IsZero.iff_id_eq_zero, ← homologyMap_id (KU ⊞ KV) n, ← biprod.total]
  rw [homologyMap_add, homologyMap_comp, homologyMap_comp]
  have hf : homologyMap (biprod.fst : KU ⊞ KV ⟶ KU) n = 0 := hU.eq_of_tgt _ _
  have hs : homologyMap (biprod.snd : KU ⊞ KV ⟶ KV) n = 0 := hV.eq_of_tgt _ _
  simp [hf, hs]

lemma isZero_homology_chartSum (n m : ℕ) (hm : m ≠ 0) :
    IsZero (((((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
          (.of ↥(puncturedNorth n)) ⊞
        ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
          (.of ↥(puncturedSouth n)))).homology m) :=
  isZero_homology_chainBiprod (R := R)
    (isZero_singularHomology_puncturedNorth (C := ModuleCat.{0} k) R n hm)
    (isZero_singularHomology_puncturedSouth (C := ModuleCat.{0} k) R n hm)

lemma triadδ_sphere_isIso {n : ℕ} (hn : 0 < n) :
    IsIso (triadδ (C := ModuleCat.{0} k) R
      (interInclLeft (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
      (interInclRight (puncturedNorth (n + 1)) (puncturedSouth (n + 1))) n) :=
  (triad_shortExact (C := ModuleCat.{0} k) R
      (interInclLeft (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
      (interInclRight (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))).isIso_δ
    (n + 1) n (by simp)
    (isZero_homology_chartSum (R := R) (n + 1) (n + 1) (Nat.succ_ne_zero n))
    (isZero_homology_chartSum (R := R) (n + 1) n hn.ne')

lemma singularHomology_sphere_mayerVietorisδ_isIso {n : ℕ} (hn : 0 < n) :
    IsIso (singularHomology_sphere_mayerVietorisδ (R := R) n) := by
  dsimp [singularHomology_sphere_mayerVietorisδ, mayerVietorisδ]
  haveI := triadδ_sphere_isIso (R := R) hn
  infer_instance

/-- In positive degrees the stereographic connecting map identifies
`H_{n+1}(S^{n+1})` with `H_n` of the chart intersection. -/
def singularHomology_sphere_mayerVietorisδ_iso {n : ℕ} (hn : 0 < n) :
    (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
        (.of (MetricSphere (n + 1)))).homology (n + 1) ≅
      (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
        (.of ↥(puncturedNorth (n + 1) ∩ puncturedSouth (n + 1)))).homology n :=
  haveI := singularHomology_sphere_mayerVietorisδ_isIso (R := R) hn
  asIso (singularHomology_sphere_mayerVietorisδ (R := R) n)

/-- For `n ≥ 1`, `H_{n+1}(S^{n+1})` is isomorphic to `H_n(S^n)`. -/
def singularHomology_sphere_succ_iso {n : ℕ} (hn : 0 < n) :
    (((singularHomologyFunctor (ModuleCat.{0} k) (n + 1)).obj R).obj
        (.of (MetricSphere (n + 1)))) ≅
      (((singularHomologyFunctor (ModuleCat.{0} k) n).obj R).obj
        (.of (MetricSphere n))) :=
  (singularHomology_sphere_mayerVietorisδ_iso (R := R) hn).trans
    (singularHomologyIso_of_homotopyEquiv
      (homotopyEquiv_puncturedInter_sphere n) R n)

/-- Iterated connecting isomorphism: for `n ≥ 1`,
`H_{n+j}(S^{n+j})` is isomorphic to `H_n(S^n)`. -/
def singularHomology_sphere_iterate_iso
    {n : ℕ} (hn : 0 < n) : (j : ℕ) →
    (((singularHomologyFunctor (ModuleCat.{0} k) (n + j)).obj R).obj
        (.of (MetricSphere (n + j)))) ≅
      (((singularHomologyFunctor (ModuleCat.{0} k) n).obj R).obj
        (.of (MetricSphere n)))
  | 0 => Iso.refl _
  | j + 1 =>
    (singularHomology_sphere_succ_iso (R := R) (n := n + j) (by omega)).trans
      (singularHomology_sphere_iterate_iso hn j)

/-! ## `H_*(S^n)` in all degrees -/

/-- Connecting map of the stereographic cover of `S^{n+1}` in any degree. -/
def singularHomology_sphere_mayerVietorisδ_deg (n m : ℕ) :
    (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
        (.of (MetricSphere (n + 1)))).homology (m + 1) ⟶
      (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
        (.of ↥(puncturedNorth (n + 1) ∩ puncturedSouth (n + 1)))).homology m :=
  mayerVietorisδ (C := ModuleCat.{0} k) R
    (interInclLeft (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
    (interInclRight (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
    (subtypeIncl (MetricSphere (n + 1)) (puncturedNorth (n + 1)))
    (subtypeIncl (MetricSphere (n + 1)) (puncturedSouth (n + 1)))
    (subset_square_comm _ _)
    (SingularExcision.IsExcisiveSubspaces_puncturedSphere (R := R) (n + 1)) m

lemma triadδ_sphere_isIso_of_pos (n m : ℕ) (hm : 0 < m) :
    IsIso (triadδ (C := ModuleCat.{0} k) R
      (interInclLeft (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
      (interInclRight (puncturedNorth (n + 1)) (puncturedSouth (n + 1))) m) :=
  (triad_shortExact (C := ModuleCat.{0} k) R
      (interInclLeft (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
      (interInclRight (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))).isIso_δ
    (m + 1) m (by simp)
    (isZero_homology_chartSum (R := R) (n + 1) (m + 1) (Nat.succ_ne_zero m))
    (isZero_homology_chartSum (R := R) (n + 1) m hm.ne')

lemma singularHomology_sphere_mayerVietorisδ_deg_isIso
    (n : ℕ) {m : ℕ} (hm : 0 < m) :
    IsIso (singularHomology_sphere_mayerVietorisδ_deg (R := R) n m) := by
  dsimp [singularHomology_sphere_mayerVietorisδ_deg, mayerVietorisδ]
  haveI := triadδ_sphere_isIso_of_pos (R := R) n m hm
  infer_instance

/-- For `m ≥ 1`, `H_{m+1}(S^{n+1})` is isomorphic to `H_m(S^n)`. -/
def singularHomology_sphere_succ_iso_of_pos {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{0} k) (m + 1)).obj R).obj
        (.of (MetricSphere (n + 1)))) ≅
      (((singularHomologyFunctor (ModuleCat.{0} k) m).obj R).obj
        (.of (MetricSphere n))) :=
  haveI := singularHomology_sphere_mayerVietorisδ_deg_isIso (R := R) n hm
  (asIso (singularHomology_sphere_mayerVietorisδ_deg (R := R) n m)).trans
    (singularHomologyIso_of_homotopyEquiv
      (homotopyEquiv_puncturedInter_sphere n) R m)

/-- The 0-sphere in `EuclideanSpace ℝ (Fin 1)` is homeomorphic to `{±1} ⊂ ℝ`. -/
def homeoMetricSphere0 :
    MetricSphere 0 ≃ₜ ↥(Metric.sphere (0 : ℝ) 1) :=
  let e : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
    (PiLp.homeomorph 2 fun _ : Fin 1 ↦ ℝ).trans (Homeomorph.funUnique (Fin 1) ℝ)
  have himg : e '' sphere 0 1 = sphere (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy1 : ‖y‖ = 1 := by simpa [mem_sphere_iff_norm] using hy
      have : |e y| = ‖y‖ := by
        simp [e, EuclideanSpace.norm_eq, Real.norm_eq_abs, Finset.univ_unique,
          Fin.default_eq_zero, Real.sqrt_sq_eq_abs, PiLp.homeomorph]
      simpa [mem_sphere_iff_norm, Real.norm_eq_abs, this] using hy1
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      have hx1 : |x| = 1 := by simpa [mem_sphere_iff_norm, Real.norm_eq_abs] using hx
      have : ‖e.symm x‖ = |x| := by
        simp [e, EuclideanSpace.norm_eq, Real.norm_eq_abs, Finset.univ_unique,
          Fin.default_eq_zero, Real.sqrt_sq_eq_abs, PiLp.homeomorph]
      simpa [mem_sphere_iff_norm, this] using hx1
  (e.image (sphere 0 1)).trans (Homeomorph.setCongr himg)

lemma isZero_singularHomology_metricSphere0 {m : ℕ} (hm : m ≠ 0) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} k) m).obj R).obj
      (.of (MetricSphere 0))) :=
  (isZero_singularHomology_sphere0 (C := ModuleCat.{0} k) R hm).of_iso
    (singularHomologyIso_of_homeomorph (homeoMetricSphere0) R m)

/-- `H_m(S^1) = 0` for `m ≥ 2`. -/
lemma isZero_singularHomology_sphere1_of_ge_two {m : ℕ} (hm : 2 ≤ m) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} k) m).obj R).obj
      (.of (MetricSphere 1))) := by
  have hm0 : 0 < m - 1 := Nat.sub_pos_of_lt hm
  convert (isZero_singularHomology_metricSphere0 (R := R) hm0.ne').of_iso
    (singularHomology_sphere_succ_iso_of_pos (R := R) hm0 0)
  exact (Nat.sub_add_cancel (Nat.le_trans (by norm_num : 1 ≤ 2) hm)).symm

lemma triadδ_sphere_mono_zero (n : ℕ) :
    Mono (triadδ (C := ModuleCat.{0} k) R
      (interInclLeft (puncturedNorth n) (puncturedSouth n))
      (interInclRight (puncturedNorth n) (puncturedSouth n)) 0) :=
  (triad_shortExact (C := ModuleCat.{0} k) R
      (interInclLeft (puncturedNorth n) (puncturedSouth n))
      (interInclRight (puncturedNorth n) (puncturedSouth n))).mono_δ
    1 0 (by simp) (isZero_homology_chartSum (R := R) n 1 one_ne_zero)

instance pathConnectedSpace_puncturedInter {n : ℕ} [NeZero n] :
    PathConnectedSpace ↥(puncturedNorth (n + 1) ∩ puncturedSouth (n + 1)) :=
  pathConnectedSpace_of_homotopyEquiv (homotopyEquiv_puncturedInter_sphere n)

lemma homologyMap_mvIncl_zero_mono
    {n : ℕ} [NeZero n] :
    Mono (homologyMap
      (mvIncl (C := ModuleCat.{0} k) R
        (interInclLeft (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
        (interInclRight (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))) 0) := by
  have : IsIso (homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
        (interInclLeft (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))) 0) :=
    inferInstance
  have hfst :
      homologyMap
          (mvIncl (C := ModuleCat.{0} k) R
            (interInclLeft (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
            (interInclRight (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))) 0 ≫
        homologyMap
          (biprod.fst :
            ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
                (.of ↥(puncturedNorth (n + 1))) ⊞
              ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
                (.of ↥(puncturedSouth (n + 1))) ⟶
              ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
                (.of ↥(puncturedNorth (n + 1)))) 0 =
        homologyMap
          (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
            (interInclLeft (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))) 0 := by
    rw [← homologyMap_comp]
    congr 1
    exact biprod.lift_fst _ _
  exact mono_of_mono_fac hfst

/-- `H_1(S^n) = 0` for `n ≥ 2`. -/
lemma isZero_singularHomology_sphere_one {n : ℕ} (hn : 2 ≤ n) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} k) 1).obj R).obj
      (.of (MetricSphere n))) := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  haveI : NeZero (n - 1) := ⟨by omega⟩
  haveI : PathConnectedSpace ↥(puncturedNorth n ∩ puncturedSouth n) := by
    rw [show n = n - 1 + 1 from hn1.symm]
    infer_instance
  have hmonoι : Mono (homologyMap
      (mvIncl (C := ModuleCat.{0} k) R
        (interInclLeft (puncturedNorth n) (puncturedSouth n))
        (interInclRight (puncturedNorth n) (puncturedSouth n))) 0) := by
    have hfst :
        homologyMap
            (mvIncl (C := ModuleCat.{0} k) R
              (interInclLeft (puncturedNorth n) (puncturedSouth n))
              (interInclRight (puncturedNorth n) (puncturedSouth n))) 0 ≫
          homologyMap
            (biprod.fst :
              ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
                  (.of ↥(puncturedNorth n)) ⊞
                ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
                  (.of ↥(puncturedSouth n)) ⟶
                ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
                  (.of ↥(puncturedNorth n))) 0 =
          homologyMap
            (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
              (interInclLeft (puncturedNorth n) (puncturedSouth n))) 0 := by
      rw [← homologyMap_comp]
      congr 1
      exact biprod.lift_fst _ _
    exact mono_of_mono_fac hfst
  have hz := (triad_shortExact (C := ModuleCat.{0} k) R
      (interInclLeft (puncturedNorth n) (puncturedSouth n))
      (interInclRight (puncturedNorth n) (puncturedSouth n))).δ_comp
    1 0 (by simp)
  have hδ0 : triadδ (C := ModuleCat.{0} k) R
      (interInclLeft (puncturedNorth n) (puncturedSouth n))
      (interInclRight (puncturedNorth n) (puncturedSouth n)) 0 = 0 := by
    refine (cancel_mono (homologyMap
        (mvIncl (C := ModuleCat.{0} k) R
          (interInclLeft (puncturedNorth n) (puncturedSouth n))
          (interInclRight (puncturedNorth n) (puncturedSouth n))) 0)).1 ?_
    erw [hz]
    exact (Limits.zero_comp (f := homologyMap
        (mvIncl (C := ModuleCat.{0} k) R
          (interInclLeft (puncturedNorth n) (puncturedSouth n))
          (interInclRight (puncturedNorth n) (puncturedSouth n))) 0)).symm
  haveI := triadδ_sphere_mono_zero (R := R) n
  refine IsZero.of_iso ?_
    (excisiveHomologyIso (C := ModuleCat.{0} k) R
      (interInclLeft (puncturedNorth n) (puncturedSouth n))
      (interInclRight (puncturedNorth n) (puncturedSouth n))
      (subtypeIncl (MetricSphere n) (puncturedNorth n))
      (subtypeIncl (MetricSphere n) (puncturedSouth n))
      (subset_square_comm _ _)
      (SingularExcision.IsExcisiveSubspaces_puncturedSphere (R := R) n) 1).symm
  rw [IsZero.iff_id_eq_zero]
  refine (cancel_mono (triadδ (C := ModuleCat.{0} k) R
      (interInclLeft (puncturedNorth n) (puncturedSouth n))
      (interInclRight (puncturedNorth n) (puncturedSouth n)) 0)).1 ?_
  rw [hδ0]
  simp

/-- Drop one dimension: `H_a(S^b) ≅ H_{a-1}(S^{b-1})` when `a ≥ 2` and `b ≥ 1`. -/
def singularHomology_sphere_down_iso
    {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) :
    (((singularHomologyFunctor (ModuleCat.{0} k) a).obj R).obj
        (.of (MetricSphere b))) ≅
      (((singularHomologyFunctor (ModuleCat.{0} k) (a - 1)).obj R).obj
        (.of (MetricSphere (b - 1)))) :=
  by
    have hm : 0 < a - 1 := Nat.sub_pos_of_lt ha
    have ha' : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
    have hb' : b - 1 + 1 = b := Nat.sub_add_cancel hb
    have type_eq :
        (((singularHomologyFunctor (ModuleCat.{0} k) a).obj R).obj
            (.of (MetricSphere b))) =
          (((singularHomologyFunctor (ModuleCat.{0} k) (a - 1 + 1)).obj R).obj
            (.of (MetricSphere (b - 1 + 1)))) := by
      rw [ha', hb']
    exact (eqToIso type_eq).trans
      (singularHomology_sphere_succ_iso_of_pos (R := R) hm (b - 1))

/-- For `n ≥ 1`, `H_n(S^n)` is isomorphic to `H_1(S^1)`. -/
def singularHomology_sphere_iso_sphere1 {n : ℕ} (hn : 0 < n) :
    (((singularHomologyFunctor (ModuleCat.{0} k) n).obj R).obj
        (.of (MetricSphere n))) ≅
      (((singularHomologyFunctor (ModuleCat.{0} k) 1).obj R).obj
        (.of (MetricSphere 1))) :=
  by
    have hn' : 1 + (n - 1) = n := Nat.add_sub_cancel' hn
    have type_eq :
        (((singularHomologyFunctor (ModuleCat.{0} k) n).obj R).obj
            (.of (MetricSphere n))) =
          (((singularHomologyFunctor (ModuleCat.{0} k) (1 + (n - 1))).obj R).obj
            (.of (MetricSphere (1 + (n - 1))))) := by
      rw [hn']
    exact (eqToIso type_eq).trans
      (singularHomology_sphere_iterate_iso (R := R) (n := 1)
        (by norm_num : 0 < 1) (n - 1))

/-- Positive-degree singular homology of `S^n` vanishes off the top degree. -/
lemma isZero_singularHomology_sphere
    {n m : ℕ} (hn : 0 < n) (hm : m ≠ 0) (hne : m ≠ n) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} k) m).obj R).obj
      (.of (MetricSphere n))) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `0 < m < n`: induct on `n`, reducing to `H_1` of a sphere of dimension ≥ 2.
    induction n generalizing m with
    | zero => exact (hn.ne rfl).elim
    | succ n ih =>
      have hn0 : n ≠ 0 := by omega
      cases m with
      | zero => exact (hm rfl).elim
      | succ m =>
        cases m with
        | zero =>
          exact isZero_singularHomology_sphere_one (R := R) (by omega)
        | succ m =>
          refine (ih (m := m + 1) (by omega) (by omega) (by omega)
              (by omega)).of_iso
            (singularHomology_sphere_down_iso (R := R) (a := m + 2) (b := n + 1)
              (by omega) (by omega))
  · -- `m > n ≥ 1`: induct on `n`, reducing to `H_*(S^1)` with degree ≥ 2.
    induction n generalizing m with
    | zero => exact (hn.ne rfl).elim
    | succ n ih =>
      by_cases hn0 : n = 0
      · subst hn0
        exact isZero_singularHomology_sphere1_of_ge_two (R := R) (by omega)
      · refine (ih (m := m - 1) (by omega) (by omega) (by omega)
            (by omega)).of_iso
          (singularHomology_sphere_down_iso (R := R) (a := m) (b := n + 1)
            (by omega) (by omega))

/-! ## `H_1(S^1) ≅ R` and the full calculation of `H_*(S^n)` -/

instance preservesBinaryBiproduct_homologyFunctor (n : ℕ)
    (K L : ChainComplex (ModuleCat.{0} k) ℕ) :
    PreservesBinaryBiproduct K L
      (homologyFunctor (ModuleCat.{0} k) (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproduct_of_preservesBiproduct _ K L

lemma homologyMap_mvIncl
    {W U V : TopCat.{0}} (iU : W ⟶ U) (iV : W ⟶ V) (n : ℕ) :
    homologyMap (mvIncl (C := ModuleCat.{0} k) R iU iV) n ≫
      ((homologyFunctor (ModuleCat.{0} k) (ComplexShape.down ℕ) n).mapBiprod
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj U)
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj V)).hom =
      biprod.lift
        (homologyMap (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map iU) n)
        (-homologyMap (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map iV) n) := by
  let F := homologyFunctor (ModuleCat.{0} k) (ComplexShape.down ℕ) n
  let KU := ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj U
  let KV := ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj V
  have h := biprod.map_lift_mapBiprod (F := F) (X := KU) (Y := KV)
    (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map iU)
    (-(((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map iV))
  simpa [mvIncl, homologyMap_neg] using h

lemma biprod_lift_id_neg_id_mono (X : ModuleCat.{0} k) :
    Mono (biprod.lift (𝟙 X) (-𝟙 X)) :=
  mono_of_mono_fac (biprod.lift_fst (𝟙 X) (-𝟙 X))

lemma biprod_lift_comp_map {W X Y X' Y' : ModuleCat.{0} k}
    (f : W ⟶ X) (g : W ⟶ Y) (a : X ⟶ X') (b : Y ⟶ Y') :
    biprod.lift f g ≫ biprod.map a b = biprod.lift (f ≫ a) (g ≫ b) := by
  refine biprod.hom_ext _ _ ?_ ?_
  · simp
  · simp

lemma biprod_comp_lift {W' W X Y : ModuleCat.{0} k}
    (h : W' ⟶ W) (f : W ⟶ X) (g : W ⟶ Y) :
    h ≫ biprod.lift f g = biprod.lift (h ≫ f) (h ≫ g) := by
  refine biprod.hom_ext _ _ ?_ ?_
  · simp
  · simp

lemma homologyMap_mvIncl_comp_aug
    {W U V : TopCat.{0}} [PathConnectedSpace U] [PathConnectedSpace V]
    (iU : W ⟶ U) (iV : W ⟶ V) :
    homologyMap (mvIncl (C := ModuleCat.{0} k) R iU iV) 0 ≫
      ((homologyFunctor (ModuleCat.{0} k) (ComplexShape.down ℕ) 0).mapBiprod
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj U)
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj V)).hom ≫
      biprod.map (U.singularHomology₀ε R) (V.singularHomology₀ε R) =
    W.singularHomology₀ε R ≫ biprod.lift (𝟙 R) (-𝟙 R) := by
  have hmv := homologyMap_mvIncl (R := R) iU iV 0
  have hU := singularHomology₀ε_natural iU R
  have hV := singularHomology₀ε_natural iV R
  have hneg :
      (-homologyMap (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map iV) 0) ≫
        V.singularHomology₀ε R =
      -W.singularHomology₀ε R := by
    rw [Preadditive.neg_comp, hV]; rfl
  calc
    homologyMap (mvIncl (C := ModuleCat.{0} k) R iU iV) 0 ≫
        ((homologyFunctor (ModuleCat.{0} k) (ComplexShape.down ℕ) 0).mapBiprod
          (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj U)
          (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj V)).hom ≫
        biprod.map (U.singularHomology₀ε R) (V.singularHomology₀ε R) =
      biprod.lift
          (homologyMap (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map iU) 0)
          (-homologyMap (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map iV) 0) ≫
        biprod.map (U.singularHomology₀ε R) (V.singularHomology₀ε R) := by
      rw [← Category.assoc, hmv]; rfl
    _ = biprod.lift (W.singularHomology₀ε R) (-W.singularHomology₀ε R) := by
      rw [biprod_lift_comp_map, hU, hneg]; rfl
    _ = W.singularHomology₀ε R ≫ biprod.lift (𝟙 R) (-𝟙 R) := by
      rw [biprod_comp_lift, Category.comp_id, Preadditive.comp_neg, Category.comp_id]

/-- Connecting map of the triad is a kernel of `mvIncl_*` when it is mono. -/
noncomputable def triadδ_isoKernel
    {W U V : TopCat.{0}} (iU : W ⟶ U) (iV : W ⟶ V) [Mono iU]
    [Mono (triadδ (C := ModuleCat.{0} k) R iU iV 0)] :
    (coverChains (C := ModuleCat.{0} k) R iU iV).homology 1 ≅
      kernel (homologyMap (mvIncl (C := ModuleCat.{0} k) R iU iV) 0) :=
  (limit.isoLimitCone
    ⟨KernelFork.ofι
        (triadδ (C := ModuleCat.{0} k) R iU iV 0)
        (by
          have h := (triad_shortExact (C := ModuleCat.{0} k) R iU iV).δ_comp
            1 0 (by simp)
          exact h),
      (triad_exact_at_W (C := ModuleCat.{0} k) R iU iV 0).fIsKernel⟩).symm

def sphere0_pos : ↥(Metric.sphere (0 : ℝ) 1) :=
  ⟨1, by simp [mem_sphere_iff_norm]⟩

def sphere0_neg : ↥(Metric.sphere (0 : ℝ) 1) :=
  ⟨-1, by simp [mem_sphere_iff_norm]⟩

lemma sphere0_eq_pos_or_neg (x : ↥(Metric.sphere (0 : ℝ) 1)) :
    x = sphere0_pos ∨ x = sphere0_neg := by
  have hx : |(x : ℝ)| = 1 := by
    have hmem := x.2
    rw [mem_sphere_iff_norm, Real.norm_eq_abs, sub_zero] at hmem
    exact hmem
  rcases (abs_eq (show (0 : ℝ) ≤ 1 from by norm_num)).mp hx with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

lemma not_joined_sphere0_pos_neg :
    ¬ Joined sphere0_pos sphere0_neg := by
  intro h
  have h0 : h.somePath 0 = sphere0_pos := Path.source _
  have h1 : h.somePath 1 = sphere0_neg := Path.target _
  have heq := TotallyDisconnectedSpace.eq_of_continuous
    (h.somePath : unitInterval → ↥(Metric.sphere (0 : ℝ) 1))
    h.somePath.continuous (0 : unitInterval) (1 : unitInterval)
  rw [h0, h1] at heq
  have : (1 : ℝ) = -1 := congrArg Subtype.val heq
  norm_num at this

lemma zerothHomotopy_sphere0_pos_ne_neg :
    ZerothHomotopy.mk sphere0_pos ≠ ZerothHomotopy.mk sphere0_neg := by
  intro h
  exact not_joined_sphere0_pos_neg (Quotient.exact h)

lemma zerothHomotopy_sphere0_eq (c : ZerothHomotopy ↥(Metric.sphere (0 : ℝ) 1)) :
    c = ZerothHomotopy.mk sphere0_pos ∨ c = ZerothHomotopy.mk sphere0_neg := by
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  rcases sphere0_eq_pos_or_neg x with hx | hx
  · exact Or.inl (congrArg _ hx)
  · exact Or.inr (congrArg _ hx)

noncomputable def equivZerothHomotopy_sphere0 :
    ZerothHomotopy ↥(Metric.sphere (0 : ℝ) 1) ≃ Bool := by
  classical
  refine
    { toFun := fun c => decide (c = ZerothHomotopy.mk sphere0_pos)
      invFun := fun b => bif b then ZerothHomotopy.mk sphere0_pos
        else ZerothHomotopy.mk sphere0_neg
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    rcases zerothHomotopy_sphere0_eq c with hc | hc
    · simp [hc]
    · have hne : ¬ ZerothHomotopy.mk sphere0_neg = ZerothHomotopy.mk sphere0_pos :=
        zerothHomotopy_sphere0_pos_ne_neg.symm
      simp [hc, hne]
  · intro b
    cases b with
    | true => simp
    | false =>
      have hne : ¬ ZerothHomotopy.mk sphere0_neg = ZerothHomotopy.mk sphere0_pos :=
        zerothHomotopy_sphere0_pos_ne_neg.symm
      simp [hne]

/-- Coproduct of two copies of `R`, indexed by `Bool`, is the biproduct. -/
noncomputable def sigmaBoolIsoBiprod :
    (∐ fun _ : Bool ↦ R) ≅ R ⊞ R where
  hom := Sigma.desc fun b => bif b then biprod.inl else biprod.inr
  inv := biprod.desc (Sigma.ι (fun _ : Bool ↦ R) true) (Sigma.ι (fun _ : Bool ↦ R) false)
  hom_inv_id := by
    refine Sigma.hom_ext _ _ ?_
    intro b
    cases b with
    | false =>
      rw [Sigma.ι_desc_assoc]
      change biprod.inr ≫ biprod.desc _ _ = _
      rw [biprod.inr_desc, Category.comp_id]
    | true =>
      rw [Sigma.ι_desc_assoc]
      change biprod.inl ≫ biprod.desc _ _ = _
      rw [biprod.inl_desc, Category.comp_id]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [biprod.inl_desc_assoc, Sigma.ι_desc, Category.comp_id]
      rfl
    · rw [biprod.inr_desc_assoc, Sigma.ι_desc, Category.comp_id]
      rfl

/-- Shear `(x, y) ↦ (x, x+y)` on a biproduct. -/
noncomputable def biprodShearIso (X : ModuleCat.{0} k) : X ⊞ X ≅ X ⊞ X where
  hom := biprod.lift biprod.fst (biprod.fst + biprod.snd)
  inv := biprod.lift biprod.fst (biprod.snd + (-biprod.fst))
  hom_inv_id := by
    refine biprod.hom_ext _ _ ?_ ?_
    · simp
    · simp [sub_eq_add_neg, add_assoc, add_neg_cancel_comm_assoc, add_neg_cancel]
  inv_hom_id := by
    refine biprod.hom_ext _ _ ?_ ?_
    · simp
    · simp [sub_eq_add_neg, add_assoc, add_neg_cancel_comm_assoc, add_neg_cancel]

lemma biprodShearIso_hom_snd (X : ModuleCat.{0} k) :
    (biprodShearIso X).hom ≫ biprod.snd = biprod.fst + biprod.snd :=
  biprod.lift_snd _ _

lemma biprod_fst_add_snd_eq_desc (X : ModuleCat.{0} k) :
    (biprod.fst : X ⊞ X ⟶ X) + biprod.snd = biprod.desc (𝟙 X) (𝟙 X) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · simp
  · simp

lemma sigmaBoolIsoBiprod_hom_desc :
    (sigmaBoolIsoBiprod (R := R)).hom ≫ biprod.desc (𝟙 R) (𝟙 R) =
      Sigma.desc fun _ : Bool ↦ 𝟙 R := by
  refine Sigma.hom_ext _ _ ?_
  intro b
  cases b with
  | false =>
    dsimp [sigmaBoolIsoBiprod]
    rw [Sigma.ι_desc_assoc]
    change biprod.inr ≫ biprod.desc (𝟙 R) (𝟙 R) = _
    rw [biprod.inr_desc, Sigma.ι_desc]
  | true =>
    dsimp [sigmaBoolIsoBiprod]
    rw [Sigma.ι_desc_assoc]
    change biprod.inl ≫ biprod.desc (𝟙 R) (𝟙 R) = _
    rw [biprod.inl_desc, Sigma.ι_desc]

lemma sigma_desc_id_sphere0 :
    (Sigma.reindex equivZerothHomotopy_sphere0
        (fun _ : Bool ↦ R)).hom ≫
      Sigma.desc (fun _ : Bool ↦ 𝟙 R) =
    Sigma.desc fun _ : ZerothHomotopy ↥(Metric.sphere (0 : ℝ) 1) ↦ 𝟙 R := by
  refine Sigma.hom_ext _ _ ?_
  intro c
  rw [Sigma.ι_reindex_hom_assoc]
  refine Eq.trans (Sigma.ι_desc (fun _ : Bool ↦ 𝟙 R)
      (equivZerothHomotopy_sphere0 c)) ?_
  exact (Sigma.ι_desc (fun _ : ZerothHomotopy ↥(Metric.sphere (0 : ℝ) 1) ↦ 𝟙 R) c).symm

/-- `ker(epsilon : H_0(S^0) → R) ≅ R`. -/
noncomputable def kernel_singularHomology₀ε_sphere0 :
    kernel ((TopCat.of ↥(Metric.sphere (0 : ℝ) 1)).singularHomology₀ε R) ≅ R :=
  let e0 := TopCat.singularHomology₀Iso (.of ↥(Metric.sphere (0 : ℝ) 1)) R
  let ere : (∐ fun _ : ZerothHomotopy ↥(Metric.sphere (0 : ℝ) 1) ↦ R) ≅
      (∐ fun _ : Bool ↦ R) :=
    Sigma.reindex equivZerothHomotopy_sphere0 (fun _ : Bool ↦ R)
  have hEps : (TopCat.of ↥(Metric.sphere (0 : ℝ) 1)).singularHomology₀ε R =
      e0.hom ≫ ere.hom ≫ (sigmaBoolIsoBiprod (R := R)).hom ≫
        (biprodShearIso R).hom ≫ biprod.snd := by
    have h1 := TopCat.singularHomology₀Iso_sigma_desc_id
      (.of ↥(Metric.sphere (0 : ℝ) 1)) R
    have h2 := sigma_desc_id_sphere0 (R := R)
    have h3 := sigmaBoolIsoBiprod_hom_desc (R := R)
    have h4 := biprodShearIso_hom_snd (X := R)
    have h5 := biprod_fst_add_snd_eq_desc (X := R)
    calc
      (TopCat.of ↥(Metric.sphere (0 : ℝ) 1)).singularHomology₀ε R =
          e0.hom ≫ Sigma.desc (fun _ ↦ 𝟙 R) := h1.symm
      _ = e0.hom ≫ ere.hom ≫ Sigma.desc fun _ : Bool ↦ 𝟙 R := by
        rw [← h2]; rfl
      _ = e0.hom ≫ ere.hom ≫ (sigmaBoolIsoBiprod (R := R)).hom ≫
            biprod.desc (𝟙 R) (𝟙 R) := by
        rw [← h3]
      _ = e0.hom ≫ ere.hom ≫ (sigmaBoolIsoBiprod (R := R)).hom ≫
            (biprod.fst + biprod.snd) := by
        rw [h5]
      _ = e0.hom ≫ ere.hom ≫ (sigmaBoolIsoBiprod (R := R)).hom ≫
            (biprodShearIso R).hom ≫ biprod.snd := by
        rw [← h4]
  (kernel.congr _ _ hEps).trans <|
    (kernelIsIsoComp (e0.hom ≫ ere.hom ≫ (sigmaBoolIsoBiprod (R := R)).hom ≫
        (biprodShearIso R).hom) biprod.snd).trans
      kernelBiprodSndIso

/-- Stereographic intersection of `S^1` is homotopy-equivalent to `S^0 ⊂ ℝ`. -/
def homotopyEquiv_puncturedInter_sphere0 :
    ↥(puncturedNorth 1 ∩ puncturedSouth 1) ≃ₕ ↥(Metric.sphere (0 : ℝ) 1) :=
  (homotopyEquiv_puncturedInter_sphere 0).trans homeoMetricSphere0.toHomotopyEquiv

/-- `H_1(S^1; R) ≅ R`. -/
noncomputable def singularHomology_sphere1 :
    (((singularHomologyFunctor (ModuleCat.{0} k) 1).obj R).obj
        (.of (MetricSphere 1))) ≅ R :=
  let iU := interInclLeft (puncturedNorth 1) (puncturedSouth 1)
  let iV := interInclRight (puncturedNorth 1) (puncturedSouth 1)
  haveI : Mono (triadδ (C := ModuleCat.{0} k) R iU iV 0) :=
    triadδ_sphere_mono_zero (R := R) 1
  have hcmp := homologyMap_mvIncl_comp_aug (R := R) iU iV
  let F := homologyFunctor (ModuleCat.{0} k) (ComplexShape.down ℕ) 0
  let KU := ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
    (.of ↥(puncturedNorth 1))
  let KV := ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
    (.of ↥(puncturedSouth 1))
  let epsU := (TopCat.of ↥(puncturedNorth 1)).singularHomology₀ε R
  let epsV := (TopCat.of ↥(puncturedSouth 1)).singularHomology₀ε R
  haveI : IsIso epsU := inferInstance
  haveI : IsIso epsV := inferInstance
  let thetaIso :
      (((singularHomologyFunctor (ModuleCat.{0} k) 0).obj R).obj
          (.of ↥(puncturedNorth 1))) ⊞
        (((singularHomologyFunctor (ModuleCat.{0} k) 0).obj R).obj
          (.of ↥(puncturedSouth 1))) ≅ R ⊞ R :=
    { hom := biprod.map epsU epsV
      inv := biprod.map (inv epsU) (inv epsV)
      hom_inv_id := by
        refine biprod.hom_ext _ _ ?_ ?_
        · simp
        · simp
      inv_hom_id := by
        refine biprod.hom_ext _ _ ?_ ?_
        · simp
        · simp }
  let q := (F.mapBiprod KU KV).trans thetaIso
  haveI : Mono (biprod.lift (𝟙 R) (-𝟙 R)) := biprod_lift_id_neg_id_mono R
  let eW := singularHomologyIso_of_homotopyEquiv
    (homotopyEquiv_puncturedInter_sphere0) R 0
  have hnat : eW.hom ≫
      (TopCat.of ↥(Metric.sphere (0 : ℝ) 1)).singularHomology₀ε R =
      (TopCat.of ↥(puncturedNorth 1 ∩ puncturedSouth 1)).singularHomology₀ε R :=
    singularHomology₀ε_natural (TopCat.ofHom homotopyEquiv_puncturedInter_sphere0.toFun) R
  (excisiveHomologyIso (C := ModuleCat.{0} k) R iU iV
      (subtypeIncl (MetricSphere 1) (puncturedNorth 1))
      (subtypeIncl (MetricSphere 1) (puncturedSouth 1))
      (subset_square_comm _ _)
      (SingularExcision.IsExcisiveSubspaces_puncturedSphere (R := R) 1) 1).symm.trans <|
    (triadδ_isoKernel (R := R) iU iV).trans <|
      (kernel.mapIso
          (f := homologyMap (mvIncl (C := ModuleCat.{0} k) R iU iV) 0)
          ((TopCat.of ↥(puncturedNorth 1 ∩ puncturedSouth 1)).singularHomology₀ε R ≫
            biprod.lift (𝟙 R) (-𝟙 R))
          (Iso.refl _) q (by
            simpa using hcmp)).trans <|
        (kernelCompMono
            ((TopCat.of ↥(puncturedNorth 1 ∩ puncturedSouth 1)).singularHomology₀ε R)
            (biprod.lift (𝟙 R) (-𝟙 R))).trans <|
          (kernel.congr _ _ hnat.symm).trans <|
            (kernelIsIsoComp eW.hom
                ((TopCat.of ↥(Metric.sphere (0 : ℝ) 1)).singularHomology₀ε R)).trans
              (kernel_singularHomology₀ε_sphere0 (R := R))

/-- For `n > 0`, `H_n(S^n; R) ≅ R`. -/
noncomputable def singularHomology_sphere {n : ℕ} (hn : 0 < n) :
    (((singularHomologyFunctor (ModuleCat.{0} k) n).obj R).obj
        (.of (MetricSphere n))) ≅ R :=
  (singularHomology_sphere_iso_sphere1 (R := R) hn).trans
    (singularHomology_sphere1 (R := R))

/-- `H_0(S^2; R) ≅ R` by path-connectedness. -/
noncomputable def singularHomology_sphere2_zero :
    (((singularHomologyFunctor (ModuleCat.{0} k) 0).obj R).obj
        (.of (MetricSphere 2))) ≅ R :=
  haveI : NeZero (2 : ℕ) := ⟨by decide⟩
  singularHomology₀Iso_pathConnected _ R

/-- `H_1(S^2; R) = 0`. -/
lemma isZero_singularHomology_sphere2_one :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} k) 1).obj R).obj
      (.of (MetricSphere 2))) :=
  isZero_singularHomology_sphere (R := R) (n := 2) (m := 1)
    (by decide) (by decide) (by decide)

/-- `H_2(S^2; R) ≅ R`. -/
noncomputable def singularHomology_sphere2 :
    (((singularHomologyFunctor (ModuleCat.{0} k) 2).obj R).obj
        (.of (MetricSphere 2))) ≅ R :=
  singularHomology_sphere (R := R) (n := 2) (by decide)

/-- The 3D classification from a cellular 2-complex with numeric Betti
numbers `1, 0, 1`, which agree with singular `H_*(S^2)`
(`singularHomology_sphere2_zero`, `isZero_singularHomology_sphere2_one`,
`singularHomology_sphere2`). Euler–Poincaré supplies `V+F=E+2`; regularity
then forces a Platonic pair. Palomar compared types are unchanged. -/
theorem platonic_solids_3d_of_sphere
    {K : Type*} [Field K]
    {C₂ C₁ C₀ : Type*}
    [AddCommGroup C₂] [Module K C₂] [FiniteDimensional K C₂]
    [AddCommGroup C₁] [Module K C₁] [FiniteDimensional K C₁]
    [AddCommGroup C₀] [Module K C₀] [FiniteDimensional K C₀]
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀)
    (V E F p q : ℕ)
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    (h_edges_faces : p * F = 2 * E)
    (h_edges_verts : q * V = 2 * E)
    (hV : Module.finrank K C₀ = V)
    (hE : Module.finrank K C₁ = E)
    (hF : Module.finrank K C₂ = F)
    (hcomp : d₁.comp d₂ = 0)
    (hs0 : betti0 d₁ = 1)
    (hs1 : betti1 d₂ d₁ = 0)
    (hs2 : betti2 d₂ = 1) :
    IsPlatonicPair p q :=
  platonic_solids_3d_of_homology d₂ d₁ V E F p q hp hq
    h_edges_faces h_edges_verts hV hE hF hcomp hs0 hs1 hs2

end
