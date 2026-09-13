/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homeomorph.Lemmas
import PlatonicSolids.RelativeHomology
import PlatonicSolids.SingularHomology

/-!
Mayer–Vietoris for a commuting square of spaces

```
  W --iU--> U
  |         |
 iV        jU
  |         |
  v         v
  V --jV--> X
```

The map `C_*(W) → C_*(U) ⊕ C_*(V)`, `σ ↦ (iU_# σ, -iV_# σ)` is a monomorphism
as soon as `iU` is. Its cokernel is the chain complex of the cover; the
commuting square induces a comparison `coker → C_*(X)`. The square is
*excisive* when that comparison is a quasi-isomorphism. In that case the
homology sequence of the cover is the Mayer–Vietoris sequence of `X`.

The stereographic cover of `Sⁿ` (complements of the poles) is the
classical excisive pair: each chart is contractible. Barycentric
subdivision and the singular chain map live in
`PlatonicSolids/SingularExcision/`. The remaining obstruction to
`Hₙ(Metric.sphere)` for `n > 0` is mesh shrinking plus the open-cover
quasi-isomorphism that would discharge `IsExcisiveSubspaces`.
-/

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Metric Set
open scoped Topology ContinuousMap

set_option linter.unusedSectionVars false

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{0} C] [HasPullbacks C]

variable (R : C)

/-! ## Abstract triad -/

variable {W U V X : TopCat.{0}}
variable (iU : W ⟶ U) (iV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X)

/-- `C_*(W) → C_*(U) ⊕ C_*(V)`, the Mayer–Vietoris inclusion of the intersection. -/
noncomputable def mvIncl :
    ((singularChainComplexFunctor C).obj R).obj W ⟶
      ((singularChainComplexFunctor C).obj R).obj U ⊞
        ((singularChainComplexFunctor C).obj R).obj V :=
  biprod.lift
    (((singularChainComplexFunctor C).obj R).map iU)
    (-(((singularChainComplexFunctor C).obj R).map iV))

instance mvIncl_mono [Mono iU] : Mono (mvIncl (C := C) R iU iV) :=
  haveI : Mono (((singularChainComplexFunctor C).obj R).map iU) :=
    ((singularChainComplexFunctor C).obj R).map_mono iU
  mono_of_mono_fac (biprod.lift_fst
    (((singularChainComplexFunctor C).obj R).map iU)
    (-(((singularChainComplexFunctor C).obj R).map iV)))

/-- Chains of the cover: `coker(C_*(W) → C_*(U) ⊕ C_*(V))`. -/
noncomputable def coverChains : ChainComplex C ℕ :=
  cokernel (mvIncl (C := C) R iU iV)

/-- The short complex of the triad. -/
noncomputable def triadShortComplex [Mono iU] :
    ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (mvIncl (C := C) R iU iV) (cokernel.π _) (cokernel.condition _)

instance triadShortComplex_mono_f [Mono iU] :
    Mono (triadShortComplex (C := C) R iU iV).f :=
  inferInstanceAs (Mono (mvIncl (C := C) R iU iV))

instance triadShortComplex_epi_g [Mono iU] :
    Epi (triadShortComplex (C := C) R iU iV).g :=
  inferInstanceAs (Epi (cokernel.π (mvIncl (C := C) R iU iV)))

/-- The triad sequence of singular chains is short exact. -/
lemma triad_shortExact [Mono iU] :
    (triadShortComplex (C := C) R iU iV).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _
      (cokernelIsCokernel (mvIncl (C := C) R iU iV)))
    inferInstance inferInstance

/-- `C_*(U) ⊕ C_*(V) → C_*(X)` induced by the two inclusions into `X`. -/
noncomputable def coverToX (_hcomm : iU ≫ jU = iV ≫ jV) :
    ((singularChainComplexFunctor C).obj R).obj U ⊞
      ((singularChainComplexFunctor C).obj R).obj V ⟶
      ((singularChainComplexFunctor C).obj R).obj X :=
  biprod.desc
    (((singularChainComplexFunctor C).obj R).map jU)
    (((singularChainComplexFunctor C).obj R).map jV)

lemma mvIncl_comp_coverToX (hcomm : iU ≫ jU = iV ≫ jV) :
    mvIncl (C := C) R iU iV ≫ coverToX (C := C) R iU iV jU jV hcomm = 0 := by
  dsimp [mvIncl, coverToX]
  ext
  simp [← Functor.map_comp, hcomm]

/-- Comparison of cover chains with ambient chains. -/
noncomputable def coverComparison (hcomm : iU ≫ jU = iV ≫ jV) :
    coverChains (C := C) R iU iV ⟶
      ((singularChainComplexFunctor C).obj R).obj X :=
  cokernel.desc _ (coverToX (C := C) R iU iV jU jV hcomm)
    (mvIncl_comp_coverToX (C := C) R iU iV jU jV hcomm)

/-- A commuting square of spaces is excisive when cover chains compute `H_*(X)`. -/
def IsExcisive (hcomm : iU ≫ jU = iV ≫ jV) : Prop :=
  QuasiIso (coverComparison (C := C) R iU iV jU jV hcomm)

/-- Connecting map of the triad: `H_{n+1}(U+V) → Hₙ(W)`. -/
noncomputable def triadδ [Mono iU] (n : ℕ) :
    (coverChains (C := C) R iU iV).homology (n + 1) ⟶
      (((singularChainComplexFunctor C).obj R).obj W).homology n :=
  (triad_shortExact (C := C) R iU iV).δ (n + 1) n (by simp)

/-- If the square is excisive, homology of the cover is homology of `X`. -/
noncomputable def excisiveHomologyIso
    (hcomm : iU ≫ jU = iV ≫ jV)
    (h : IsExcisive (C := C) R iU iV jU jV hcomm) (n : ℕ) :
    (coverChains (C := C) R iU iV).homology n ≅
      (((singularChainComplexFunctor C).obj R).obj X).homology n :=
  have : QuasiIso (coverComparison (C := C) R iU iV jU jV hcomm) := h
  asIso (homologyMap (coverComparison (C := C) R iU iV jU jV hcomm) n)

/-- Mayer–Vietoris connecting map, after excision. -/
noncomputable def mayerVietorisδ [Mono iU]
    (hcomm : iU ≫ jU = iV ≫ jV)
    (h : IsExcisive (C := C) R iU iV jU jV hcomm) (n : ℕ) :
    (((singularChainComplexFunctor C).obj R).obj X).homology (n + 1) ⟶
      (((singularChainComplexFunctor C).obj R).obj W).homology n :=
  (excisiveHomologyIso (C := C) R iU iV jU jV hcomm h (n + 1)).inv ≫
    triadδ (C := C) R iU iV n

/-- Exactness of `Hₙ(W) → Hₙ(U) ⊕ Hₙ(V) → Hₙ(U+V)`. -/
lemma triad_exact_at_sum [Mono iU] (n : ℕ) :
    (ShortComplex.mk
      (homologyMap (mvIncl (C := C) R iU iV) n)
      (homologyMap (cokernel.π (mvIncl (C := C) R iU iV)) n)
      (by rw [← homologyMap_comp, cokernel.condition, homologyMap_zero])).Exact :=
  (triad_shortExact (C := C) R iU iV).homology_exact₂ n

/-- Exactness of `H_{n+1}(U+V) → Hₙ(W) → Hₙ(U) ⊕ Hₙ(V)`. -/
lemma triad_exact_at_W [Mono iU] (n : ℕ) :
    (ShortComplex.mk (triadδ (C := C) R iU iV n)
      (homologyMap (mvIncl (C := C) R iU iV) n)
      (by
        simpa [triadδ, triadShortComplex] using
          (triad_shortExact (C := C) R iU iV).δ_comp (n + 1) n (by simp))).Exact :=
  (triad_shortExact (C := C) R iU iV).homology_exact₁ (n + 1) n (by simp)

/-! ## Subspace covers -/

variable {Y : Type} [TopologicalSpace Y]

/-- Inclusion of an intersection as a subspace of the first set. -/
def interInclLeft (A B : Set Y) : TopCat.of ↥(A ∩ B) ⟶ TopCat.of ↥A :=
  TopCat.ofHom (ContinuousMap.inclusion (fun _ hx => hx.1))

/-- Inclusion of an intersection as a subspace of the second set. -/

def interInclRight (A B : Set Y) : TopCat.of ↥(A ∩ B) ⟶ TopCat.of ↥B :=
  TopCat.ofHom (ContinuousMap.inclusion (fun _ hx => hx.2))

instance interInclLeft_mono (A B : Set Y) : Mono (interInclLeft A B) :=
  (TopCat.mono_iff_injective _).2 fun _ _ h =>
    Subtype.ext (congrArg (Subtype.val : ↥A → Y) h)

instance interInclRight_mono (A B : Set Y) : Mono (interInclRight A B) :=
  (TopCat.mono_iff_injective _).2 fun _ _ h =>
    Subtype.ext (congrArg (Subtype.val : ↥B → Y) h)

lemma subset_square_comm (A B : Set Y) :
    interInclLeft A B ≫ subtypeIncl Y A =
      interInclRight A B ≫ subtypeIncl Y B := by
  ext x
  rfl

/-- A pair of subspaces is excisive when their cover computes `H_*(Y)`. -/
def IsExcisiveSubspaces (A B : Set Y) : Prop :=
  IsExcisive (C := C) R (interInclLeft A B) (interInclRight A B)
    (subtypeIncl Y A) (subtypeIncl Y B) (subset_square_comm A B)

/-! ## Stereographic cover of the metric sphere -/

/-- The unit `n`-sphere in Euclidean space of dimension `n+1`. -/
abbrev MetricSphere (n : ℕ) : Type :=
  ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- North pole `e₀` of `Sⁿ`. -/
noncomputable def northPole (n : ℕ) : MetricSphere n :=
  ⟨EuclideanSpace.single 0 1, by simp [mem_sphere_iff_norm]⟩

/-- South pole `−e₀` of `Sⁿ`. -/
noncomputable def southPole (n : ℕ) : MetricSphere n :=
  ⟨-EuclideanSpace.single 0 1, by simp [mem_sphere_iff_norm]⟩

lemma northPole_ne_southPole (n : ℕ) : northPole n ≠ southPole n := by
  intro h
  have h1 : (1 : ℝ) = -1 := by
    simpa [northPole, southPole] using
      congrArg (fun p : MetricSphere n =>
        (p : EuclideanSpace ℝ (Fin (n + 1))) 0) h
  norm_num at h1

/-- Open chart `Sⁿ \ {N}`. -/
def puncturedNorth (n : ℕ) : Set (MetricSphere n) :=
  {northPole n}ᶜ

/-- Open chart `Sⁿ \ {S}`. -/
def puncturedSouth (n : ℕ) : Set (MetricSphere n) :=
  {southPole n}ᶜ

lemma isOpen_puncturedNorth (n : ℕ) : IsOpen (puncturedNorth n) :=
  isOpen_compl_singleton

lemma isOpen_puncturedSouth (n : ℕ) : IsOpen (puncturedSouth n) :=
  isOpen_compl_singleton

lemma punctured_cover (n : ℕ) :
    puncturedNorth n ∪ puncturedSouth n = univ := by
  ext x
  simp [puncturedNorth, puncturedSouth]
  exact or_iff_not_imp_left.2 fun hx => by
    rintro rfl
    exact hx (northPole_ne_southPole n).symm

lemma punctured_inter (n : ℕ) :
    puncturedNorth n ∩ puncturedSouth n = {northPole n, southPole n}ᶜ := by
  ext x
  simp [puncturedNorth, puncturedSouth]

lemma norm_northPole (n : ℕ) :
    ‖(northPole n : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
  simp [northPole]

lemma norm_southPole (n : ℕ) :
    ‖(southPole n : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
  simp [southPole]

/-- Stereographic projection from the north pole is a homeomorphism
`Sⁿ \ {N}` homeomorphic to the orthogonal complement of `ℝ ∙ N`. -/
noncomputable def homeoPuncturedNorth (n : ℕ) :
    ↥(puncturedNorth n) ≃ₜ
      ((ℝ ∙ (northPole n : EuclideanSpace ℝ (Fin (n + 1))))ᗮ) :=
  have hsrc : (stereographic (norm_northPole n)).source = puncturedNorth n := by
    ext x
    simp [puncturedNorth, northPole, stereographic_source]
  (Homeomorph.setCongr hsrc).trans
    ((stereographic (norm_northPole n)).toHomeomorphSourceTarget.trans
      (Homeomorph.Set.univ _))

instance contractible_puncturedNorth (n : ℕ) :
    ContractibleSpace ↥(puncturedNorth n) :=
  (homeoPuncturedNorth n).contractibleSpace

/-- Stereographic projection from the south pole is a homeomorphism
`Sⁿ \ {S}` homeomorphic to the orthogonal complement of `ℝ ∙ S`. -/
noncomputable def homeoPuncturedSouth (n : ℕ) :
    ↥(puncturedSouth n) ≃ₜ
      ((ℝ ∙ (southPole n : EuclideanSpace ℝ (Fin (n + 1))))ᗮ) :=
  have hsrc : (stereographic (norm_southPole n)).source = puncturedSouth n := by
    ext x
    simp [puncturedSouth, southPole, stereographic_source]
  (Homeomorph.setCongr hsrc).trans
    ((stereographic (norm_southPole n)).toHomeomorphSourceTarget.trans
      (Homeomorph.Set.univ _))

instance contractible_puncturedSouth (n : ℕ) :
    ContractibleSpace ↥(puncturedSouth n) :=
  (homeoPuncturedSouth n).contractibleSpace

/-- Positive singular homology of the northern stereographic chart vanishes. -/
lemma isZero_singularHomology_puncturedNorth
    (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    IsZero (((singularHomologyFunctor C k).obj R).obj
      (.of ↥(puncturedNorth n))) :=
  isZero_singularHomology_of_contractible R hk

/-- Positive singular homology of the southern stereographic chart vanishes. -/
lemma isZero_singularHomology_puncturedSouth
    (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    IsZero (((singularHomologyFunctor C k).obj R).obj
      (.of ↥(puncturedSouth n))) :=
  isZero_singularHomology_of_contractible R hk

/-- Mayer–Vietoris connecting map for the stereographic cover, after
excision. The charts are contractible, so this is the inductive step
for `Hₙ(Sⁿ)` once `IsExcisiveSubspaces` is available. -/
noncomputable def singularHomology_sphere_mayerVietorisδ
    (n : ℕ)
    (hex : IsExcisiveSubspaces (C := C) R
      (puncturedNorth (n + 1)) (puncturedSouth (n + 1))) :
    (((singularChainComplexFunctor C).obj R).obj
        (.of (MetricSphere (n + 1)))).homology (n + 1) ⟶
      (((singularChainComplexFunctor C).obj R).obj
        (.of ↥(puncturedNorth (n + 1) ∩ puncturedSouth (n + 1)))).homology n :=
  mayerVietorisδ (C := C) R
    (interInclLeft (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
    (interInclRight (puncturedNorth (n + 1)) (puncturedSouth (n + 1)))
    (subtypeIncl (MetricSphere (n + 1)) (puncturedNorth (n + 1)))
    (subtypeIncl (MetricSphere (n + 1)) (puncturedSouth (n + 1)))
    (subset_square_comm _ _) hex n
