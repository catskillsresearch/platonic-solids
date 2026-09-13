/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.QuasiIso
import PlatonicSolids.SingularExcision.CoverChains
import PlatonicSolids.SingularExcision.SmallChains

/-!
Open-cover excision: the small-subcomplex inclusion is the remaining
comparison from cover chains to ambient singular chains. The geometric
retract is in `SmallChains`; the triangle identification of
`coverComparison` with `smallι` is the next algebraic step.
-/

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Set
open scoped Topology

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

end

end SingularExcision
