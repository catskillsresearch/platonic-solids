/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
The canonical chain map from the simplicial chains of a simplicial set to
the singular chains of its geometric realization.

The intended comparison theorem says that this map is a quasi-isomorphism
for finite nonsingular simplicial sets. This file begins by fixing the
canonical map, its normalized form, and the naturality and reduction lemmas
needed by an attachment proof.
-/

noncomputable section

open AlgebraicTopology CategoryTheory HomologicalComplex
open scoped Simplicial

variable {k : Type} [Ring k]

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

