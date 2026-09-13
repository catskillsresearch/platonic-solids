/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import PlatonicSolids.SingularExcision.AffineRealization

/-!
# Interpreting finite affine chains as singular chains

A finite integral affine chain in the standard `q`-simplex is composed
with a singular `q`-simplex, then interpreted in Mathlib's coproduct of
copies of the coefficient object.
-/

open AlgebraicTopology CategoryTheory Limits
open scoped Simplicial

namespace PlatonicSolids.SingularExcision

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Preadditive C]

/-- The singular-chain generator obtained by affine reparametrization. -/
noncomputable def realizeAffineSimplex
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    R ⟶ (((singularChainComplexFunctor C).obj R).obj X).X p :=
  (TopCat.toSSet.obj X).ιChainComplex
    (reparametrizeSingularSimplex s σ)

/-- Interpret a finite integral affine chain as a morphism into singular chains. -/
noncomputable def realizeAffineChain
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (c : AffineChain (stdSimplex ℝ (Fin (q + 1))) p) :
    R ⟶ (((singularChainComplexFunctor C).obj R).obj X).X p :=
  c.sum fun σ z ↦ z • realizeAffineSimplex R s σ

@[simp]
theorem realizeAffineChain_zero
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌) :
    realizeAffineChain R s
      (0 : AffineChain (stdSimplex ℝ (Fin (q + 1))) p) = 0 := by
  simp [realizeAffineChain]

@[simp]
theorem realizeAffineChain_single
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) (z : ℤ) :
    realizeAffineChain R s (Finsupp.single σ z) =
      z • realizeAffineSimplex R s σ := by
  classical
  simp [realizeAffineChain]

/-- Subdivision of one singular one-simplex, on its coproduct generator. -/
noncomputable def singularIntervalSubdivision
    (R : C) {X : TopCat.{0}}
    (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    R ⟶ (((singularChainComplexFunctor C).obj R).obj X).X 1 :=
  realizeAffineChain R s standardIntervalSubdivision

/-- The one-dimensional prism, interpreted as a singular two-chain. -/
noncomputable def singularIntervalPrism
    (R : C) {X : TopCat.{0}}
    (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    R ⟶ (((singularChainComplexFunctor C).obj R).obj X).X 2 :=
  realizeAffineChain R s standardIntervalPrism

end

end PlatonicSolids.SingularExcision
