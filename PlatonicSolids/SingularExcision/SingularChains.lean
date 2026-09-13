/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import PlatonicSolids.SingularExcision.AffineRealization

/-!
# Interpreting finite affine chains as singular chains

A finite integral affine chain in the standard `q`-simplex is composed
with a singular `q`-simplex, then interpreted in Mathlib's coproduct of
copies of the coefficient object. Face-compatibility of realization
makes the barycentric generators assemble to a chain map, with the
prism as a chain homotopy to the identity.
-/

open AlgebraicTopology CategoryTheory Limits HomologicalComplex
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
    (s : (TopCat.toSSet.obj X) _⦋q⦌) :
    AffineChain (stdSimplex ℝ (Fin (q + 1))) p →+
      (R ⟶ (((singularChainComplexFunctor C).obj R).obj X).X p) :=
  Finsupp.liftAddHom fun σ =>
    (smulAddHom ℤ
      (R ⟶ (((singularChainComplexFunctor C).obj R).obj X).X p)).flip
      (realizeAffineSimplex R s σ)

@[simp]
theorem realizeAffineChain_zero
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌) :
    realizeAffineChain R s
      (0 : AffineChain (stdSimplex ℝ (Fin (q + 1))) p) = 0 := by
  simp

@[simp]
theorem realizeAffineChain_single
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) (z : ℤ) :
    realizeAffineChain R s (Finsupp.single σ z) =
      z • realizeAffineSimplex R s σ := by
  simp [realizeAffineChain]

@[simp]
theorem realizeAffineChain_simplex
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    realizeAffineChain R s (simplex σ) = realizeAffineSimplex R s σ := by
  simp [simplex]

theorem realizeAffineSimplex_map
    (R : C) {X : TopCat.{0}} {p q k : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (ρ : AffineSimplex (stdSimplex ℝ (Fin (p + 1))) k) :
    realizeAffineSimplex R s (AffineSimplex.map σ.realize ρ) =
      realizeAffineSimplex R (reparametrizeSingularSimplex s σ) ρ := by
  simp [realizeAffineSimplex, reparametrizeSingularSimplex_map]

theorem realizeAffineChain_map
    (R : C) {X : TopCat.{0}} {p q k : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (c : AffineChain (stdSimplex ℝ (Fin (p + 1))) k) :
    realizeAffineChain R s (AffineChain.map σ.realize c) =
      realizeAffineChain R (reparametrizeSingularSimplex s σ) c := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add τ z c _ _ ih =>
      simp [map_add, ih, AffineChain.map_single, realizeAffineSimplex_map]

theorem realizeAffineSimplex_d
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) (p + 1)) :
    realizeAffineSimplex R s σ ≫
        (((singularChainComplexFunctor C).obj R).obj X).d (p + 1) p =
      ∑ i : Fin (p + 2),
        (-1 : ℤ) ^ (i : ℕ) • realizeAffineSimplex R s (σ.face i) := by
  simp only [realizeAffineSimplex]
  change _ ≫ ((TopCat.toSSet.obj X).chainComplex R).d (p + 1) p = _
  rw [SSet.ιChainComplex_d]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  rw [reparametrizeSingularSimplex_face]

theorem realizeAffineChain_simplexBoundary
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) (p + 1)) :
    realizeAffineChain R s (simplexBoundary σ) =
      ∑ i : Fin (p + 2),
        (-1 : ℤ) ^ (i : ℕ) • realizeAffineSimplex R s (σ.face i) := by
  simp [simplexBoundary, map_sum, map_zsmul]

theorem realizeAffineChain_boundary
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (c : AffineChain (stdSimplex ℝ (Fin (q + 1))) (p + 1)) :
    realizeAffineChain R s (boundary c) =
      realizeAffineChain R s c ≫
        (((singularChainComplexFunctor C).obj R).obj X).d (p + 1) p := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add σ z c _ _ ih =>
      simp [map_add, ih, Preadditive.add_comp]
      rw [show Finsupp.single σ z = z • simplex σ by simp [simplex]]
      simp [map_zsmul, boundary_simplex,
        realizeAffineChain_simplexBoundary, realizeAffineSimplex_d]

theorem realizeAffineChain_subdivideStd_simplex
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    realizeAffineChain R s (subdivideStd (q := q) p (simplex σ)) =
      realizeAffineChain R (reparametrizeSingularSimplex s σ)
        (standardSubdivision p) := by
  rw [← AffineChain.map_standardSubdivision, realizeAffineChain_map]

theorem realizeAffineChain_prismStd_simplex
    (R : C) {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    realizeAffineChain R s (prismStd (q := q) p (simplex σ)) =
      realizeAffineChain R (reparametrizeSingularSimplex s σ)
        (standardPrism p) := by
  rw [← AffineChain.map_standardPrism, realizeAffineChain_map]

@[simp]
theorem realizeAffineSimplex_id
    (R : C) {X : TopCat.{0}} {q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌) :
    realizeAffineSimplex R s (idSimplex q) =
      (TopCat.toSSet.obj X).ιChainComplex s := by
  simp [realizeAffineSimplex]

/-- Subdivision of one singular simplex, on its coproduct generator. -/
noncomputable def singularSubdivideGenerator
    (R : C) {X : TopCat.{0}} {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    R ⟶ (((singularChainComplexFunctor C).obj R).obj X).X n :=
  realizeAffineChain R s (standardSubdivision n)

/-- Prism of one singular simplex, on its coproduct generator. -/
noncomputable def singularPrismGenerator
    (R : C) {X : TopCat.{0}} {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    R ⟶ (((singularChainComplexFunctor C).obj R).obj X).X (n + 1) :=
  realizeAffineChain R s (standardPrism n)

theorem singularPrismGenerator_homotopy
    (R : C) {X : TopCat.{0}} {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    singularPrismGenerator R s ≫
        (((singularChainComplexFunctor C).obj R).obj X).d (n + 2) (n + 1) +
      realizeAffineChain R s
        (prismStd (q := n + 1) n (simplexBoundary (idSimplex (n + 1)))) =
      (TopCat.toSSet.obj X).ιChainComplex s -
        singularSubdivideGenerator R s := by
  have hprism :=
    boundary_prismStd (q := n + 1) (simplex (idSimplex (n + 1)))
  simp only [singularPrismGenerator, singularSubdivideGenerator,
    standardPrism, standardSubdivision]
  rw [← realizeAffineChain_boundary]
  have hreal := congrArg (realizeAffineChain R s) hprism
  simp [map_add, map_sub, boundary_simplex, realizeAffineSimplex_id] at hreal
  exact hreal

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

/-- Degreewise barycentric subdivision of singular chains. -/
noncomputable def singularSubdivisionHom
    (R : C) (X : TopCat.{0}) (n : ℕ) :
    (((singularChainComplexFunctor C).obj R).obj X).X n ⟶
      (((singularChainComplexFunctor C).obj R).obj X).X n :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R n).desc
    (Cofan.mk _ fun s => singularSubdivideGenerator R s)

@[reassoc (attr := simp)]
theorem ι_singularSubdivisionHom
    (R : C) (X : TopCat.{0}) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex s ≫ singularSubdivisionHom R X n =
      singularSubdivideGenerator R s :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R n).fac _ ⟨s⟩

/-- Degreewise prism operator on singular chains. -/
noncomputable def singularPrismHom
    (R : C) (X : TopCat.{0}) (n : ℕ) :
    (((singularChainComplexFunctor C).obj R).obj X).X n ⟶
      (((singularChainComplexFunctor C).obj R).obj X).X (n + 1) :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R n).desc
    (Cofan.mk _ fun s => singularPrismGenerator R s)

@[reassoc (attr := simp)]
theorem ι_singularPrismHom
    (R : C) (X : TopCat.{0}) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex s ≫ singularPrismHom R X n =
      singularPrismGenerator R s :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R n).fac _ ⟨s⟩

theorem singularSubdivideGenerator_d
    (R : C) {X : TopCat.{0}} {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    singularSubdivideGenerator R s ≫
        (((singularChainComplexFunctor C).obj R).obj X).d (n + 1) n =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) •
          singularSubdivideGenerator R ((TopCat.toSSet.obj X).δ i s) := by
  have hbound :
      boundary (standardSubdivision (n + 1)) =
        subdivideStd (q := n + 1) n
          (simplexBoundary (idSimplex (n + 1))) := by
    simpa [standardSubdivision, boundary_simplex] using
      boundary_subdivideStd (q := n + 1) (simplex (idSimplex (n + 1)))
  simp only [singularSubdivideGenerator]
  rw [← realizeAffineChain_boundary, hbound]
  simp only [simplexBoundary, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [realizeAffineChain_subdivideStd_simplex, reparametrizeSingularSimplex_id_face]

/-- Barycentric subdivision of singular chains, as a chain map. -/
noncomputable def singularSubdivision
    (R : C) (X : TopCat.{0}) :
    ((singularChainComplexFunctor C).obj R).obj X ⟶
      ((singularChainComplexFunctor C).obj R).obj X where
  f := singularSubdivisionHom R X
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst hij
    apply (TopCat.toSSet.obj X).chainComplex_hom_ext
    intro s
    calc
      (TopCat.toSSet.obj X).ιChainComplex s ≫
          singularSubdivisionHom R X (j + 1) ≫
            (((singularChainComplexFunctor C).obj R).obj X).d (j + 1) j =
          singularSubdivideGenerator R s ≫
            (((singularChainComplexFunctor C).obj R).obj X).d (j + 1) j := by
        rw [← Category.assoc, ι_singularSubdivisionHom]
      _ = ∑ i : Fin (j + 2),
            (-1 : ℤ) ^ (i : ℕ) •
              singularSubdivideGenerator R ((TopCat.toSSet.obj X).δ i s) :=
        singularSubdivideGenerator_d R s
      _ = (TopCat.toSSet.obj X).ιChainComplex s ≫
            (((singularChainComplexFunctor C).obj R).obj X).d (j + 1) j ≫
              singularSubdivisionHom R X j := by
        have hd :
            (TopCat.toSSet.obj X).ιChainComplex s ≫
                (((singularChainComplexFunctor C).obj R).obj X).d (j + 1) j =
              ∑ i : Fin (j + 2),
                (-1 : ℤ) ^ (i : ℕ) •
                  (TopCat.toSSet.obj X).ιChainComplex
                    ((TopCat.toSSet.obj X).δ i s) := by
          change _ ≫ ((TopCat.toSSet.obj X).chainComplex R).d (j + 1) j = _
          rw [SSet.ιChainComplex_d]
        rw [← Category.assoc, hd]
        refine Eq.trans ?_
          (Preadditive.sum_comp (s := Finset.univ)
            (fun i : Fin (j + 2) =>
              (-1 : ℤ) ^ (i : ℕ) •
                (TopCat.toSSet.obj X).ιChainComplex
                  ((TopCat.toSSet.obj X).δ i s))
            (singularSubdivisionHom R X j)).symm
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← ι_singularSubdivisionHom, ← Preadditive.zsmul_comp]
        rfl

end

end PlatonicSolids.SingularExcision
