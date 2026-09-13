/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.SingularSet
import PlatonicSolids.SingularExcision.AffineSubdivision

/-!
# Realization of finite affine simplices

Finite affine chains become singular chains by realizing a list of vertices
in a standard simplex as its barycentric affine map.
-/

open CategoryTheory
open scoped BigOperators Simplicial

namespace PlatonicSolids.SingularExcision

noncomputable section

/-- Barycentric realization of ordered vertices in a standard simplex. -/
def AffineSimplex.realize {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    C(stdSimplex ℝ (Fin (p + 1)), stdSimplex ℝ (Fin (q + 1))) where
  toFun x :=
    ⟨fun j ↦ ∑ i, x.1 i * (σ i).1 j, by
      constructor
      · intro j
        exact Finset.sum_nonneg fun i _ ↦
          mul_nonneg (x.2.1 i) ((σ i).2.1 j)
      · rw [Finset.sum_comm]
        calc
          ∑ i, ∑ j, x.1 i * (σ i).1 j =
              ∑ i, x.1 i * ∑ j, (σ i).1 j := by
                congr with i
                rw [Finset.mul_sum]
          _ = ∑ i, x.1 i := by
                congr with i
                rw [(σ i).2.2, mul_one]
          _ = 1 := x.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

@[simp]
theorem AffineSimplex.realize_apply {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (x : stdSimplex ℝ (Fin (p + 1))) (j : Fin (q + 1)) :
    (σ.realize x : Fin (q + 1) → ℝ) j =
      ∑ i, x.1 i * (σ i).1 j :=
  rfl

/-- Realization sends each standard vertex to the corresponding listed vertex. -/
@[simp]
theorem AffineSimplex.realize_vertex {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (i : Fin (p + 1)) :
    σ.realize (stdSimplex.vertex i) = σ i := by
  classical
  apply Subtype.ext
  funext j
  change ∑ k, (Pi.single i (1 : ℝ) : Fin (p + 1) → ℝ) k * (σ k).1 j =
    (σ i).1 j
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [Pi.single_eq_of_ne hki]
  · simp

/-- Reparametrize a singular simplex by a realized finite affine simplex. -/
noncomputable def reparametrizeSingularSimplex {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    (TopCat.toSSet.obj X) _⦋p⦌ :=
  (X.toSSetObjEquiv _).symm ((X.toSSetObjEquiv _ s).comp σ.realize)

@[simp]
theorem reparametrizeSingularSimplex_toContinuousMap
    {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    X.toSSetObjEquiv _ (reparametrizeSingularSimplex s σ) =
      (X.toSSetObjEquiv _ s).comp σ.realize := by
  simp [reparametrizeSingularSimplex]

/-- The signed barycentric subdivision chain of the standard interval. -/
def standardIntervalSubdivision :
    AffineChain (stdSimplex ℝ (Fin 2)) 1 :=
  edge (stdSimplex.vertex 0) stdSimplex.barycenter -
    edge (stdSimplex.vertex 1) stdSimplex.barycenter

/-- The standard interval subdivision has the original endpoint boundary. -/
theorem boundary_standardIntervalSubdivision :
    boundary standardIntervalSubdivision =
      vertex (stdSimplex.vertex (1 : Fin 2)) -
        vertex (stdSimplex.vertex (0 : Fin 2)) := by
  simp [standardIntervalSubdivision, boundary_edge]

/-- Universal affine prism for subdivision of the standard interval. -/
def standardIntervalPrism :
    AffineChain (stdSimplex ℝ (Fin 2)) 2 :=
  cone stdSimplex.barycenter
    (edge (stdSimplex.vertex 0) (stdSimplex.vertex 1) -
      standardIntervalSubdivision)

/-- The standard one-dimensional prism identity. -/
theorem boundary_standardIntervalPrism :
    boundary standardIntervalPrism =
      edge (stdSimplex.vertex 0) (stdSimplex.vertex 1) -
        standardIntervalSubdivision := by
  classical
  unfold standardIntervalPrism standardIntervalSubdivision
  simp only [map_sub]
  rw [boundary_cone_edge, boundary_cone_edge, boundary_cone_edge]
  simp only [map_sub, cone_vertex]
  abel

end

end PlatonicSolids.SingularExcision
