/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid

/-!
# Finite affine chains for singular excision

This file isolates the integral signs in barycentric subdivision from
the categorical singular-chain construction. An `AffineSimplex V n`
is an ordered list of `n + 1` vertices in `V`.

The cone convention is chosen so that
`∂ (cone v c) = c - cone v (∂ c)`. In dimension one this produces the
usual permutation formula `[a,m] - [b,m]` for subdivision of `[a,b]`.
-/

open scoped BigOperators

namespace PlatonicSolids.SingularExcision

noncomputable section

/-- An ordered affine `n`-simplex, represented by its vertices. -/
abbrev AffineSimplex (V : Type*) (n : ℕ) := Fin (n + 1) → V

/-- Finite integral chains of ordered affine simplices. -/
abbrev AffineChain (V : Type*) (n : ℕ) := AffineSimplex V n →₀ ℤ

/-- Delete vertex `i` from an ordered simplex. -/
def AffineSimplex.face {V : Type*} {n : ℕ}
    (σ : AffineSimplex V (n + 1)) (i : Fin (n + 2)) :
    AffineSimplex V n :=
  fun j ↦ σ (i.succAbove j)

/-- The chain consisting of one oriented simplex. -/
def simplex {V : Type*} {n : ℕ} (σ : AffineSimplex V n) :
    AffineChain V n :=
  Finsupp.single σ 1

/-- Boundary of one ordered affine simplex. -/
def simplexBoundary {V : Type*} {n : ℕ}
    (σ : AffineSimplex V (n + 1)) : AffineChain V n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • simplex (σ.face i)

/-- The integral boundary map on finite affine chains. -/
def boundary {V : Type*} {n : ℕ} :
    AffineChain V (n + 1) →+ AffineChain V n :=
  Finsupp.liftAddHom fun σ ↦
    (smulAddHom ℤ (AffineChain V n)).flip (simplexBoundary σ)

@[simp]
theorem boundary_simplex {V : Type*} {n : ℕ} (σ : AffineSimplex V (n + 1)) :
    boundary (simplex σ) = simplexBoundary σ := by
  simp [boundary, simplex]

/-- A vertex as a zero-chain. -/
def vertex {V : Type*} (v : V) : AffineChain V 0 :=
  simplex (fun _ ↦ v)

/-- The ordered edge `[a,b]`. -/
def edge {V : Type*} (a b : V) : AffineChain V 1 :=
  simplex (Fin.cases a fun _ ↦ b)

/-- The ordered triangle `[a,b,c]`. -/
def triangle {V : Type*} (a b c : V) : AffineChain V 2 :=
  simplex (Fin.cases a (Fin.cases b fun _ ↦ c))

/-- The boundary of an edge is its endpoint minus its startpoint. -/
theorem boundary_edge {V : Type*} (a b : V) :
    boundary (edge a b) = vertex b - vertex a := by
  classical
  let σ : AffineSimplex V 1 := Fin.cases a fun _ ↦ b
  have h0 : σ.face (0 : Fin 2) = (fun _ ↦ b) := by
    funext i
    fin_cases i
    rfl
  have h1 : σ.face (1 : Fin 2) = (fun _ ↦ a) := by
    funext i
    fin_cases i
    rfl
  rw [edge, boundary_simplex]
  simp [simplexBoundary, Fin.sum_univ_succ, h0, h1, σ, vertex]
  abel

/-- The low-dimensional oriented boundary formula for a triangle. -/
theorem boundary_triangle {V : Type*} (a b c : V) :
    boundary (triangle a b c) = edge b c - edge a c + edge a b := by
  classical
  let σ : AffineSimplex V 2 := Fin.cases a (Fin.cases b fun _ ↦ c)
  have h0 : σ.face (0 : Fin 3) = (Fin.cases b fun _ ↦ c) := by
    funext i
    fin_cases i <;> rfl
  have h1 : σ.face (1 : Fin 3) = (Fin.cases a fun _ ↦ c) := by
    funext i
    fin_cases i <;> rfl
  have h2 : σ.face (2 : Fin 3) = (Fin.cases a fun _ ↦ b) := by
    funext i
    fin_cases i <;> rfl
  rw [triangle, boundary_simplex]
  simp [simplexBoundary, Fin.sum_univ_succ, h0, h1, h2, σ, edge]
  abel

/-- Append an apex to the ordered vertices of a simplex. -/
def AffineSimplex.append {V : Type*} {n : ℕ}
    (σ : AffineSimplex V n) (v : V) : AffineSimplex V (n + 1) :=
  Fin.lastCases v σ

/-- Cone on one simplex, with the dimension-dependent orientation sign. -/
def simplexCone {V : Type*} {n : ℕ} (v : V) (σ : AffineSimplex V n) :
    AffineChain V (n + 1) :=
  (-1 : ℤ) ^ (n + 1) • simplex (σ.append v)

/-- Extend coning linearly to finite chains. -/
def cone {V : Type*} {n : ℕ} (v : V) :
    AffineChain V n →+ AffineChain V (n + 1) :=
  Finsupp.liftAddHom fun σ ↦
    (smulAddHom ℤ (AffineChain V (n + 1))).flip (simplexCone v σ)

@[simp]
theorem cone_simplex {V : Type*} {n : ℕ} (v : V) (σ : AffineSimplex V n) :
    cone v (simplex σ) = simplexCone v σ := by
  simp [cone, simplex]

theorem simplexCone_vertex {V : Type*} (v a : V) :
    simplexCone v (fun _ : Fin 1 ↦ a) = -edge a v := by
  unfold simplexCone edge
  norm_num
  congr 1
  funext i
  fin_cases i <;> rfl

theorem simplexCone_edge {V : Type*} (v a b : V) :
    simplexCone v (Fin.cases a fun _ ↦ b) = triangle a b v := by
  unfold simplexCone triangle
  norm_num
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp]
theorem cone_vertex {V : Type*} (v a : V) :
    cone v (vertex a) = -edge a v := by
  rw [vertex, cone_simplex, simplexCone_vertex]

@[simp]
theorem cone_edge {V : Type*} (v a b : V) :
    cone v (edge a b) = triangle a b v := by
  rw [edge, cone_simplex, simplexCone_edge]

/-- The cone identity on zero-simplices. -/
theorem boundary_cone_vertex {V : Type*} (v a : V) :
    boundary (cone v (vertex a)) = vertex a - vertex v := by
  classical
  rw [cone_vertex]
  rw [map_neg, boundary_edge]
  abel

/-- The cone identity on edges. -/
theorem boundary_cone_edge {V : Type*} (v a b : V) :
    boundary (cone v (edge a b)) =
      edge a b - cone v (vertex b - vertex a) := by
  classical
  rw [cone_edge, map_sub, cone_vertex, cone_vertex]
  rw [boundary_triangle]
  abel

/-- The affine barycenter of the vertices of a simplex in a vector space. -/
def AffineSimplex.barycenter {V : Type*} [AddCommGroup V] [Module ℚ V]
    {n : ℕ} (σ : AffineSimplex V n) : V :=
  (n + 1 : ℚ)⁻¹ • ∑ i, σ i

/-- The midpoint used by one-dimensional barycentric subdivision. -/
def midpoint {V : Type*} [AddCommGroup V] [Module ℚ V] (a b : V) : V :=
  (2 : ℚ)⁻¹ • (a + b)

theorem barycenter_edge {V : Type*} [AddCommGroup V] [Module ℚ V] (a b : V) :
    AffineSimplex.barycenter
      ((Fin.cases a fun _ ↦ b) : AffineSimplex V 1) = midpoint a b := by
  norm_num [AffineSimplex.barycenter, midpoint, Fin.sum_univ_succ]

/-- Barycentric subdivision of an oriented affine interval.

The expression `[a,m] - [b,m]` is the signed-permutation form of
`[a,m] + [m,b]`; no quotient by affine reparametrization is taken here.
-/
def subdivideInterval {V : Type*} [AddCommGroup V] [Module ℚ V]
    (a b : V) : AffineChain V 1 :=
  edge a (midpoint a b) - edge b (midpoint a b)

/-- Subdivision is a chain map on the one-dimensional checkpoint. -/
theorem boundary_subdivideInterval {V : Type*} [AddCommGroup V] [Module ℚ V]
    (a b : V) :
    boundary (subdivideInterval a b) = vertex b - vertex a := by
  simp [subdivideInterval, boundary_edge]

/-- The universal one-dimensional prism between an edge and its subdivision. -/
def intervalPrism {V : Type*} [AddCommGroup V] [Module ℚ V]
    (a b : V) : AffineChain V 2 :=
  cone (midpoint a b) (edge a b - subdivideInterval a b)

/-- The prism identity `∂P = id - Sd` for an affine interval. -/
theorem boundary_intervalPrism {V : Type*} [AddCommGroup V] [Module ℚ V]
    (a b : V) :
    boundary (intervalPrism a b) = edge a b - subdivideInterval a b := by
  classical
  unfold intervalPrism subdivideInterval
  simp only [map_sub]
  rw [boundary_cone_edge, boundary_cone_edge, boundary_cone_edge]
  simp only [map_sub, cone_vertex]
  abel

end

end PlatonicSolids.SingularExcision
