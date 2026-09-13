/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.LinearAlgebra.Finsupp.Pi
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

/-- Pairing against a `FunOnFinite` pushforward is the original pairing. -/
lemma sum_linearMap_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (s : α → ℝ) (t : β → ℝ) :
    ∑ y : β, FunOnFinite.linearMap ℝ ℝ f s y * t y = ∑ x : α, s x * t (f x) := by
  simp_rw [FunOnFinite.linearMap_apply_apply]
  calc
    ∑ y : β, (∑ x ∈ Finset.univ.filter (fun x ↦ f x = y), s x) * t y =
        ∑ y : β, ∑ x ∈ Finset.univ.filter (fun x ↦ f x = y), s x * t y := by
      simp_rw [Finset.sum_mul]
    _ = ∑ y : β, ∑ x ∈ Finset.univ.filter (fun x ↦ f x = y), s x * t (f x) := by
      refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x hx ↦ ?_
      rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x : α, s x * t (f x) :=
      Finset.sum_fiberwise Finset.univ f (fun x ↦ s x * t (f x))

/-- Realization commutes with deleting a vertex. -/
theorem AffineSimplex.realize_face {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) (p + 1))
    (i : Fin (p + 2)) (x : stdSimplex ℝ (Fin (p + 1))) :
    σ.realize (stdSimplex.map i.succAbove x) = (σ.face i).realize x := by
  classical
  apply Subtype.ext
  funext j
  simpa [stdSimplex.map_coe] using
    sum_linearMap_mul i.succAbove x.1 (fun k ↦ (σ k).1 j)

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

/-- Faces of a reparametrized simplex are reparametrizations of the faces. -/
theorem reparametrizeSingularSimplex_face {X : TopCat.{0}} {p q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) (p + 1))
    (i : Fin (p + 2)) :
    reparametrizeSingularSimplex s (σ.face i) =
      (TopCat.toSSet.obj X).δ i (reparametrizeSingularSimplex s σ) := by
  apply (X.toSSetObjEquiv _).injective
  ext x
  rw [reparametrizeSingularSimplex_toContinuousMap,
    TopCat.toSSetObjEquiv_δ_apply,
    reparametrizeSingularSimplex_toContinuousMap]
  simp [AffineSimplex.realize_face]

/-- The identity affine simplex on a standard simplex. -/
def idSimplex (n : ℕ) :
    AffineSimplex (stdSimplex ℝ (Fin (n + 1))) n :=
  stdSimplex.vertex

/-- The identity affine simplex realizes as the identity map. -/
@[simp]
theorem realize_idSimplex (n : ℕ) :
    (idSimplex n).realize = ContinuousMap.id _ := by
  classical
  ext x j
  change ∑ i, x.1 i * (stdSimplex.vertex i : Fin (n + 1) → ℝ) j = x.1 j
  simp_rw [stdSimplex.vertex_coe]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij.symm, mul_zero]
  · simp

/-- Reparametrizing by the identity simplex is the identity. -/
@[simp]
theorem reparametrizeSingularSimplex_id {X : TopCat.{0}} {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    reparametrizeSingularSimplex s (idSimplex n) = s := by
  apply (X.toSSetObjEquiv _).injective
  rw [reparametrizeSingularSimplex_toContinuousMap, realize_idSimplex]
  ext x
  simp

/-- Reparametrizing by a face of the identity simplex is an ordinary face. -/
theorem reparametrizeSingularSimplex_id_face {X : TopCat.{0}} {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (i : Fin (n + 2)) :
    reparametrizeSingularSimplex s ((idSimplex (n + 1)).face i) =
      (TopCat.toSSet.obj X).δ i s := by
  rw [reparametrizeSingularSimplex_face, reparametrizeSingularSimplex_id]

/-- Geometric barycenter of an affine simplex inside a standard simplex. -/
def AffineSimplex.stdBarycenter {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    stdSimplex ℝ (Fin (q + 1)) :=
  σ.realize stdSimplex.barycenter

/-- Realization is functorial for vertex-wise maps coming from an
ambient realized simplex. -/
theorem AffineSimplex.realize_map {p q k : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (ρ : AffineSimplex (stdSimplex ℝ (Fin (p + 1))) k) :
    (AffineSimplex.map σ.realize ρ).realize = σ.realize.comp ρ.realize := by
  classical
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  ext j
  change (∑ i, x.1 i * ∑ m, (ρ i).1 m * (σ m).1 j) =
    ∑ m, (∑ i, x.1 i * (ρ i).1 m) * (σ m).1 j
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem AffineSimplex.stdBarycenter_map {p q k : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (ρ : AffineSimplex (stdSimplex ℝ (Fin (p + 1))) k) :
    AffineSimplex.stdBarycenter (AffineSimplex.map σ.realize ρ) =
      σ.realize (AffineSimplex.stdBarycenter ρ) := by
  simp [AffineSimplex.stdBarycenter, AffineSimplex.realize_map]

@[simp]
theorem AffineSimplex.map_realize_idSimplex {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    AffineSimplex.map σ.realize (idSimplex p) = σ := by
  funext i
  simp [AffineSimplex.map, idSimplex]

theorem reparametrizeSingularSimplex_map {X : TopCat.{0}} {p q k : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋q⦌)
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (ρ : AffineSimplex (stdSimplex ℝ (Fin (p + 1))) k) :
    reparametrizeSingularSimplex s (AffineSimplex.map σ.realize ρ) =
      reparametrizeSingularSimplex (reparametrizeSingularSimplex s σ) ρ := by
  apply (X.toSSetObjEquiv _).injective
  rw [reparametrizeSingularSimplex_toContinuousMap,
    reparametrizeSingularSimplex_toContinuousMap,
    reparametrizeSingularSimplex_toContinuousMap,
    AffineSimplex.realize_map]
  ext x
  simp [ContinuousMap.comp_assoc]

/-- Barycentric subdivision of affine chains in a standard simplex. -/
def subdivideStd {q : ℕ} :
    (n : ℕ) → AffineChain (stdSimplex ℝ (Fin (q + 1))) n →+
      AffineChain (stdSimplex ℝ (Fin (q + 1))) n :=
  subdivide AffineSimplex.stdBarycenter

/-- Prism operator for affine chains in a standard simplex. -/
def prismStd {q : ℕ} :
    (n : ℕ) → AffineChain (stdSimplex ℝ (Fin (q + 1))) n →+
      AffineChain (stdSimplex ℝ (Fin (q + 1))) (n + 1) :=
  prism AffineSimplex.stdBarycenter

theorem boundary_subdivideStd {q n : ℕ}
    (c : AffineChain (stdSimplex ℝ (Fin (q + 1))) (n + 1)) :
    boundary (subdivideStd (q := q) (n + 1) c) =
      subdivideStd (q := q) n (boundary c) :=
  boundary_subdivide AffineSimplex.stdBarycenter n c

theorem boundary_prismStd {q n : ℕ}
    (c : AffineChain (stdSimplex ℝ (Fin (q + 1))) (n + 1)) :
    boundary (prismStd (q := q) (n + 1) c) +
        prismStd (q := q) n (boundary c) =
      c - subdivideStd (q := q) (n + 1) c :=
  boundary_prism AffineSimplex.stdBarycenter n c

/-- Subdivision of the identity simplex. -/
def standardSubdivision (n : ℕ) :
    AffineChain (stdSimplex ℝ (Fin (n + 1))) n :=
  subdivideStd (q := n) n (simplex (idSimplex n))

/-- Prism of the identity simplex. -/
def standardPrism (n : ℕ) :
    AffineChain (stdSimplex ℝ (Fin (n + 1))) (n + 1) :=
  prismStd (q := n) n (simplex (idSimplex n))

theorem AffineChain.map_subdivideStd {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (n : ℕ) (c : AffineChain (stdSimplex ℝ (Fin (p + 1))) n) :
    AffineChain.map σ.realize (subdivideStd (q := p) n c) =
      subdivideStd (q := q) n (AffineChain.map σ.realize c) :=
  AffineChain.map_subdivide
    AffineSimplex.stdBarycenter AffineSimplex.stdBarycenter σ.realize
    (fun ρ ↦ (AffineSimplex.stdBarycenter_map σ ρ).symm) n c

theorem AffineChain.map_prismStd {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p)
    (n : ℕ) (c : AffineChain (stdSimplex ℝ (Fin (p + 1))) n) :
    AffineChain.map σ.realize (prismStd (q := p) n c) =
      prismStd (q := q) n (AffineChain.map σ.realize c) :=
  AffineChain.map_prism
    AffineSimplex.stdBarycenter AffineSimplex.stdBarycenter σ.realize
    (fun ρ ↦ (AffineSimplex.stdBarycenter_map σ ρ).symm) n c

theorem AffineChain.map_standardSubdivision {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    AffineChain.map σ.realize (standardSubdivision p) =
      subdivideStd (q := q) p (simplex σ) := by
  simp [standardSubdivision, AffineChain.map_subdivideStd]

theorem AffineChain.map_standardPrism {p q : ℕ}
    (σ : AffineSimplex (stdSimplex ℝ (Fin (q + 1))) p) :
    AffineChain.map σ.realize (standardPrism p) =
      prismStd (q := q) p (simplex σ) := by
  simp [standardPrism, AffineChain.map_prismStd]

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
