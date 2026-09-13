/-
Copyright (c) 2026 Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.Data.Finsupp.Ext
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

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

set_option maxHeartbeats 800000

/-- An ordered affine `n`-simplex, represented by its vertices. -/
abbrev AffineSimplex (V : Type*) (n : ℕ) := Fin (n + 1) → V

/-- Finite integral chains of ordered affine simplices. -/
abbrev AffineChain (V : Type*) (n : ℕ) := AffineSimplex V n →₀ ℤ

lemma AffineChain.eq_of_single {V : Type*} {n : ℕ} {M : Type*} [AddCommGroup M]
    (f g : AffineChain V n →+ M) (c : AffineChain V n)
    (h : ∀ σ z, f (Finsupp.single σ z) = g (Finsupp.single σ z)) :
    f c = g c :=
  DFunLike.congr_fun (Finsupp.addHom_ext h) c

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

/-- Deleting the appended last vertex recovers the original simplex. -/
@[simp]
lemma AffineSimplex.append_face_last {V : Type*} {n : ℕ}
    (σ : AffineSimplex V n) (v : V) :
    (σ.append v).face (Fin.last (n + 1)) = σ := by
  funext i
  simp [AffineSimplex.face, AffineSimplex.append,
    Fin.succAbove_last_apply]

/-- Deleting an original vertex commutes with appending a last vertex. -/
@[simp]
lemma AffineSimplex.append_face_castSucc {V : Type*} {n : ℕ}
    (σ : AffineSimplex V (n + 1)) (v : V) (i : Fin (n + 2)) :
    (σ.append v).face i.castSucc = (σ.face i).append v := by
  funext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · simp [AffineSimplex.face, AffineSimplex.append]
  · simp [AffineSimplex.face, AffineSimplex.append,
      Fin.castSucc_succAbove_castSucc]

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

/-- Boundary of a cone on a positive-dimensional simplex. -/
theorem boundary_simplexCone {V : Type*} {n : ℕ}
    (v : V) (σ : AffineSimplex V (n + 1)) :
    boundary (simplexCone v σ) =
      simplex σ - cone v (simplexBoundary σ) := by
  classical
  rw [simplexCone, map_zsmul, boundary_simplex, simplexBoundary]
  rw [Fin.sum_univ_castSucc]
  simp only [AffineSimplex.append_face_castSucc,
    AffineSimplex.append_face_last, Fin.val_castSucc, Fin.val_last]
  simp only [simplexBoundary]
  rw [map_sum]
  simp_rw [map_zsmul, cone_simplex, simplexCone]
  simp only [Nat.add_assoc, Nat.reduceAdd, smul_add, Finset.smul_sum]
  simp_rw [smul_smul]
  have hsign : (-1 : ℤ) ^ (n + 2) * (-1 : ℤ) ^ (n + 2) = 1 := by
    rw [← pow_add, show n + 2 + (n + 2) = 2 * (n + 2) by omega, pow_mul]
    norm_num
  rw [hsign, one_smul]
  rw [sub_eq_add_neg]
  rw [add_comm (∑ x : Fin (n + 2),
    ((-1 : ℤ) ^ (n + 2) * (-1 : ℤ) ^ (x : ℕ)) •
      simplex ((σ.face x).append v)) (simplex σ)]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← neg_smul]
  congr 1
  have hnext : (-1 : ℤ) ^ (n + 2) = -((-1 : ℤ) ^ (n + 1)) := by
    rw [show n + 2 = Nat.succ (n + 1) by omega, pow_succ]
    ring
  rw [hnext]
  ring

/-- Boundary of a cone on any positive-dimensional affine chain. -/
theorem boundary_cone {V : Type*} {n : ℕ}
    (v : V) (c : AffineChain V (n + 1)) :
    boundary (cone v c) = c - cone v (boundary c) := by
  classical
  refine AffineChain.eq_of_single
    (boundary.comp (cone v))
    (AddMonoidHom.id _ - (cone v).comp boundary) c ?_
  intro σ z
  change boundary (cone v (Finsupp.single σ z)) =
    Finsupp.single σ z - cone v (boundary (Finsupp.single σ z))
  rw [show Finsupp.single σ z = z • simplex σ by simp [simplex]]
  simp [map_zsmul, cone_simplex, boundary_simplexCone, boundary_simplex, smul_sub]

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

/-- The first simplicial identity, as an equality of ordered faces. -/
lemma AffineSimplex.face_face {V : Type*} {n : ℕ}
    (σ : AffineSimplex V (n + 2)) {i j : Fin (n + 2)} (hij : i ≤ j) :
    (σ.face j.succ).face i = (σ.face i.castSucc).face j := by
  funext k
  simp only [AffineSimplex.face]
  congr 1
  change j.succ.succAbove (i.succAbove k) =
    i.castSucc.succAbove (j.succAbove k)
  dsimp [Fin.succAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> · simp at * <;> lia

/-- The signed sum of coefficients of a finite affine chain. -/
def coeffSum {V : Type*} {n : ℕ} : AffineChain V n →+ ℤ :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

@[simp]
lemma coeffSum_single {V : Type*} {n : ℕ} (σ : AffineSimplex V n) (z : ℤ) :
    coeffSum (Finsupp.single σ z) = z := by
  simp [coeffSum]

@[simp]
lemma coeffSum_simplex {V : Type*} {n : ℕ} (σ : AffineSimplex V n) :
    coeffSum (simplex σ) = 1 := by
  simp [simplex]

@[simp]
lemma coeffSum_vertex {V : Type*} (v : V) :
    coeffSum (vertex v) = 1 := by
  simp [vertex]

lemma coeffSum_simplexBoundary_one {V : Type*} (σ : AffineSimplex V 1) :
    coeffSum (simplexBoundary σ) = 0 := by
  rw [simplexBoundary, Fin.sum_univ_two]
  simp [coeffSum_simplex]

/-- Cone identity in dimension zero: the extra term is the augmentation. -/
theorem boundary_cone_zero {V : Type*} (v : V) (c : AffineChain V 0) :
    boundary (cone v c) = c - coeffSum c • vertex v := by
  classical
  refine AffineChain.eq_of_single
    (boundary.comp (cone v))
    (AddMonoidHom.id _ -
      ((smulAddHom ℤ (AffineChain V 0)).flip (vertex v)).comp coeffSum) c ?_
  intro σ z
  have hσ : σ = fun _ : Fin 1 ↦ σ 0 := by
    funext i
    fin_cases i
    rfl
  change boundary (cone v (Finsupp.single σ z)) =
    Finsupp.single σ z - coeffSum (Finsupp.single σ z) • vertex v
  have hsingle : Finsupp.single σ z = z • vertex (σ 0) := by
    rw [hσ, vertex, simplex, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsingle, map_zsmul, cone_vertex, map_zsmul, map_neg, boundary_edge,
    map_zsmul, coeffSum_vertex]
  module

/-- Double faces cancel: `∂ ∘ ∂ = 0` on a generator. -/
theorem boundary_simplexBoundary {V : Type*} {n : ℕ}
    (σ : AffineSimplex V (n + 2)) :
    boundary (simplexBoundary σ) = 0 := by
  classical
  simp only [simplexBoundary, map_sum, map_zsmul, boundary_simplex]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_product']
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨j, i⟩ hij ⟨j', i'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨j', i'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(i'.pred ?_, Fin.castSucc j'), ?_, ?_⟩
    · exact_mod_cast hij'.ne_zero
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨j, i⟩ hij
    simp only [← neg_smul]
    congr 1
    · simp [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_comm]
    · have hij' : i ≤ j.castSucc := by
        simpa [S, Fin.le_iff_val_le_val] using hij
      have hlt : (i : ℕ) < n + 2 :=
        Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hij') j.isLt
      have hcast : (i.castLT hlt).castSucc = i := by
        ext
        simp
      have hface :
          (σ.face j.succ).face (i.castLT hlt) = (σ.face i).face j := by
        have := AffineSimplex.face_face (σ := σ)
          (i := i.castLT hlt) (j := j) (by
            simpa [Fin.le_iff_val_le_val, Fin.val_castLT] using hij')
        rwa [hcast] at this
      congr 1
      simpa [φ] using hface.symm

theorem boundary_boundary {V : Type*} {n : ℕ} (c : AffineChain V (n + 2)) :
    boundary (boundary c) = 0 := by
  classical
  refine AffineChain.eq_of_single
    (boundary.comp boundary) 0 c ?_
  intro σ z
  change boundary (boundary (Finsupp.single σ z)) = 0
  rw [show Finsupp.single σ z = z • simplex σ by simp [simplex]]
  simp [map_zsmul, boundary_simplex, boundary_simplexBoundary]

/-- Barycentric subdivision of finite affine chains, coning on a
chosen point of each simplex (classically the barycenter). -/
def subdivide {V : Type*} (b : {n : ℕ} → AffineSimplex V n → V) :
    (n : ℕ) → AffineChain V n →+ AffineChain V n
  | 0 => AddMonoidHom.id _
  | n + 1 =>
      Finsupp.liftAddHom fun σ =>
        (smulAddHom ℤ (AffineChain V (n + 1))).flip
          (cone (b σ) (subdivide b n (simplexBoundary σ)))

@[simp]
theorem subdivide_zero {V : Type*} (b : {n : ℕ} → AffineSimplex V n → V)
    (c : AffineChain V 0) :
    subdivide b 0 c = c :=
  rfl

theorem subdivide_single {V : Type*} (b : {n : ℕ} → AffineSimplex V n → V)
    {n : ℕ} (σ : AffineSimplex V (n + 1)) (z : ℤ) :
    subdivide b (n + 1) (Finsupp.single σ z) =
      z • cone (b σ) (subdivide b n (simplexBoundary σ)) := by
  simp [subdivide]

theorem subdivide_simplex {V : Type*} (b : {n : ℕ} → AffineSimplex V n → V)
    {n : ℕ} (σ : AffineSimplex V (n + 1)) :
    subdivide b (n + 1) (simplex σ) =
      cone (b σ) (subdivide b n (simplexBoundary σ)) := by
  simpa [simplex] using subdivide_single b σ 1

/-- Subdivision commutes with the boundary. -/
theorem boundary_subdivide {V : Type*} (b : {n : ℕ} → AffineSimplex V n → V)
    (n : ℕ) (c : AffineChain V (n + 1)) :
    boundary (subdivide b (n + 1) c) = subdivide b n (boundary c) := by
  induction n with
  | zero =>
      induction c using Finsupp.induction with
      | zero => simp
      | single_add σ z c _ _ ih =>
          rw [map_add, map_add, map_add, ih]
          rw [subdivide_single b, map_zsmul, subdivide_zero]
          rw [boundary_cone_zero, coeffSum_simplexBoundary_one, zero_smul,
            sub_zero]
          rw [show Finsupp.single σ z = z • simplex σ by simp [simplex]]
          simp [map_zsmul, boundary_simplex]
  | succ n ih =>
      induction c using Finsupp.induction with
      | zero => simp
      | single_add σ z c _ _ ihc =>
          rw [map_add, map_add, map_add, ihc]
          rw [subdivide_single b, map_zsmul, boundary_cone, ih,
            boundary_simplexBoundary]
          simp only [map_zero, sub_zero]
          rw [show Finsupp.single σ z = z • simplex σ by simp [simplex]]
          simp [map_zsmul, boundary_simplex]

/-- The prism operator: a chain homotopy from the identity to subdivision. -/
def prism {V : Type*} (b : {n : ℕ} → AffineSimplex V n → V) :
    (n : ℕ) → AffineChain V n →+ AffineChain V (n + 1)
  | 0 => 0
  | n + 1 =>
      Finsupp.liftAddHom fun σ =>
        (smulAddHom ℤ (AffineChain V (n + 2))).flip
          (cone (b σ)
            (simplex σ - subdivide b (n + 1) (simplex σ) -
              prism b n (simplexBoundary σ)))

@[simp]
theorem prism_zero {V : Type*} (b : {n : ℕ} → AffineSimplex V n → V)
    (c : AffineChain V 0) :
    prism b 0 c = 0 :=
  rfl

theorem prism_single {V : Type*} (b : {n : ℕ} → AffineSimplex V n → V)
    {n : ℕ} (σ : AffineSimplex V (n + 1)) (z : ℤ) :
    prism b (n + 1) (Finsupp.single σ z) =
      z • cone (b σ)
        (simplex σ - subdivide b (n + 1) (simplex σ) -
          prism b n (simplexBoundary σ)) := by
  simp [prism, smul_sub]

/-- The prism identity `∂T + T∂ = id - Sd`. -/
theorem boundary_prism {V : Type*} (b : {n : ℕ} → AffineSimplex V n → V)
    (n : ℕ) (c : AffineChain V (n + 1)) :
    boundary (prism b (n + 1) c) + prism b n (boundary c) =
      c - subdivide b (n + 1) c := by
  induction n with
  | zero =>
      induction c using Finsupp.induction with
      | zero => simp
      | single_add σ z c _ _ ih =>
          have hsingle :
              boundary (prism b 1 (Finsupp.single σ z)) +
                prism b 0 (boundary (Finsupp.single σ z)) =
              Finsupp.single σ z - subdivide b 1 (Finsupp.single σ z) := by
            rw [prism_single, map_zsmul]
            simp only [prism_zero, sub_zero, add_zero]
            have hw :
                boundary (simplex σ - subdivide b 1 (simplex σ)) = 0 := by
              rw [map_sub, boundary_subdivide, boundary_simplex,
                subdivide_zero]
              abel
            rw [boundary_cone, hw]
            simp only [map_zero, sub_zero]
            rw [show Finsupp.single σ z = z • simplex σ by
              rw [simplex, Finsupp.smul_single, smul_eq_mul, mul_one]]
            simp [map_zsmul]
            module
          simp only [map_add]
          calc
            _ = (boundary (prism b 1 (Finsupp.single σ z)) +
                  prism b 0 (boundary (Finsupp.single σ z))) +
                (boundary (prism b 1 c) + prism b 0 (boundary c)) := by abel
            _ = (Finsupp.single σ z - subdivide b 1 (Finsupp.single σ z)) +
                (c - subdivide b 1 c) := by rw [hsingle, ih]
            _ = _ := by abel
  | succ n ih =>
      induction c using Finsupp.induction with
      | zero => simp
      | single_add σ z c _ _ ihc =>
          have hsingle :
              boundary (prism b (n + 2) (Finsupp.single σ z)) +
                prism b (n + 1) (boundary (Finsupp.single σ z)) =
              Finsupp.single σ z - subdivide b (n + 2) (Finsupp.single σ z) := by
            rw [prism_single, map_zsmul]
            have hw :
                boundary (simplex σ - subdivide b (n + 2) (simplex σ) -
                    prism b (n + 1) (simplexBoundary σ)) = 0 := by
              have hih := ih (simplexBoundary σ)
              have hsd := boundary_subdivide b (n + 1) (simplex σ)
              rw [map_sub, map_sub, hsd, boundary_simplex]
              simp [boundary_simplexBoundary] at hih
              rw [hih]
              abel
            rw [boundary_cone, hw]
            simp only [map_zero, sub_zero]
            rw [show Finsupp.single σ z = z • simplex σ by
              rw [simplex, Finsupp.smul_single, smul_eq_mul, mul_one]]
            simp [map_zsmul, boundary_simplex]
            module
          simp only [map_add]
          calc
            _ = (boundary (prism b (n + 2) (Finsupp.single σ z)) +
                  prism b (n + 1) (boundary (Finsupp.single σ z))) +
                (boundary (prism b (n + 2) c) +
                  prism b (n + 1) (boundary c)) := by abel
            _ = (Finsupp.single σ z - subdivide b (n + 2) (Finsupp.single σ z)) +
                (c - subdivide b (n + 2) c) := by rw [hsingle, ihc]
            _ = _ := by abel

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

/-- Push vertices of an ordered simplex forward along a function. -/
def AffineSimplex.map {V W : Type*} {n : ℕ} (f : V → W)
    (σ : AffineSimplex V n) : AffineSimplex W n :=
  f ∘ σ

@[simp]
theorem AffineSimplex.map_apply {V W : Type*} {n : ℕ} (f : V → W)
    (σ : AffineSimplex V n) (i : Fin (n + 1)) :
    AffineSimplex.map f σ i = f (σ i) :=
  rfl

@[simp]
theorem AffineSimplex.map_id {V : Type*} {n : ℕ} (σ : AffineSimplex V n) :
    AffineSimplex.map id σ = σ :=
  rfl

@[simp]
theorem AffineSimplex.map_comp {U V W : Type*} {n : ℕ}
    (g : V → W) (f : U → V) (σ : AffineSimplex U n) :
    AffineSimplex.map g (AffineSimplex.map f σ) =
      AffineSimplex.map (g ∘ f) σ :=
  rfl

@[simp]
theorem AffineSimplex.map_face {V W : Type*} {n : ℕ} (f : V → W)
    (σ : AffineSimplex V (n + 1)) (i : Fin (n + 2)) :
    AffineSimplex.map f (σ.face i) = (AffineSimplex.map f σ).face i :=
  rfl

@[simp]
theorem AffineSimplex.map_append {V W : Type*} {n : ℕ} (f : V → W)
    (σ : AffineSimplex V n) (v : V) :
    AffineSimplex.map f (σ.append v) = (AffineSimplex.map f σ).append (f v) := by
  funext i
  refine Fin.lastCases ?_ (fun _ ↦ ?_) i
  · simp [AffineSimplex.map, AffineSimplex.append]
  · simp [AffineSimplex.map, AffineSimplex.append]

/-- Push a finite affine chain forward along a function of vertices. -/
def AffineChain.map {V W : Type*} (f : V → W) {n : ℕ} :
    AffineChain V n →+ AffineChain W n :=
  Finsupp.mapDomain.addMonoidHom (AffineSimplex.map f)

@[simp]
theorem AffineChain.map_single {V W : Type*} (f : V → W) {n : ℕ}
    (σ : AffineSimplex V n) (z : ℤ) :
    AffineChain.map f (Finsupp.single σ z) =
      Finsupp.single (AffineSimplex.map f σ) z := by
  simp [AffineChain.map, Finsupp.mapDomain_single]

@[simp]
theorem AffineChain.map_simplex {V W : Type*} (f : V → W) {n : ℕ}
    (σ : AffineSimplex V n) :
    AffineChain.map f (simplex σ) = simplex (AffineSimplex.map f σ) := by
  simp [simplex]

@[simp]
theorem AffineChain.map_vertex {V W : Type*} (f : V → W) (v : V) :
    AffineChain.map f (vertex v) = vertex (f v) := by
  simp [vertex, AffineSimplex.map]
  rfl

theorem AffineChain.map_simplexBoundary {V W : Type*} (f : V → W) {n : ℕ}
    (σ : AffineSimplex V (n + 1)) :
    AffineChain.map f (simplexBoundary σ) =
      simplexBoundary (AffineSimplex.map f σ) := by
  simp [simplexBoundary, map_sum, map_zsmul]

theorem AffineChain.map_boundary {V W : Type*} (f : V → W) {n : ℕ}
    (c : AffineChain V (n + 1)) :
    AffineChain.map f (boundary c) = boundary (AffineChain.map f c) := by
  refine AffineChain.eq_of_single
    ((AffineChain.map f).comp boundary)
    (boundary.comp (AffineChain.map f)) c ?_
  intro σ z
  change AffineChain.map f (boundary (Finsupp.single σ z)) =
    boundary (AffineChain.map f (Finsupp.single σ z))
  rw [show Finsupp.single σ z = z • simplex σ by simp [simplex]]
  simp [map_zsmul, boundary_simplex, AffineChain.map_simplexBoundary]

theorem AffineChain.map_simplexCone {V W : Type*} (f : V → W) {n : ℕ}
    (v : V) (σ : AffineSimplex V n) :
    AffineChain.map f (simplexCone v σ) =
      simplexCone (f v) (AffineSimplex.map f σ) := by
  simp [simplexCone, map_zsmul, AffineSimplex.map_append]

theorem AffineChain.map_cone {V W : Type*} (f : V → W) {n : ℕ}
    (v : V) (c : AffineChain V n) :
    AffineChain.map f (cone v c) = cone (f v) (AffineChain.map f c) := by
  refine AffineChain.eq_of_single
    ((AffineChain.map f).comp (cone v))
    ((cone (f v)).comp (AffineChain.map f)) c ?_
  intro σ z
  change AffineChain.map f (cone v (Finsupp.single σ z)) =
    cone (f v) (AffineChain.map f (Finsupp.single σ z))
  rw [show Finsupp.single σ z = z • simplex σ by simp [simplex]]
  simp [map_zsmul, cone_simplex, AffineChain.map_simplexCone]

/-- Subdivision is natural for maps that send chosen cone points to
chosen cone points. -/
theorem AffineChain.map_subdivide {V W : Type*}
    (bV : {n : ℕ} → AffineSimplex V n → V)
    (bW : {n : ℕ} → AffineSimplex W n → W) (f : V → W)
    (hb : ∀ {n : ℕ} (σ : AffineSimplex V n),
      f (bV σ) = bW (AffineSimplex.map f σ))
    (n : ℕ) (c : AffineChain V n) :
    AffineChain.map f (subdivide bV n c) =
      subdivide bW n (AffineChain.map f c) := by
  induction n with
  | zero => simp
  | succ n ih =>
      refine AffineChain.eq_of_single
        ((AffineChain.map f).comp (subdivide bV (n + 1)))
        ((subdivide bW (n + 1)).comp (AffineChain.map f)) c ?_
      intro σ z
      change AffineChain.map f (subdivide bV (n + 1) (Finsupp.single σ z)) =
        subdivide bW (n + 1) (AffineChain.map f (Finsupp.single σ z))
      rw [subdivide_single, AffineChain.map_single, subdivide_single, map_zsmul,
        AffineChain.map_cone, ih, AffineChain.map_simplexBoundary, hb]

/-- The prism is natural for the same cone-point maps. -/
theorem AffineChain.map_prism {V W : Type*}
    (bV : {n : ℕ} → AffineSimplex V n → V)
    (bW : {n : ℕ} → AffineSimplex W n → W) (f : V → W)
    (hb : ∀ {n : ℕ} (σ : AffineSimplex V n),
      f (bV σ) = bW (AffineSimplex.map f σ))
    (n : ℕ) (c : AffineChain V n) :
    AffineChain.map f (prism bV n c) =
      prism bW n (AffineChain.map f c) := by
  induction n with
  | zero => simp
  | succ n ih =>
      refine AffineChain.eq_of_single
        ((AffineChain.map f).comp (prism bV (n + 1)))
        ((prism bW (n + 1)).comp (AffineChain.map f)) c ?_
      intro σ z
      change AffineChain.map f (prism bV (n + 1) (Finsupp.single σ z)) =
        prism bW (n + 1) (AffineChain.map f (Finsupp.single σ z))
      rw [prism_single, AffineChain.map_single, prism_single, map_zsmul,
        AffineChain.map_cone]
      simp [map_sub, AffineChain.map_subdivide bV bW f hb,
        ih, AffineChain.map_simplexBoundary, hb]

lemma mem_support_simplexCone {V : Type*} {n : ℕ} (v : V)
    (σ : AffineSimplex V n) {τ : AffineSimplex V (n + 1)}
    (hτ : τ ∈ (simplexCone v σ).support) :
    τ = σ.append v := by
  have hz : (-1 : ℤ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by decide)
  simpa [simplexCone, simplex, Finsupp.support_smul_eq hz,
    Finsupp.support_single_ne_zero _ (one_ne_zero (α := ℤ))] using hτ

lemma cone_single {V : Type*} {n : ℕ} (v : V)
    (σ : AffineSimplex V n) (z : ℤ) :
    cone v (Finsupp.single σ z) = z • simplexCone v σ := by
  rw [show Finsupp.single σ z = z • simplex σ by simp [simplex]]
  simp [map_zsmul, cone_simplex]

lemma mem_support_cone {V : Type*} {n : ℕ} (v : V)
    (c : AffineChain V n) {τ : AffineSimplex V (n + 1)}
    (hτ : τ ∈ (cone v c).support) :
    ∃ σ ∈ c.support, τ = σ.append v := by
  classical
  induction c using Finsupp.induction with
  | zero =>
      simp at hτ
  | single_add σ z c hmem hn ih =>
      rw [map_add, cone_single] at hτ
      have hτ' :
          τ ∈ (z • simplexCone v σ).support ∪ (cone v c).support :=
        Finset.mem_of_subset Finsupp.support_add hτ
      rw [Finset.mem_union] at hτ'
      rcases hτ' with hσ | hc
      · refine ⟨σ, ?_,
          mem_support_simplexCone v σ (Finset.mem_of_subset Finsupp.support_smul hσ)⟩
        have hcσ : c σ = 0 := Finsupp.notMem_support_iff.mp hmem
        simp [Finsupp.mem_support_iff, hcσ, hn]
      · obtain ⟨ρ, hρ, hτρ⟩ := ih hc
        refine ⟨ρ, ?_, hτρ⟩
        simp [Finsupp.mem_support_iff] at hρ ⊢
        have hρσ : ρ ≠ σ := fun h => hmem (h ▸ (Finsupp.mem_support_iff.mpr hρ))
        simpa [hρσ] using hρ

lemma mem_support_subdivide_simplexBoundary {V : Type*}
    (b : {n : ℕ} → AffineSimplex V n → V) {n : ℕ}
    (σ : AffineSimplex V (n + 1)) {τ : AffineSimplex V n}
    (hτ : τ ∈ (subdivide b n (simplexBoundary σ)).support) :
    ∃ i : Fin (n + 2),
      τ ∈ (subdivide b n (simplex (σ.face i))).support := by
  classical
  simp only [simplexBoundary, map_sum, map_zsmul] at hτ
  have hsum (s : Finset (Fin (n + 2))) :
      τ ∈ (∑ i ∈ s,
          (-1 : ℤ) ^ (i : ℕ) •
            subdivide b n (simplex (σ.face i))).support →
        ∃ i ∈ s, τ ∈ (subdivide b n (simplex (σ.face i))).support := by
    induction s using Finset.induction with
    | empty => simp
    | insert i s his ih =>
        intro h
        rw [Finset.sum_insert his] at h
        have h' := Finset.mem_of_subset Finsupp.support_add h
        rw [Finset.mem_union] at h'
        rcases h' with hi | hs
        · exact ⟨i, Finset.mem_insert_self _ _,
            Finset.mem_of_subset Finsupp.support_smul hi⟩
        · obtain ⟨j, hj, hjτ⟩ := ih hs
          exact ⟨j, Finset.mem_insert_of_mem hj, hjτ⟩
  obtain ⟨i, _, hi⟩ := hsum _ hτ
  exact ⟨i, hi⟩

lemma mem_support_subdivide_simplex {V : Type*}
    (b : {n : ℕ} → AffineSimplex V n → V) {n : ℕ}
    (σ : AffineSimplex V (n + 1)) {τ : AffineSimplex V (n + 1)}
    (hτ : τ ∈ (subdivide b (n + 1) (simplex σ)).support) :
    ∃ i : Fin (n + 2),
      ∃ ρ ∈ (subdivide b n (simplex (σ.face i))).support,
        τ = ρ.append (b σ) := by
  rw [subdivide_simplex] at hτ
  obtain ⟨ρ, hρ, hτρ⟩ := mem_support_cone (b σ) _ hτ
  obtain ⟨i, hi⟩ := mem_support_subdivide_simplexBoundary b σ hρ
  exact ⟨i, ρ, hi, hτρ⟩

/-- Every simplex in the support of a subdivided chain comes from
subdividing one of the original generators. -/
lemma mem_support_subdivide {V : Type*}
    (b : {n : ℕ} → AffineSimplex V n → V) (n : ℕ)
    {c : AffineChain V n} {τ : AffineSimplex V n}
    (hτ : τ ∈ (subdivide b n c).support) :
    ∃ σ ∈ c.support, τ ∈ (subdivide b n (simplex σ)).support := by
  classical
  induction c using Finsupp.induction with
  | zero =>
      simp at hτ
  | single_add σ z c hmem hn ih =>
      rw [map_add] at hτ
      have hτ' :
          τ ∈ (subdivide b n (Finsupp.single σ z)).support ∪
            (subdivide b n c).support :=
        Finset.mem_of_subset Finsupp.support_add hτ
      rw [Finset.mem_union] at hτ'
      rcases hτ' with hσ | hc
      · refine ⟨σ, ?_, ?_⟩
        · have hcσ : c σ = 0 := Finsupp.notMem_support_iff.mp hmem
          simp [Finsupp.mem_support_iff, hcσ, hn]
        · have hsmul :
              subdivide b n (Finsupp.single σ z) =
                z • subdivide b n (simplex σ) := by
            rw [show Finsupp.single σ z = z • simplex σ by simp [simplex]]
            simp
          rw [hsmul] at hσ
          exact Finset.mem_of_subset Finsupp.support_smul hσ
      · obtain ⟨ρ, hρ, hτρ⟩ := ih hc
        refine ⟨ρ, ?_, hτρ⟩
        simp [Finsupp.mem_support_iff] at hρ ⊢
        have hρσ : ρ ≠ σ := fun h => hmem (h ▸ (Finsupp.mem_support_iff.mpr hρ))
        simpa [hρσ] using hρ

end

end PlatonicSolids.SingularExcision
