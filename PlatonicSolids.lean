/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/platonic-solids/blob/main/PlatonicSolids.lean
-/
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Formal Classification of Platonic Solids (3D) and Regular Polychora (4D)

Fully verified: 0 axioms, 0 admits, 0 sorrys. Companion note: `PlatonicSolids.md`.
-/

-- ============================================================================
-- PART 1: DIMENSION 3 — PLATONIC SOLIDS VIA TOPOLOGY & INCIDENCE
-- ============================================================================

/-- The 5 Platonic pairs (p, q):
    (3, 3): Tetrahedron
    (3, 4): Octahedron
    (4, 3): Cube
    (3, 5): Icosahedron
    (5, 3): Dodecahedron -/
def IsPlatonicPair (p q : ℕ) : Prop :=
  (p = 3 ∧ q = 3) ∨
  (p = 3 ∧ q = 4) ∨
  (p = 4 ∧ q = 3) ∨
  (p = 3 ∧ q = 5) ∨
  (p = 5 ∧ q = 3)

/-- Diophantine impossibility lemma: If p ≥ 4 and q ≥ 4, then p * q ≥ 2 * p + 2 * q.
    Derived algebraically from (p - 2)(q - 2) ≥ 4 without axioms. -/
lemma pq_ge_two_p_add_two_q {p q : ℕ} (hp : p ≥ 4) (hq : q ≥ 4) :
    p * q ≥ 2 * p + 2 * q := by
  have hp' : (p : ℤ) ≥ 4 := by omega
  have hq' : (q : ℤ) ≥ 4 := by omega
  zify
  nlinarith

/-- Complete classification of the Diophantine inequality p * q < 2 * p + 2 * q for p, q ≥ 3. -/
theorem platonic_pairs_of_inequality {p q : ℕ}
    (hp : p ≥ 3) (hq : q ≥ 3) (h : p * q < 2 * p + 2 * q) :
    IsPlatonicPair p q := by
  rcases show p = 3 ∨ q = 3 ∨ (p ≥ 4 ∧ q ≥ 4) by omega with rfl | rfl | ⟨hp4, hq4⟩
  · -- Case p = 3: 3q < 6 + 2q ==> q < 6. Since q ≥ 3, q ∈ {3, 4, 5}.
    rcases show q = 3 ∨ q = 4 ∨ q = 5 by omega with rfl | rfl | rfl
    · simp [IsPlatonicPair]
    · simp [IsPlatonicPair]
    · simp [IsPlatonicPair]
  · -- Case q = 3: 3p < 6 + 2p ==> p < 6. Since p ≥ 3, p ∈ {3, 4, 5}.
    rcases show p = 3 ∨ p = 4 ∨ p = 5 by omega with rfl | rfl | rfl
    · simp [IsPlatonicPair]
    · simp [IsPlatonicPair]
    · simp [IsPlatonicPair]
  · -- Case p ≥ 4 ∧ q ≥ 4: Direct contradiction with non-linear arithmetic
    have h_ge := pq_ge_two_p_add_two_q hp4 hq4
    omega

/-- Theorem: A Platonic configuration cannot have zero edges.
    The topological Euler characteristic (χ = 2) and regularity conditions (p, q ≥ 3)
    algebraically force E ≥ 1 without requiring any geometric non-degeneracy axiom. -/
theorem edges_pos_of_regular
    (V E F p q : ℕ)
    (hp : p ≥ 3) (hq : q ≥ 3)
    (h_edges_faces : p * F = 2 * E)
    (h_edges_verts : q * V = 2 * E)
    (h_euler : V + F = E + 2) :
    E > 0 := by
  have h_lhs : p * q * (V + F) = (2 * p + 2 * q) * E := calc
    p * q * (V + F) = p * (q * V) + q * (p * F) := by ring
    _ = p * (2 * E) + q * (2 * E) := by rw [h_edges_verts, h_edges_faces]
    _ = (2 * p + 2 * q) * E := by ring
  have h_rhs : p * q * (V + F) = (p * q) * E + 2 * p * q := calc
    p * q * (V + F) = p * q * (E + 2) := by rw [h_euler]
    _ = (p * q) * E + 2 * p * q := by ring
  have h_eq : (2 * p + 2 * q) * E = (p * q) * E + 2 * p * q := by
    rw [← h_lhs, h_rhs]
  by_contra h_zero
  have hE0 : E = 0 := Nat.eq_zero_of_not_pos h_zero
  subst hE0
  simp only [mul_zero, zero_add] at h_eq
  exact (Nat.pos_iff_ne_zero.mp (by positivity : 0 < 2 * p * q)) h_eq.symm

/-- The 3D Main Theorem:
    Any polyhedron satisfying Euler's formula (V - E + F = 2)
    and regularity incidence relations (pF = 2E, qV = 2E)
    must have (p, q) belonging to the 5 Platonic solids. -/
theorem platonic_solids_3d
    (V E F p q : ℕ)
    (hp : p ≥ 3) (hq : q ≥ 3)
    (h_edges_faces : p * F = 2 * E)
    (h_edges_verts : q * V = 2 * E)
    (h_euler : V + F = E + 2) :
    IsPlatonicPair p q := by
  have h_mul : p * q * (V + F) = p * q * (E + 2) := by rw [h_euler]
  have h_lhs : p * q * (V + F) = (2 * p + 2 * q) * E := calc
    p * q * (V + F) = p * (q * V) + q * (p * F) := by ring
    _ = p * (2 * E) + q * (2 * E) := by rw [h_edges_verts, h_edges_faces]
    _ = (2 * p + 2 * q) * E := by ring
  have h_rhs : p * q * (E + 2) = (p * q) * E + 2 * p * q := by ring
  have h_eq : (2 * p + 2 * q) * E = (p * q) * E + 2 * p * q := calc
    (2 * p + 2 * q) * E = p * q * (V + F) := h_lhs.symm
    _ = p * q * (E + 2) := h_mul
    _ = (p * q) * E + 2 * p * q := h_rhs
  have h_ineq : p * q < 2 * p + 2 * q := by
    obtain hlt | hge := lt_or_ge (p * q) (2 * p + 2 * q)
    · exact hlt
    · have h1 : (2 * p + 2 * q) * E ≤ (p * q) * E := Nat.mul_le_mul_right E hge
      have h_pos : 2 * p * q > 0 := by positivity
      omega
  exact platonic_pairs_of_inequality hp hq h_ineq


-- ============================================================================
-- PART 2: DIMENSION 4 — COXETER GRAM MATRICES AND SCHLÄFLI MINORS
-- ============================================================================

/-- Exact algebraic values of sin²(π/n) and cos²(π/n) represented in ℝ. -/
noncomputable def sin_sq (n : ℕ) : ℝ :=
  if n = 3 then 3 / 4
  else if n = 4 then 1 / 2
  else if n = 5 then (5 - Real.sqrt 5) / 8
  else 0

noncomputable def cos_sq (n : ℕ) : ℝ :=
  if n = 3 then 1 / 4
  else if n = 4 then 1 / 2
  else if n = 5 then (3 + Real.sqrt 5) / 8
  else 0

/-- The 4D Schläfli Gram determinant:
    D₄ = det(M₄) = sin²(π/p) * sin²(π/r) - cos²(π/q). -/
noncomputable def SchläfliDeterminant (p q r : ℕ) : ℝ :=
  sin_sq p * sin_sq r - cos_sq q

/-- The 6 regular convex 4-polytopes (Schläfli symbols {p, q, r}):
    {3, 3, 3}: 5-cell (4D Simplex)
    {4, 3, 3}: 8-cell (Tesseract / Hypercube)
    {3, 3, 4}: 16-cell (Cross-polytope)
    {3, 4, 3}: 24-cell (Exceptional 4D regular polytope)
    {5, 3, 3}: 120-cell
    {3, 3, 5}: 600-cell -/
def IsRegular4Polytope (p q r : ℕ) : Prop :=
  (p = 3 ∧ q = 3 ∧ r = 3) ∨
  (p = 4 ∧ q = 3 ∧ r = 3) ∨
  (p = 3 ∧ q = 3 ∧ r = 4) ∨
  (p = 3 ∧ q = 4 ∧ r = 3) ∨
  (p = 5 ∧ q = 3 ∧ r = 3) ∨
  (p = 3 ∧ q = 3 ∧ r = 5)

/-- Fundamental algebraic property of √5 without axioms: 2 < √5 < 3. -/
lemma sqrt5_bounds : 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- 3 * √5 < 7 because 45 < 49. -/
lemma three_mul_sqrt5_lt_seven : 3 * Real.sqrt 5 < 7 := by
  have h : (3 * Real.sqrt 5) ^ 2 < (7 : ℝ) ^ 2 := by
    calc (3 * Real.sqrt 5) ^ 2 = 9 * (Real.sqrt 5 ^ 2) := by ring
    _ = 9 * 5 := by rw [Real.sq_sqrt (by norm_num)]
    _ = 45 := by norm_num
    _ < 49 := by norm_num
    _ = (7 : ℝ) ^ 2 := by norm_num
  have hpos : 0 ≤ 3 * Real.sqrt 5 := by positivity
  nlinarith

/-- 2 * √5 > 3 because 20 > 9. -/
lemma two_mul_sqrt5_gt_three : 2 * Real.sqrt 5 > 3 := by
  have h : (3 : ℝ) ^ 2 < (2 * Real.sqrt 5) ^ 2 := by
    calc (3 : ℝ) ^ 2 = 9 := by norm_num
    _ < 20 := by norm_num
    _ = 4 * 5 := by norm_num
    _ = 4 * (Real.sqrt 5 ^ 2) := by rw [Real.sq_sqrt (by norm_num)]
    _ = (2 * Real.sqrt 5) ^ 2 := by ring
  have hpos : 0 ≤ 2 * Real.sqrt 5 := by positivity
  nlinarith

/-- The Main Classification Theorem for 4D Regular Polychora:
    Any triple {p, q, r} whose 3D cells {p, q} and vertex figures {q, r} are
    Platonic solids, and whose Coxeter Gram matrix is positive-definite (D₄ > 0),
    is strictly one of the 6 regular convex 4-polytopes. -/
theorem regular_polychora_classification (p q r : ℕ)
    (h_cell : IsPlatonicPair p q)
    (h_vf : IsPlatonicPair q r)
    (h_det : SchläfliDeterminant p q r > 0) :
    IsRegular4Polytope p q r := by
  rcases h_cell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- Case p = 3, q = 3
    rcases h_vf with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨h_eq, -⟩ | ⟨-, rfl⟩ | ⟨h_eq, -⟩
    · simp [IsRegular4Polytope] -- {3, 3, 3}: 5-cell
    · simp [IsRegular4Polytope] -- {3, 3, 4}: 16-cell
    · contradiction           -- 4 = 3 is impossible
    · simp [IsRegular4Polytope] -- {3, 3, 5}: 600-cell
    · contradiction           -- 5 = 3 is impossible
  · -- Case p = 3, q = 4
    rcases h_vf with ⟨h_eq, -⟩ | ⟨h_eq, -⟩ | ⟨-, rfl⟩ | ⟨h_eq, -⟩ | ⟨h_eq, -⟩
    · contradiction
    · contradiction
    · simp [IsRegular4Polytope] -- {3, 4, 3}: 24-cell
    · contradiction
    · contradiction
  · -- Case p = 4, q = 3
    rcases h_vf with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨h_eq, -⟩ | ⟨-, rfl⟩ | ⟨h_eq, -⟩
    · simp [IsRegular4Polytope] -- {4, 3, 3}: 8-cell (Tesseract)
    · -- {4, 3, 4}: Cubic Honeycomb has determinant exactly 0, contradicting > 0
      dsimp [SchläfliDeterminant, sin_sq, cos_sq] at h_det
      linarith
    · contradiction
    · -- {4, 3, 5}: Hyperbolic, det < 0
      dsimp [SchläfliDeterminant, sin_sq, cos_sq] at h_det
      have := sqrt5_bounds.1
      linarith
    · contradiction
  · -- Case p = 3, q = 5
    rcases h_vf with ⟨h_eq, -⟩ | ⟨h_eq, -⟩ | ⟨h_eq, -⟩ | ⟨h_eq, -⟩ | ⟨-, rfl⟩
    · contradiction
    · contradiction
    · contradiction
    · contradiction
    · -- {3, 5, 3}: Icosacell Honeycomb has det < 0
      dsimp [SchläfliDeterminant, sin_sq, cos_sq] at h_det
      have := two_mul_sqrt5_gt_three
      linarith
  · -- Case p = 5, q = 3
    rcases h_vf with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨h_eq, -⟩ | ⟨-, rfl⟩ | ⟨h_eq, -⟩
    · simp [IsRegular4Polytope] -- {5, 3, 3}: 120-cell
    · -- {5, 3, 4}: Hyperbolic, det < 0
      dsimp [SchläfliDeterminant, sin_sq, cos_sq] at h_det
      have := sqrt5_bounds.1
      linarith
    · contradiction
    · -- {5, 3, 5}: Hyperbolic, det < 0
      dsimp [SchläfliDeterminant, sin_sq, cos_sq] at h_det
      have h1 : 2 < Real.sqrt 5 := sqrt5_bounds.1
      have h_sq : (Real.sqrt 5 - 2) * (Real.sqrt 5 - 2) ≥ 0 := by positivity
      have h_eval : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      nlinarith
    · contradiction
