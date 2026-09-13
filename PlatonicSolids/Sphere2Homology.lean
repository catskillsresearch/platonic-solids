/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import PlatonicSolids.EulerPoincare
import PlatonicSolids.Incidence

/-!
Paper §2.1. Cellular homology of the standard simplicial \(S^2\):
the boundary of a tetrahedron (4 vertices, 6 edges, 4 triangles).

This is the usual CW / simplicial calculation
`H₀ ≅ ℚ`, `H₁ = 0`, `H₂ ≅ ℚ`. Mathlib's singular homology of
`Metric.sphere` is not computed; this is the chain complex the
Euler–Poincaré argument uses.
-/

open scoped Matrix
open Matrix Module

/-- Oriented incidence vertices ← edges: columns `01,02,03,12,13,23`. -/
def tetra_d1 : Matrix (Fin 4) (Fin 6) ℚ :=
  !![ -1, -1, -1,  0,  0,  0;
       1,  0,  0, -1, -1,  0;
       0,  1,  0,  1,  0, -1;
       0,  0,  1,  0,  1,  1]

/-- Oriented incidence edges ← faces: columns `012,013,023,123`. -/
def tetra_d2 : Matrix (Fin 6) (Fin 4) ℚ :=
  !![ 1,  1,  0,  0;
     -1,  0,  1,  0;
      0, -1, -1,  0;
      1,  0,  0,  1;
      0,  1,  0, -1;
      0,  0,  1,  1]

lemma tetra_comp : tetra_d1 * tetra_d2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tetra_d1, tetra_d2]

noncomputable def tetra_del1 : (Fin 6 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) := tetra_d1.toLin'
noncomputable def tetra_del2 : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 6 → ℚ) := tetra_d2.toLin'

lemma tetra_del_comp : tetra_del1.comp tetra_del2 = 0 := by
  rw [tetra_del1, tetra_del2, ← toLin'_mul, tetra_comp]
  exact map_zero _

lemma tetra_d1_rank_ge : 3 ≤ tetra_d1.rank := by
  have hI : ((1 : Matrix (Fin 3) (Fin 3) ℚ).rank) = 3 := rank_one
  have hsub :
      tetra_d1.submatrix ![1, 2, 3] ![0, 1, 2] = (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tetra_d1]
  have : (tetra_d1.submatrix ![1, 2, 3] ![0, 1, 2]).rank = 3 := by
    rw [hsub]; exact hI
  exact this.symm.trans_le (rank_submatrix_le _ _ _)

lemma tetra_d2_rank_ge : 3 ≤ tetra_d2.rank := by
  have hI : ((1 : Matrix (Fin 3) (Fin 3) ℚ).rank) = 3 := rank_one
  have hsub :
      tetra_d2.submatrix ![3, 4, 5] ![0, 1, 2] = (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tetra_d2]
  have : (tetra_d2.submatrix ![3, 4, 5] ![0, 1, 2]).rank = 3 := by
    rw [hsub]; exact hI
  exact this.symm.trans_le (rank_submatrix_le _ _ _)

lemma tetra_d1_rank : tetra_d1.rank = 3 := by
  have hsum := rank_add_rank_le_card_of_mul_eq_zero tetra_comp
  have h1 := tetra_d1_rank_ge
  have h2 := tetra_d2_rank_ge
  simp only [Fintype.card_fin] at hsum
  omega

lemma tetra_d2_rank : tetra_d2.rank = 3 := by
  have hsum := rank_add_rank_le_card_of_mul_eq_zero tetra_comp
  have h1 := tetra_d1_rank_ge
  have h2 := tetra_d2_rank_ge
  simp only [Fintype.card_fin] at hsum
  omega

lemma tetra_del1_range : finrank ℚ (LinearMap.range tetra_del1) = 3 := by
  simpa [tetra_del1, toLin'_apply'] using tetra_d1_rank

lemma tetra_del2_range : finrank ℚ (LinearMap.range tetra_del2) = 3 := by
  simpa [tetra_del2, toLin'_apply'] using tetra_d2_rank

/-- `H₀(S²; ℚ) ≅ ℚ`. -/
theorem sphere2_betti0 : betti0 tetra_del1 = 1 := by
  simp [betti0, tetra_del1_range, finrank_fintype_fun_eq_card]

/-- `H₁(S²; ℚ) = 0`. -/
theorem sphere2_betti1 : betti1 tetra_del2 tetra_del1 = 0 := by
  have hr := tetra_del1.finrank_range_add_finrank_ker
  simp [betti1, tetra_del2_range, tetra_del1_range, finrank_fintype_fun_eq_card] at hr ⊢
  omega

/-- `H₂(S²; ℚ) ≅ ℚ`. -/
theorem sphere2_betti2 : betti2 tetra_del2 = 1 := by
  have hr := tetra_del2.finrank_range_add_finrank_ker
  simp [betti2, tetra_del2_range, finrank_fintype_fun_eq_card] at hr ⊢
  omega

/-- Cellular homology of the standard simplicial 2-sphere. -/
theorem homology_sphere2 :
    betti0 tetra_del1 = 1 ∧ betti1 tetra_del2 tetra_del1 = 0 ∧ betti2 tetra_del2 = 1 :=
  ⟨sphere2_betti0, sphere2_betti1, sphere2_betti2⟩

/-- Euler's formula on the tetrahedron, from its computed Betti numbers. -/
theorem euler_tetrahedron : (4 : ℕ) + 4 = 6 + 2 :=
  euler_formula_of_sphere2 tetra_del2 tetra_del1
    (by simp [finrank_fintype_fun_eq_card])
    (by simp [finrank_fintype_fun_eq_card])
    (by simp [finrank_fintype_fun_eq_card])
    tetra_del_comp sphere2_betti0 sphere2_betti1 sphere2_betti2

/-- The tetrahedron incidence structure is Platonic, using homology not a
raw Euler hypothesis. -/
theorem tetrahedron_platonic : IsPlatonicPair 3 3 :=
  platonic_solids_3d_of_homology tetra_del2 tetra_del1 4 6 4 3 3
    (by decide) (by decide) (by decide) (by decide)
    (by simp [finrank_fintype_fun_eq_card])
    (by simp [finrank_fintype_fun_eq_card])
    (by simp [finrank_fintype_fun_eq_card])
    tetra_del_comp sphere2_betti0 sphere2_betti1 sphere2_betti2
