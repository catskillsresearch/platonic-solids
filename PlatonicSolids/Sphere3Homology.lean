/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import PlatonicSolids.EulerPoincare

/-!
Paper §3.1. Cellular homology of the standard simplicial \(S^3\):
the boundary of a 4-simplex (5 vertices, 10 edges, 10 triangles,
5 tetrahedra).

Ranks are `4, 6, 4`, so `b₀ = 1`, `b₁ = 0`, `b₂ = 0`, `b₃ = 1` and
`χ = 0`. This is the combinatorial 3-sphere the paper uses; Mathlib
does not compute singular homology of `Metric.sphere` in positive
degree.
-/

open scoped Matrix
open Matrix Module

/-- Vertices `0..4` ← edges `01,02,03,04,12,13,14,23,24,34`. -/
def pentatope_d1 : Matrix (Fin 5) (Fin 10) ℚ :=
  !![ -1, -1, -1, -1,  0,  0,  0,  0,  0,  0;
       1,  0,  0,  0, -1, -1, -1,  0,  0,  0;
       0,  1,  0,  0,  1,  0,  0, -1, -1,  0;
       0,  0,  1,  0,  0,  1,  0,  1,  0, -1;
       0,  0,  0,  1,  0,  0,  1,  0,  1,  1]

/-- Edges ← triangles
`012,013,014,023,024,034,123,124,134,234`. -/
def pentatope_d2 : Matrix (Fin 10) (Fin 10) ℚ :=
  !![ 1,  1,  1,  0,  0,  0,  0,  0,  0,  0;
     -1,  0,  0,  1,  1,  0,  0,  0,  0,  0;
      0, -1,  0, -1,  0,  1,  0,  0,  0,  0;
      0,  0, -1,  0, -1, -1,  0,  0,  0,  0;
      1,  0,  0,  0,  0,  0,  1,  1,  0,  0;
      0,  1,  0,  0,  0,  0, -1,  0,  1,  0;
      0,  0,  1,  0,  0,  0,  0, -1, -1,  0;
      0,  0,  0,  1,  0,  0,  1,  0,  0,  1;
      0,  0,  0,  0,  1,  0,  0,  1,  0, -1;
      0,  0,  0,  0,  0,  1,  0,  0,  1,  1]

/-- Triangles ← tetrahedra `0123,0124,0134,0234,1234`. -/
def pentatope_d3 : Matrix (Fin 10) (Fin 5) ℚ :=
  !![ -1, -1,  0,  0,  0;
       1,  0, -1,  0,  0;
       0,  1,  1,  0,  0;
      -1,  0,  0, -1,  0;
       0, -1,  0,  1,  0;
       0,  0, -1, -1,  0;
       1,  0,  0,  0, -1;
       0,  1,  0,  0,  1;
       0,  0,  1,  0, -1;
       0,  0,  0,  1,  1]

lemma pentatope_comp21 : pentatope_d1 * pentatope_d2 = 0 := by
  native_decide

lemma pentatope_comp32 : pentatope_d2 * pentatope_d3 = 0 := by
  native_decide

noncomputable def pentatope_del1 : (Fin 10 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) :=
  pentatope_d1.toLin'
noncomputable def pentatope_del2 : (Fin 10 → ℚ) →ₗ[ℚ] (Fin 10 → ℚ) :=
  pentatope_d2.toLin'
noncomputable def pentatope_del3 : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 10 → ℚ) :=
  pentatope_d3.toLin'

lemma pentatope_del_comp21 : pentatope_del1.comp pentatope_del2 = 0 := by
  rw [pentatope_del1, pentatope_del2, ← toLin'_mul, pentatope_comp21]
  exact map_zero _

lemma pentatope_del_comp32 : pentatope_del2.comp pentatope_del3 = 0 := by
  rw [pentatope_del2, pentatope_del3, ← toLin'_mul, pentatope_comp32]
  exact map_zero _

lemma pentatope_d1_rank_ge : 4 ≤ pentatope_d1.rank := by
  have hI : ((1 : Matrix (Fin 4) (Fin 4) ℚ).rank) = 4 := rank_one
  have hsub :
      pentatope_d1.submatrix ![1, 2, 3, 4] ![0, 1, 2, 3] =
        (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pentatope_d1]
  have : (pentatope_d1.submatrix ![1, 2, 3, 4] ![0, 1, 2, 3]).rank = 4 := by
    rw [hsub]; exact hI
  exact this.symm.trans_le (rank_submatrix_le _ _ _)

lemma pentatope_d3_rank_ge : 4 ≤ pentatope_d3.rank := by
  have hI : ((1 : Matrix (Fin 4) (Fin 4) ℚ).rank) = 4 := rank_one
  have hsub :
      pentatope_d3.submatrix ![6, 7, 8, 9] ![0, 1, 2, 3] =
        (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pentatope_d3]
  have : (pentatope_d3.submatrix ![6, 7, 8, 9] ![0, 1, 2, 3]).rank = 4 := by
    rw [hsub]; exact hI
  exact this.symm.trans_le (rank_submatrix_le _ _ _)

/-- A `6 × 6` minor of `d₂` with determinant `1`. -/
def pentatope_d2_minor : Matrix (Fin 6) (Fin 6) ℚ :=
  !![ 1,  1,  1,  0,  0,  0;
     -1,  0,  0,  1,  1,  0;
      0, -1,  0, -1,  0,  1;
      1,  0,  0,  0,  0,  0;
      0,  1,  0,  0,  0,  0;
      0,  0,  0,  1,  0,  0]

lemma pentatope_d2_minor_eq :
    pentatope_d2.submatrix ![0, 1, 2, 4, 5, 7] ![0, 1, 2, 3, 4, 5] =
      pentatope_d2_minor := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pentatope_d2, pentatope_d2_minor]

lemma pentatope_d2_minor_det : pentatope_d2_minor.det = 1 := by
  native_decide

lemma pentatope_d2_rank_ge : 6 ≤ pentatope_d2.rank := by
  have hU : IsUnit pentatope_d2_minor :=
    (Matrix.isUnit_iff_isUnit_det _).2 (by simp [pentatope_d2_minor_det])
  have : pentatope_d2_minor.rank = 6 := by
    simpa using rank_of_isUnit pentatope_d2_minor hU
  rw [← pentatope_d2_minor_eq] at this
  exact this.symm.trans_le (rank_submatrix_le _ _ _)

lemma pentatope_d1_rank : pentatope_d1.rank = 4 := by
  have hsum := rank_add_rank_le_card_of_mul_eq_zero pentatope_comp21
  have h1 := pentatope_d1_rank_ge
  have h2 := pentatope_d2_rank_ge
  simp only [Fintype.card_fin] at hsum
  omega

lemma pentatope_d2_rank : pentatope_d2.rank = 6 := by
  have hsum := rank_add_rank_le_card_of_mul_eq_zero pentatope_comp21
  have h1 := pentatope_d1_rank_ge
  have h2 := pentatope_d2_rank_ge
  simp only [Fintype.card_fin] at hsum
  omega

lemma pentatope_d3_rank : pentatope_d3.rank = 4 := by
  have hsum := rank_add_rank_le_card_of_mul_eq_zero pentatope_comp32
  have h2 := pentatope_d2_rank
  have h3 := pentatope_d3_rank_ge
  simp only [Fintype.card_fin] at hsum
  omega

lemma pentatope_del1_range : finrank ℚ (LinearMap.range pentatope_del1) = 4 := by
  simpa [pentatope_del1, toLin'_apply'] using pentatope_d1_rank

lemma pentatope_del2_range : finrank ℚ (LinearMap.range pentatope_del2) = 6 := by
  simpa [pentatope_del2, toLin'_apply'] using pentatope_d2_rank

lemma pentatope_del3_range : finrank ℚ (LinearMap.range pentatope_del3) = 4 := by
  simpa [pentatope_del3, toLin'_apply'] using pentatope_d3_rank

theorem sphere3_betti0 : betti0 pentatope_del1 = 1 := by
  simp [betti0, pentatope_del1_range, finrank_fintype_fun_eq_card]

theorem sphere3_betti1 : betti1 pentatope_del2 pentatope_del1 = 0 := by
  have hr := pentatope_del1.finrank_range_add_finrank_ker
  simp [betti1, pentatope_del2_range, pentatope_del1_range,
    finrank_fintype_fun_eq_card] at hr ⊢
  omega

theorem sphere3_betti2 : betti2Rel pentatope_del3 pentatope_del2 = 0 := by
  have hr := pentatope_del2.finrank_range_add_finrank_ker
  simp [betti2Rel, pentatope_del3_range, pentatope_del2_range,
    finrank_fintype_fun_eq_card] at hr ⊢
  omega

theorem sphere3_betti3 : betti3 pentatope_del3 = 1 := by
  have hr := pentatope_del3.finrank_range_add_finrank_ker
  simp [betti3, pentatope_del3_range, finrank_fintype_fun_eq_card] at hr ⊢
  omega

/-- Cellular homology of the standard simplicial 3-sphere. -/
theorem homology_sphere3 :
    betti0 pentatope_del1 = 1 ∧
    betti1 pentatope_del2 pentatope_del1 = 0 ∧
    betti2Rel pentatope_del3 pentatope_del2 = 0 ∧
    betti3 pentatope_del3 = 1 :=
  ⟨sphere3_betti0, sphere3_betti1, sphere3_betti2, sphere3_betti3⟩

/-- `χ(S³) = 0` from the computed Betti numbers of the 4-simplex boundary. -/
theorem eulerChar_sphere3 : ((5 : ℕ) : ℤ) - 10 + 10 - 5 = 0 :=
  euler_formula_of_sphere3 pentatope_del3 pentatope_del2 pentatope_del1
    (by simp [finrank_fintype_fun_eq_card])
    (by simp [finrank_fintype_fun_eq_card])
    (by simp [finrank_fintype_fun_eq_card])
    (by simp [finrank_fintype_fun_eq_card])
    pentatope_del_comp32 pentatope_del_comp21
    sphere3_betti0 sphere3_betti1 sphere3_betti2 sphere3_betti3
