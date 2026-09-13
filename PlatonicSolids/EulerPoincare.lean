/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Paper §2.1. Algebraic Euler–Poincaré for a 2-dimensional chain complex
of finite-dimensional vector spaces (the cellular complex of a polyhedron):

`χ(C) = rank C₀ - rank C₁ + rank C₂` equals `χ(H) = b₀ - b₁ + b₂`.

The identity is rank-nullity in dimensions $2$ and $3$. Specializing
to the Betti numbers of the tetrahedron surface
(`PlatonicSolids/Sphere2Homology.lean`) yields `V + F = E + 2`.
Specializing to the $4$-simplex boundary
(`PlatonicSolids/Sphere3Homology.lean`) yields `V - E + F - C = 0`.
-/

open Module

variable {K : Type*} [Field K]
variable {C₂ C₁ C₀ : Type*}
  [AddCommGroup C₂] [Module K C₂] [FiniteDimensional K C₂]
  [AddCommGroup C₁] [Module K C₁] [FiniteDimensional K C₁]
  [AddCommGroup C₀] [Module K C₀]

/-- `b₀ = rank(C₀ / im d₁)`. -/
noncomputable def betti0 (d₁ : C₁ →ₗ[K] C₀) : ℤ :=
  finrank K C₀ - finrank K (LinearMap.range d₁)

/-- `b₁ = rank(ker d₁ / im d₂)`. -/
noncomputable def betti1 (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀) : ℤ :=
  finrank K (LinearMap.ker d₁) - finrank K (LinearMap.range d₂)

/-- `b₂ = rank(ker d₂)`. -/
noncomputable def betti2 (d₂ : C₂ →ₗ[K] C₁) : ℤ :=
  finrank K (LinearMap.ker d₂)

/-- Algebraic Euler–Poincaré: cell Euler characteristic equals homological
Euler characteristic for any 2-complex with `d₁.comp d₂ = 0`. -/
theorem euler_poincare (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀)
    (hcomp : d₁.comp d₂ = 0) :
    (finrank K C₀ : ℤ) - finrank K C₁ + finrank K C₂ =
      betti0 d₁ - betti1 d₂ d₁ + betti2 d₂ := by
  have _hB : LinearMap.range d₂ ≤ LinearMap.ker d₁ :=
    LinearMap.range_le_ker_iff.mpr hcomp
  have hr1 : (finrank K (LinearMap.range d₁) : ℤ) + finrank K (LinearMap.ker d₁) =
      finrank K C₁ := by exact_mod_cast d₁.finrank_range_add_finrank_ker
  have hr2 : (finrank K (LinearMap.range d₂) : ℤ) + finrank K (LinearMap.ker d₂) =
      finrank K C₂ := by exact_mod_cast d₂.finrank_range_add_finrank_ker
  simp only [betti0, betti1, betti2]
  linarith

/-- `V - E + F = 2` is the same counting identity as `V + F = E + 2`. -/
theorem euler_count {V E F : ℕ} (h : (V : ℤ) - E + F = 2) : V + F = E + 2 := by
  omega

/-- Cellular ranks `V, E, F` and the Betti numbers of `S²` give Euler's formula. -/
theorem euler_formula_of_sphere2
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀)
    {V E F : ℕ}
    (hV : finrank K C₀ = V) (hE : finrank K C₁ = E) (hF : finrank K C₂ = F)
    (hcomp : d₁.comp d₂ = 0)
    (hb0 : betti0 d₁ = 1) (hb1 : betti1 d₂ d₁ = 0) (hb2 : betti2 d₂ = 1) :
    V + F = E + 2 := by
  have hχ := euler_poincare d₂ d₁ hcomp
  rw [hV, hE, hF, hb0, hb1, hb2] at hχ
  exact euler_count hχ

variable {C₃ : Type*}
  [AddCommGroup C₃] [Module K C₃] [FiniteDimensional K C₃]

/-- In a 3-complex, `b₂ = rank(ker d₂ / im d₃)`. -/
noncomputable def betti2Rel (d₃ : C₃ →ₗ[K] C₂) (d₂ : C₂ →ₗ[K] C₁) : ℤ :=
  finrank K (LinearMap.ker d₂) - finrank K (LinearMap.range d₃)

/-- `b₃ = rank(ker d₃)`. -/
noncomputable def betti3 (d₃ : C₃ →ₗ[K] C₂) : ℤ :=
  finrank K (LinearMap.ker d₃)

/-- Algebraic Euler–Poincaré in dimension 3. -/
theorem euler_poincare3 (d₃ : C₃ →ₗ[K] C₂) (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀)
    (h32 : d₂.comp d₃ = 0) (h21 : d₁.comp d₂ = 0) :
    (finrank K C₀ : ℤ) - finrank K C₁ + finrank K C₂ - finrank K C₃ =
      betti0 d₁ - betti1 d₂ d₁ + betti2Rel d₃ d₂ - betti3 d₃ := by
  have _hB21 : LinearMap.range d₂ ≤ LinearMap.ker d₁ :=
    LinearMap.range_le_ker_iff.mpr h21
  have _hB32 : LinearMap.range d₃ ≤ LinearMap.ker d₂ :=
    LinearMap.range_le_ker_iff.mpr h32
  have hr1 : (finrank K (LinearMap.range d₁) : ℤ) + finrank K (LinearMap.ker d₁) =
      finrank K C₁ := by exact_mod_cast d₁.finrank_range_add_finrank_ker
  have hr2 : (finrank K (LinearMap.range d₂) : ℤ) + finrank K (LinearMap.ker d₂) =
      finrank K C₂ := by exact_mod_cast d₂.finrank_range_add_finrank_ker
  have hr3 : (finrank K (LinearMap.range d₃) : ℤ) + finrank K (LinearMap.ker d₃) =
      finrank K C₃ := by exact_mod_cast d₃.finrank_range_add_finrank_ker
  simp only [betti0, betti1, betti2Rel, betti3]
  linarith

/-- Cell counts of an `S³` complex with Betti numbers `1,0,0,1` give `χ = 0`. -/
theorem euler_formula_of_sphere3
    (d₃ : C₃ →ₗ[K] C₂) (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀)
    {V E F C : ℕ}
    (hV : finrank K C₀ = V) (hE : finrank K C₁ = E)
    (hF : finrank K C₂ = F) (hC : finrank K C₃ = C)
    (h32 : d₂.comp d₃ = 0) (h21 : d₁.comp d₂ = 0)
    (hb0 : betti0 d₁ = 1) (hb1 : betti1 d₂ d₁ = 0)
    (hb2 : betti2Rel d₃ d₂ = 0) (hb3 : betti3 d₃ = 1) :
    (V : ℤ) - E + F - C = 0 := by
  have hχ := euler_poincare3 d₃ d₂ d₁ h32 h21
  rw [hV, hE, hF, hC, hb0, hb1, hb2, hb3] at hχ
  linarith
