/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import PlatonicSolids.EulerPoincare

/-!
Categorical infrastructure for a finite-dimensional cellular `2`-complex.

The chain groups are concentrated in degrees `0`, `1`, and `2`.  The
categorical homology dimensions are identified with the integer-valued Betti
numbers used by `EulerPoincare.lean`.
-/

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
open Module

variable {K : Type} [Field K]
variable {C₂ C₁ C₀ : Type}
  [AddCommGroup C₂] [Module K C₂]
  [AddCommGroup C₁] [Module K C₁]
  [AddCommGroup C₀] [Module K C₀]

/-- The chain complex `C₂ → C₁ → C₀`, extended by zero in degrees at least `3`. -/
noncomputable def cellularChainComplex
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀) (hcomp : d₁.comp d₂ = 0) :
    ChainComplex (ModuleCat.{0} K) ℕ :=
  ChainComplex.mk
    (ModuleCat.of K C₀) (ModuleCat.of K C₁) (ModuleCat.of K C₂)
    (ModuleCat.ofHom d₁) (ModuleCat.ofHom d₂)
    (by
      apply ModuleCat.hom_ext
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using hcomp)
    (fun S => ⟨ModuleCat.of K (Fin 0 → K), 0, zero_comp⟩)

@[simp]
theorem cellularChainComplex_X_zero
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀) (hcomp : d₁.comp d₂ = 0) :
    (cellularChainComplex d₂ d₁ hcomp).X 0 = ModuleCat.of K C₀ := rfl

@[simp]
theorem cellularChainComplex_X_one
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀) (hcomp : d₁.comp d₂ = 0) :
    (cellularChainComplex d₂ d₁ hcomp).X 1 = ModuleCat.of K C₁ := rfl

@[simp]
theorem cellularChainComplex_X_two
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀) (hcomp : d₁.comp d₂ = 0) :
    (cellularChainComplex d₂ d₁ hcomp).X 2 = ModuleCat.of K C₂ := rfl

@[simp]
theorem cellularChainComplex_d_one_zero
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀) (hcomp : d₁.comp d₂ = 0) :
    (cellularChainComplex d₂ d₁ hcomp).d 1 0 = ModuleCat.ofHom d₁ := by
  simp [cellularChainComplex]

@[simp]
theorem cellularChainComplex_d_two_one
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀) (hcomp : d₁.comp d₂ = 0) :
    (cellularChainComplex d₂ d₁ hcomp).d 2 1 = ModuleCat.ofHom d₂ := by
  simp [cellularChainComplex]

@[simp]
theorem cellularChainComplex_d_high
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀) (hcomp : d₁.comp d₂ = 0) (n : ℕ) :
    (cellularChainComplex d₂ d₁ hcomp).d (n + 3) (n + 2) = 0 := by
  rw [cellularChainComplex, ChainComplex.mk_d]
  simp

/-- Finrank is invariant under an isomorphism of `ModuleCat` objects. -/
theorem ModuleCat.finrank_eq_of_iso {V W : ModuleCat.{0} K} (e : V ≅ W) :
    finrank K V = finrank K W :=
  e.toLinearEquiv.finrank_eq

/-- Finrank of short-complex homology is the dimension of cycles minus boundaries. -/
theorem ShortComplex.int_finrank_homology_eq
    (S : ShortComplex (ModuleCat.{0} K))
    [FiniteDimensional K S.X₁] [FiniteDimensional K S.X₂] :
    (finrank K S.homology : ℤ) =
      (finrank K (LinearMap.ker S.g.hom) : ℤ) -
        finrank K (LinearMap.range S.f.hom) := by
  have hrange :
      finrank K (LinearMap.range S.moduleCatToCycles) =
        finrank K (LinearMap.range S.f.hom) := by
    have h₁ := S.moduleCatToCycles.finrank_range_add_finrank_ker
    have h₂ := S.f.hom.finrank_range_add_finrank_ker
    rw [LinearMap.ker_codRestrict] at h₁
    omega
  have hiso := S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  change finrank K S.homology =
    finrank K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at hiso
  rw [hiso, Submodule.finrank_quotient]
  have hle :
      finrank K (LinearMap.range S.moduleCatToCycles) ≤
        finrank K (LinearMap.ker S.g.hom) :=
    (LinearMap.range S.moduleCatToCycles).finrank_le
  omega

/-- Degree-zero categorical homology has the existing integer Betti number `betti0`. -/
theorem cellularChainComplex_homology_finrank_zero
    [FiniteDimensional K C₂] [FiniteDimensional K C₁] [FiniteDimensional K C₀]
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀) (hcomp : d₁.comp d₂ = 0) :
    (finrank K ((cellularChainComplex d₂ d₁ hcomp).homology 0) : ℤ) = betti0 d₁ := by
  let C := cellularChainComplex d₂ d₁ hcomp
  letI : FiniteDimensional K (C.sc' 1 0 0).X₁ := by
    change FiniteDimensional K C₁
    exact ‹FiniteDimensional K C₁›
  letI : FiniteDimensional K (C.sc' 1 0 0).X₂ := by
    change FiniteDimensional K C₀
    exact ‹FiniteDimensional K C₀›
  calc
    (finrank K (C.homology 0) : ℤ) =
        finrank K ((C.sc' 1 0 0).homology) := by
      exact_mod_cast ModuleCat.finrank_eq_of_iso (C.homologyIsoSc' 1 0 0 (by simp) (by simp))
    _ = (finrank K (LinearMap.ker (C.d 0 0).hom) : ℤ) -
          finrank K (LinearMap.range (C.d 1 0).hom) :=
      ShortComplex.int_finrank_homology_eq (C.sc' 1 0 0)
    _ = betti0 d₁ := by
      have hd00 : C.d 0 0 = 0 := C.shape 0 0 (by simp)
      have hd10 : C.d 1 0 = ModuleCat.ofHom d₁ := by
        simp [C]
      rw [hd00, hd10]
      change (finrank K (LinearMap.ker (0 : C₀ →ₗ[K] C₀)) : ℤ) -
        finrank K (LinearMap.range d₁) = betti0 d₁
      rw [LinearMap.ker_zero, finrank_top]
      rfl

/-- Degree-one categorical homology has the existing integer Betti number `betti1`. -/
theorem cellularChainComplex_homology_finrank_one
    [FiniteDimensional K C₂] [FiniteDimensional K C₁] [FiniteDimensional K C₀]
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀) (hcomp : d₁.comp d₂ = 0) :
    (finrank K ((cellularChainComplex d₂ d₁ hcomp).homology 1) : ℤ) =
      betti1 d₂ d₁ := by
  let C := cellularChainComplex d₂ d₁ hcomp
  letI : FiniteDimensional K (C.sc' 2 1 0).X₁ := by
    change FiniteDimensional K C₂
    exact ‹FiniteDimensional K C₂›
  letI : FiniteDimensional K (C.sc' 2 1 0).X₂ := by
    change FiniteDimensional K C₁
    exact ‹FiniteDimensional K C₁›
  calc
    (finrank K (C.homology 1) : ℤ) =
        finrank K ((C.sc' 2 1 0).homology) := by
      exact_mod_cast ModuleCat.finrank_eq_of_iso (C.homologyIsoSc' 2 1 0 (by simp) (by simp))
    _ = (finrank K (LinearMap.ker (C.d 1 0).hom) : ℤ) -
          finrank K (LinearMap.range (C.d 2 1).hom) :=
      ShortComplex.int_finrank_homology_eq (C.sc' 2 1 0)
    _ = betti1 d₂ d₁ := by
      have hd10 : C.d 1 0 = ModuleCat.ofHom d₁ := by
        simp [C]
      have hd21 : C.d 2 1 = ModuleCat.ofHom d₂ := by
        simp [C]
      rw [hd10, hd21]
      rfl

/-- Degree-two categorical homology has the existing integer Betti number `betti2`. -/
theorem cellularChainComplex_homology_finrank_two
    [FiniteDimensional K C₂] [FiniteDimensional K C₁] [FiniteDimensional K C₀]
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀) (hcomp : d₁.comp d₂ = 0) :
    (finrank K ((cellularChainComplex d₂ d₁ hcomp).homology 2) : ℤ) = betti2 d₂ := by
  let C := cellularChainComplex d₂ d₁ hcomp
  letI : FiniteDimensional K (C.sc' 3 2 1).X₁ := by
    change FiniteDimensional K (Fin 0 → K)
    infer_instance
  letI : FiniteDimensional K (C.sc' 3 2 1).X₂ := by
    change FiniteDimensional K C₂
    exact ‹FiniteDimensional K C₂›
  calc
    (finrank K (C.homology 2) : ℤ) =
        finrank K ((C.sc' 3 2 1).homology) := by
      exact_mod_cast ModuleCat.finrank_eq_of_iso (C.homologyIsoSc' 3 2 1 (by simp) (by simp))
    _ = (finrank K (LinearMap.ker (C.d 2 1).hom) : ℤ) -
          finrank K (LinearMap.range (C.d 3 2).hom) :=
      ShortComplex.int_finrank_homology_eq (C.sc' 3 2 1)
    _ = betti2 d₂ := by
      have hd21 : C.d 2 1 = ModuleCat.ofHom d₂ := by
        simp [C]
      have hd32 : C.d 3 2 = 0 := by
        simp [C]
      rw [hd21, hd32]
      change (finrank K (LinearMap.ker d₂) : ℤ) -
        finrank K (LinearMap.range (0 : (Fin 0 → K) →ₗ[K] C₂)) = betti2 d₂
      simp [betti2]

/-- An isomorphism between homology objects preserves their finrank. -/
theorem homology_finrank_eq_of_iso
    {A B : ChainComplex (ModuleCat.{0} K) ℕ} {n : ℕ}
    (e : A.homology n ≅ B.homology n) :
    finrank K (A.homology n) = finrank K (B.homology n) :=
  ModuleCat.finrank_eq_of_iso e

/-- A quasi-isomorphism in one degree preserves homology finrank in that degree. -/
theorem homology_finrank_eq_of_quasiIsoAt
    {A B : ChainComplex (ModuleCat.{0} K) ℕ} (f : A ⟶ B) (n : ℕ)
    [QuasiIsoAt f n] :
    finrank K (A.homology n) = finrank K (B.homology n) :=
  homology_finrank_eq_of_iso (isoOfQuasiIsoAt f n)

/-- A quasi-isomorphism preserves homology finrank in every degree. -/
theorem homology_finrank_eq_of_quasiIso
    {A B : ChainComplex (ModuleCat.{0} K) ℕ} (f : A ⟶ B) [QuasiIso f] (n : ℕ) :
    finrank K (A.homology n) = finrank K (B.homology n) :=
  homology_finrank_eq_of_quasiIsoAt f n

