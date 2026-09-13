/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PlatonicSolids.EulerPoincare
import PlatonicSolids.PlatonicPair

/-!
Paper §2.2–2.4. Regularity incidence `pF = 2E`, `qV = 2E` and Euler
`V + F = E + 2` force a Platonic pair, and force `E > 0` with no extra
non-degeneracy axiom.
-/

/-- The Euler + regularity identities algebraically prohibit `E = 0`. -/
theorem edges_pos_of_regular
    (V E F p q : ℕ)
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    (h_edges_faces : p * F = 2 * E)
    (h_edges_verts : q * V = 2 * E)
    (h_euler : V + F = E + 2) :
    0 < E := by
  have h_lhs : p * q * (V + F) = (2 * p + 2 * q) * E := calc
    p * q * (V + F) = p * (q * V) + q * (p * F) := by ring
    _ = p * (2 * E) + q * (2 * E) := by rw [h_edges_verts, h_edges_faces]
    _ = (2 * p + 2 * q) * E := by ring
  have h_rhs : p * q * (V + F) = p * q * E + 2 * p * q := calc
    p * q * (V + F) = p * q * (E + 2) := by rw [h_euler]
    _ = p * q * E + 2 * p * q := by ring
  have h_eq : (2 * p + 2 * q) * E = p * q * E + 2 * p * q := by rw [← h_lhs, h_rhs]
  by_contra hz
  have hE0 : E = 0 := Nat.eq_zero_of_not_pos hz
  subst hE0
  simp only [mul_zero, zero_add] at h_eq
  exact (Nat.pos_iff_ne_zero.mp (by positivity : 0 < 2 * p * q)) h_eq.symm

/-- Any regular incidence structure with χ = 2 is a Platonic pair. -/
theorem platonic_solids_3d
    (V E F p q : ℕ)
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    (h_edges_faces : p * F = 2 * E)
    (h_edges_verts : q * V = 2 * E)
    (h_euler : V + F = E + 2) :
    IsPlatonicPair p q := by
  have h_lhs : p * q * (V + F) = (2 * p + 2 * q) * E := calc
    p * q * (V + F) = p * (q * V) + q * (p * F) := by ring
    _ = p * (2 * E) + q * (2 * E) := by rw [h_edges_verts, h_edges_faces]
    _ = (2 * p + 2 * q) * E := by ring
  have h_eq : (2 * p + 2 * q) * E = p * q * E + 2 * p * q := by
    calc (2 * p + 2 * q) * E = p * q * (V + F) := h_lhs.symm
      _ = p * q * (E + 2) := by rw [h_euler]
      _ = p * q * E + 2 * p * q := by ring
  have h_ineq : p * q < 2 * p + 2 * q := by
    obtain hlt | hge := lt_or_ge (p * q) (2 * p + 2 * q)
    · exact hlt
    · have : (2 * p + 2 * q) * E ≤ p * q * E := Nat.mul_le_mul_right E hge
      have : 0 < 2 * p * q := by positivity
      omega
  exact platonic_pairs_of_inequality hp hq h_ineq

/-- The 3D classification from a cellular 2-complex with Betti numbers
`1, 0, 1`. Euler–Poincaré (`euler_formula_of_sphere2`) supplies
`V + F = E + 2`; regularity incidence then forces a Platonic pair.
The optional form `platonic_solids_3d_of_sphere` in
`SphereSingularHomology.lean` derives these numbers from a
quasi-isomorphism to singular chains of a model of `S^2`. -/
theorem platonic_solids_3d_of_homology
    {K : Type*} [Field K]
    {C₂ C₁ C₀ : Type*}
    [AddCommGroup C₂] [Module K C₂] [FiniteDimensional K C₂]
    [AddCommGroup C₁] [Module K C₁] [FiniteDimensional K C₁]
    [AddCommGroup C₀] [Module K C₀] [FiniteDimensional K C₀]
    (d₂ : C₂ →ₗ[K] C₁) (d₁ : C₁ →ₗ[K] C₀)
    (V E F p q : ℕ)
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    (h_edges_faces : p * F = 2 * E)
    (h_edges_verts : q * V = 2 * E)
    (hV : Module.finrank K C₀ = V)
    (hE : Module.finrank K C₁ = E)
    (hF : Module.finrank K C₂ = F)
    (hcomp : d₁.comp d₂ = 0)
    (hb0 : betti0 d₁ = 1) (hb1 : betti1 d₂ d₁ = 0) (hb2 : betti2 d₂ = 1) :
    IsPlatonicPair p q :=
  platonic_solids_3d V E F p q hp hq h_edges_faces h_edges_verts
    (euler_formula_of_sphere2 d₂ d₁ hV hE hF hcomp hb0 hb1 hb2)
