/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.GaugeRescale

/-!
Paper §2.1. Radial projection: the frontier of a bounded convex body
with nonempty interior is homeomorphic to the unit sphere. Mathlib's
`gaugeRescaleHomeomorph` is the homeomorphism of the ambient space
that carries the frontier onto `Metric.sphere 0 1`.
-/

open Metric Set

/-- The frontier of a bounded convex set with nonempty interior is a
topological sphere. This is the radial projection of the paper, stated
for a body that need not be centred at the origin. -/
theorem frontier_convex_homeo_sphere
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    (hc : Convex ℝ s) (hne : (interior s).Nonempty) (hb : Bornology.IsBounded s) :
    ∃ h : E ≃ₜ E, h '' frontier s = sphere (0 : E) 1 :=
  let ⟨h, _, _, hf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hb
  ⟨h, hf⟩
