/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.DirectSum.Module

/-!
Finite-support access for categorical coproducts in `ModuleCat`.

This is why the elementwise small-simplices proof is specialized to module
coefficients: every element of the categorical coproduct is, through
`ModuleCat.coprodIsoDirectSum`, a genuinely finite direct sum.
-/

open CategoryTheory Limits

universe u v w

namespace ModuleCat

variable {R : Type u} [Ring R] {ι : Type v}
variable (Z : ι → ModuleCat.{max v w} R) [DecidableEq ι] [HasCoproduct Z]

/-- The finite set of summands on which an element of a categorical
coproduct of modules is nonzero. -/
noncomputable def coprodSupport
    (x : Limits.sigmaObj (C := ModuleCat.{max v w} R) Z) : Finset ι :=
  by
    classical
    exact (coprodIsoDirectSum Z).hom x |>.support

/-- Every element of a categorical coproduct of modules is the finite sum
of its components included into the coproduct. -/
lemma eq_sum_ι_apply_coprodSupport
    (x : Limits.sigmaObj (C := ModuleCat.{max v w} R) Z) :
    x = ∑ i ∈ coprodSupport Z x,
      Sigma.ι Z i ((coprodIsoDirectSum Z).hom x i) := by
  classical
  apply_fun (coprodIsoDirectSum Z).hom using
    (ModuleCat.mono_iff_injective (coprodIsoDirectSum Z).hom).mp inferInstance
  simp only [map_sum, ι_coprodIsoDirectSum_hom_apply]
  exact (DirectSum.sum_support_of ((coprodIsoDirectSum Z).hom x)).symm

end ModuleCat
