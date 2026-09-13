/-
Copyright (c) 2026  Lars Warren Ericson.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.EpiMono

/-!
Relative singular homology of a pair `(X, A)` as the cokernel of the
inclusion of singular chains. Mathlib’s singular chain-complex functor
preserves monomorphisms (it is free on simplices), so a subspace
inclusion yields a short exact sequence of chain complexes and therefore
the long exact sequence of the pair.

This is the first half of the classical path to `Hₙ(Sⁿ)`: the remaining
obstruction is excision / small simplices, packaged in
`PlatonicSolids/MayerVietoris.lean`.
-/

open AlgebraicTopology CategoryTheory Limits HomologicalComplex
open scoped Topology

set_option linter.unusedSectionVars false

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{0} C] [HasPullbacks C]

variable (R : C)

/-- Inclusion of a subspace as a morphism of `TopCat`. -/
def subtypeIncl (X : Type) [TopologicalSpace X] (A : Set X) :
    TopCat.of ↥A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

instance subtypeIncl_mono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (subtypeIncl X A) :=
  (TopCat.mono_iff_injective _).2 Subtype.val_injective

/-- Singular chains of a subspace, included into those of the ambient space. -/
noncomputable def inclChains (X : Type) [TopologicalSpace X] (A : Set X) :
    ((singularChainComplexFunctor C).obj R).obj (.of ↥A) ⟶
      ((singularChainComplexFunctor C).obj R).obj (.of X) :=
  ((singularChainComplexFunctor C).obj R).map (subtypeIncl X A)

instance inclChains_mono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (inclChains (C := C) R X A) :=
  ((singularChainComplexFunctor C).obj R).map_mono (subtypeIncl X A)

/-- Relative singular chains `C_*(X, A; R) := coker(C_*(A) → C_*(X))`. -/
noncomputable def relativeSingularChains (X : Type) [TopologicalSpace X] (A : Set X) :
    ChainComplex C ℕ :=
  cokernel (inclChains (C := C) R X A)

/-- The short complex `C_*(A) → C_*(X) → C_*(X, A)`. -/
noncomputable def pairShortComplex (X : Type) [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (inclChains (C := C) R X A) (cokernel.π _) (cokernel.condition _)

instance pairShortComplex_mono_f (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (pairShortComplex (C := C) R X A).f :=
  inferInstanceAs (Mono (inclChains (C := C) R X A))

instance pairShortComplex_epi_g (X : Type) [TopologicalSpace X] (A : Set X) :
    Epi (pairShortComplex (C := C) R X A).g :=
  inferInstanceAs (Epi (cokernel.π (inclChains (C := C) R X A)))

/-- The pair sequence of singular chains is short exact. -/
lemma pair_shortExact (X : Type) [TopologicalSpace X] (A : Set X) :
    (pairShortComplex (C := C) R X A).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _
      (cokernelIsCokernel (inclChains (C := C) R X A)))
    inferInstance inferInstance

/-- Relative singular homology `Hₙ(X, A; R)`. -/
noncomputable def relativeSingularHomology
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) : C :=
  (relativeSingularChains (C := C) R X A).homology n

/-- The map `Hₙ(A) → Hₙ(X)` induced by the subspace inclusion. -/
noncomputable def pair_i
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (((singularChainComplexFunctor C).obj R).obj (.of ↥A)).homology n ⟶
      (((singularChainComplexFunctor C).obj R).obj (.of X)).homology n :=
  homologyMap (inclChains (C := C) R X A) n

/-- The map `Hₙ(X) → Hₙ(X, A)` to relative homology. -/
noncomputable def pair_j
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (((singularChainComplexFunctor C).obj R).obj (.of X)).homology n ⟶
      relativeSingularHomology (C := C) R X A n :=
  homologyMap (cokernel.π (inclChains (C := C) R X A)) n

/-- Connecting homomorphism `δ : H_{n+1}(X, A) → Hₙ(A)` of the pair. -/
noncomputable def pairδ
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    relativeSingularHomology (C := C) R X A (n + 1) ⟶
      (((singularChainComplexFunctor C).obj R).obj (.of ↥A)).homology n :=
  (pair_shortExact (C := C) R X A).δ (n + 1) n (by simp)

/-- The composition `Hₙ(A) → Hₙ(X) → Hₙ(X, A)` is zero. -/
lemma pair_i_comp_pair_j
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    pair_i (C := C) R X A n ≫ pair_j (C := C) R X A n = 0 := by
  simpa [pair_i, pair_j] using
    (by
      rw [← homologyMap_comp, cokernel.condition, homologyMap_zero] :
      homologyMap (inclChains (C := C) R X A) n ≫
        homologyMap (cokernel.π (inclChains (C := C) R X A)) n = 0)

/-- The composition `Hₙ(X) → Hₙ(X, A) → H_{n-1}(A)` is zero. -/
lemma pair_j_comp_pairδ
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    pair_j (C := C) R X A (n + 1) ≫ pairδ (C := C) R X A n = 0 :=
  (pair_shortExact (C := C) R X A).comp_δ (n + 1) n (by simp)

/-- The composition `H_{n+1}(X, A) → Hₙ(A) → Hₙ(X)` is zero. -/
lemma pairδ_comp_pair_i
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    pairδ (C := C) R X A n ≫ pair_i (C := C) R X A n = 0 :=
  (pair_shortExact (C := C) R X A).δ_comp (n + 1) n (by simp)

/-- Exactness of `Hₙ(A) → Hₙ(X) → Hₙ(X, A)`. -/
lemma pair_exact_at_X
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk (pair_i (C := C) R X A n) (pair_j (C := C) R X A n)
      (pair_i_comp_pair_j (C := C) R X A n)).Exact := by
  simpa [pair_i, pair_j, pairShortComplex] using
    (pair_shortExact (C := C) R X A).homology_exact₂ n

/-- Exactness of `Hₙ(X) → Hₙ(X, A) → H_{n-1}(A)`. -/
lemma pair_exact_at_rel
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk (pair_j (C := C) R X A (n + 1)) (pairδ (C := C) R X A n)
      (pair_j_comp_pairδ (C := C) R X A n)).Exact :=
  (pair_shortExact (C := C) R X A).homology_exact₃ (n + 1) n (by simp)

/-- Exactness of `H_{n+1}(X, A) → Hₙ(A) → Hₙ(X)`. -/
lemma pair_exact_at_A
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk (pairδ (C := C) R X A n) (pair_i (C := C) R X A n)
      (pairδ_comp_pair_i (C := C) R X A n)).Exact :=
  (pair_shortExact (C := C) R X A).homology_exact₁ (n + 1) n (by simp)
