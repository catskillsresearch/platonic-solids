import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import PlatonicSolids.SimplicialSingularComparison
import PlatonicSolids.SingularExcision.OpenCoverQI

/-!
# The boundary-two comparison

This file supplies the open-cover bridge from the simplicial
Mayer--Vietoris sequence for `∂Δ[2]` to singular chains.
-/

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Set
open scoped ContinuousMap Simplicial Topology

noncomputable section

universe u

variable {k : Type} [Ring k]

local instance boundaryTwoCirclePeriodPositive : Fact (0 < (3 : ℝ)) :=
  ⟨by norm_num⟩

/-- The puncture in the interior of the horn arc. -/
def hornInteriorPoint : AddCircle (3 : ℝ) := (1 : ℝ)

/-- The puncture in the interior of the last-edge arc. -/
def lastEdgeInteriorPoint : AddCircle (3 : ℝ) := ((5 / 2 : ℝ) : AddCircle (3 : ℝ))

lemma hornInteriorPoint_ne_lastEdgeInteriorPoint :
    hornInteriorPoint ≠ lastEdgeInteriorPoint := by
  intro h
  have h' : (1 : ℝ) = 5 / 2 := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (3 : ℝ)) (a := (0 : ℝ))
      (x := (1 : ℝ)) (y := (5 / 2 : ℝ))
      (by norm_num) (by norm_num)).1
    exact h
  norm_num at h'

/-- An open neighborhood of the last closed edge. -/
def boundaryTwoLastEdgeOpen : Set |boundaryTwoSSet| :=
  boundaryTwoToBoundaryCircle ⁻¹' ({hornInteriorPoint}ᶜ)

/-- An open neighborhood of the two-edge horn. -/
def boundaryTwoHornOpen : Set |boundaryTwoSSet| :=
  boundaryTwoToBoundaryCircle ⁻¹' ({lastEdgeInteriorPoint}ᶜ)

lemma isOpen_boundaryTwoLastEdgeOpen : IsOpen boundaryTwoLastEdgeOpen :=
  isOpen_compl_singleton.preimage boundaryTwoToBoundaryCircle.hom.continuous

lemma isOpen_boundaryTwoHornOpen : IsOpen boundaryTwoHornOpen :=
  isOpen_compl_singleton.preimage boundaryTwoToBoundaryCircle.hom.continuous

lemma boundaryTwo_open_cover :
    boundaryTwoLastEdgeOpen ∪ boundaryTwoHornOpen = univ := by
  ext x
  simp only [boundaryTwoLastEdgeOpen, boundaryTwoHornOpen, mem_union,
    mem_preimage, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
  by_contra h
  push_neg at h
  exact hornInteriorPoint_ne_lastEdgeInteriorPoint (h.1.symm.trans h.2)

/-- The punctured circle used around the last edge has an open-interval
coordinate. -/
noncomputable def boundaryTwoLastEdgeOpenHomeoIoo :
    ↥boundaryTwoLastEdgeOpen ≃ₜ ↥(Ioo (1 : ℝ) 4) :=
  ((homeomorph_boundaryTwo_addCircle.subtype
      (p := fun x => x ∈ boundaryTwoLastEdgeOpen)
      (q := fun y => y ∈
        (AddCircle.openPartialHomeomorphCoe (3 : ℝ) (1 : ℝ)).target)
      (fun _ => Iff.rfl)).trans
    (AddCircle.openPartialHomeomorphCoe
      (3 : ℝ) (1 : ℝ)).toHomeomorphSourceTarget.symm).trans
    (Homeomorph.setCongr (by norm_num))

/-- The punctured circle used around the horn has an open-interval
coordinate. -/
noncomputable def boundaryTwoHornOpenHomeoIoo :
    ↥boundaryTwoHornOpen ≃ₜ ↥(Ioo (5 / 2 : ℝ) (11 / 2 : ℝ)) :=
  ((homeomorph_boundaryTwo_addCircle.subtype
      (p := fun x => x ∈ boundaryTwoHornOpen)
      (q := fun y => y ∈
        (AddCircle.openPartialHomeomorphCoe
          (3 : ℝ) (5 / 2 : ℝ)).target)
      (fun _ => Iff.rfl)).trans
    (AddCircle.openPartialHomeomorphCoe
      (3 : ℝ) (5 / 2 : ℝ)).toHomeomorphSourceTarget.symm).trans
    (Homeomorph.setCongr (by norm_num))

noncomputable instance boundaryTwoLastEdgeOpen_contractible :
    ContractibleSpace ↥boundaryTwoLastEdgeOpen := by
  letI : ContractibleSpace ↥(Ioo (1 : ℝ) 4) :=
    (convex_Ioo (1 : ℝ) 4).contractibleSpace
      ⟨2, by norm_num⟩
  exact boundaryTwoLastEdgeOpenHomeoIoo.contractibleSpace

noncomputable instance boundaryTwoHornOpen_contractible :
    ContractibleSpace ↥boundaryTwoHornOpen := by
  letI : ContractibleSpace ↥(Ioo (5 / 2 : ℝ) (11 / 2 : ℝ)) :=
    (convex_Ioo (5 / 2 : ℝ) (11 / 2 : ℝ)).contractibleSpace
      ⟨3, by norm_num⟩
  exact boundaryTwoHornOpenHomeoIoo.contractibleSpace

/-- Inclusion of the last edge into the whole simplicial boundary. -/
def boundaryTwoLastEdgeIncl :
    |(boundaryTwoFirstFace : SSet.{0})| ⟶ |boundaryTwoSSet| :=
  SSet.toTop.map (SSet.Subcomplex.homOfLE
    (by
      rw [boundary_two_eq_face_sup]
      exact (le_sup_left :
        boundaryTwoFirstFace ≤
          boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)))

/-- Inclusion of the horn into the whole simplicial boundary. -/
def boundaryTwoHornIncl :
    |(boundaryTwoRemainingFaces : SSet.{0})| ⟶ |boundaryTwoSSet| :=
  SSet.toTop.map (SSet.Subcomplex.homOfLE
    (by
      rw [boundary_two_eq_face_sup]
      exact (le_sup_right :
        boundaryTwoRemainingFaces ≤
          boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)))

lemma boundaryTwoLastEdgeIncl_circle :
    boundaryTwoLastEdgeIncl ≫ boundaryTwoToBoundaryCircle =
      lastEdgeToBoundaryCircle := by
  change
    SSet.toTop.map (SSet.Subcomplex.homOfLE _) ≫
        SSet.toTop.map boundaryTwoIsoSup.hom ≫
          boundaryTwoSupToBoundaryCircle =
      lastEdgeToBoundaryCircle
  rw [← Category.assoc, ← SSet.toTop.map_comp]
  have h :
      SSet.Subcomplex.homOfLE
          (show boundaryTwoFirstFace ≤
              (SSet.boundary 2 :
                (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) by
            rw [boundary_two_eq_face_sup]
            exact le_sup_left) ≫
        boundaryTwoIsoSup.hom =
      SSet.Subcomplex.homOfLE
        (le_sup_left : boundaryTwoFirstFace ≤
          boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces) := rfl
  rw [h, boundaryTwoSupToBoundaryCircle_firstFace]

lemma boundaryTwoHornIncl_circle :
    boundaryTwoHornIncl ≫ boundaryTwoToBoundaryCircle =
      boundaryTwoRemainingFacesToBoundaryCircle := by
  change
    SSet.toTop.map (SSet.Subcomplex.homOfLE _) ≫
        SSet.toTop.map boundaryTwoIsoSup.hom ≫
          boundaryTwoSupToBoundaryCircle =
      boundaryTwoRemainingFacesToBoundaryCircle
  rw [← Category.assoc, ← SSet.toTop.map_comp]
  have h :
      SSet.Subcomplex.homOfLE
          (show boundaryTwoRemainingFaces ≤
              (SSet.boundary 2 :
                (SSet.stdSimplex.obj ⦋2⦌ : SSet.{0}).Subcomplex) by
            rw [boundary_two_eq_face_sup]
            exact le_sup_right) ≫
        boundaryTwoIsoSup.hom =
      SSet.Subcomplex.homOfLE
        (le_sup_right : boundaryTwoRemainingFaces ≤
          boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces) := rfl
  rw [h, boundaryTwoSupToBoundaryCircle_remainingFaces]

lemma lastEdgeToBoundaryCircle_ne_hornInteriorPoint
    (x : |(boundaryTwoFirstFace : SSet.{0})|) :
    lastEdgeToBoundaryCircle x ≠ hornInteriorPoint := by
  intro h
  let t := lastEdgeIsoI.hom x
  have hmem : 2 + (TopCat.I.homeomorph t : ℝ) ∈ Ico (1 : ℝ) 4 :=
    ⟨by linarith [(TopCat.I.homeomorph t).property.1],
      by linarith [(TopCat.I.homeomorph t).property.2]⟩
  have hmem' : 2 + (TopCat.I.homeomorph t : ℝ) ∈
      Ico (1 : ℝ) (1 + 3) := by
    convert hmem using 1 <;> norm_num
  have hone : (1 : ℝ) ∈ Ico (1 : ℝ) (1 + 3) := by norm_num
  have hr : 2 + (TopCat.I.homeomorph t : ℝ) = 1 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (3 : ℝ)) (a := (1 : ℝ)) hmem' hone).1 h
  linarith [(TopCat.I.homeomorph t).property.1]

lemma boundaryTwoRemainingFacesToBoundaryCircle_ne_lastEdgeInteriorPoint
    (x : |(boundaryTwoRemainingFaces : SSet.{0})|) :
    boundaryTwoRemainingFacesToBoundaryCircle x ≠ lastEdgeInteriorPoint := by
  intro h
  let t := horn_two_zero_toIcc
    (SSet.toTop.map boundaryTwoRemainingFacesIsoHorn.hom x)
  have ht : (t : ℝ) ∈ Icc (-1 : ℝ) 1 := t.property
  have hmem : (t : ℝ) + 1 ∈ Ico (0 : ℝ) 3 :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hp : (5 / 2 : ℝ) ∈ Ico (0 : ℝ) 3 := by norm_num
  have hmem' : (t : ℝ) + 1 ∈ Ico (0 : ℝ) (0 + 3) := by
    simpa using hmem
  have hp' : (5 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 3) := by
    simpa using hp
  have hr : (t : ℝ) + 1 = 5 / 2 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (3 : ℝ)) (a := (0 : ℝ)) hmem' hp').1 h
  linarith [ht.2]

/-- The last edge lands in its punctured-circle neighborhood. -/
def boundaryTwoLastEdgeToOpen :
    |(boundaryTwoFirstFace : SSet.{0})| ⟶ TopCat.of ↥boundaryTwoLastEdgeOpen :=
  TopCat.ofHom
    { toFun := fun x => ⟨boundaryTwoLastEdgeIncl x, by
        change boundaryTwoToBoundaryCircle (boundaryTwoLastEdgeIncl x) ≠
          hornInteriorPoint
        rw [← CategoryTheory.comp_apply, boundaryTwoLastEdgeIncl_circle]
        exact lastEdgeToBoundaryCircle_ne_hornInteriorPoint x⟩
      continuous_toFun := by fun_prop }

/-- The horn lands in its punctured-circle neighborhood. -/
def boundaryTwoHornToOpen :
    |(boundaryTwoRemainingFaces : SSet.{0})| ⟶ TopCat.of ↥boundaryTwoHornOpen :=
  TopCat.ofHom
    { toFun := fun x => ⟨boundaryTwoHornIncl x, by
        change boundaryTwoToBoundaryCircle (boundaryTwoHornIncl x) ≠
          lastEdgeInteriorPoint
        rw [← CategoryTheory.comp_apply, boundaryTwoHornIncl_circle]
        exact boundaryTwoRemainingFacesToBoundaryCircle_ne_lastEdgeInteriorPoint x⟩
      continuous_toFun := by fun_prop }

/-! ## Quasi-isomorphisms for the two contractible pieces -/

lemma singularChainMap_quasiIso_of_contractible
    (R : ModuleCat.{0} k) {X Y : TopCat.{0}}
    [ContractibleSpace X] [ContractibleSpace Y] (f : X ⟶ Y) :
    QuasiIso
      (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map f) := by
  letI : PathConnectedSpace X :=
    ContractibleSpace.instPathConnectedSpace
  letI : PathConnectedSpace Y :=
    ContractibleSpace.instPathConnectedSpace
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hn : n = 0
  · subst n
    letI hXiso : IsIso (X.singularHomology₀ε R) := by infer_instance
    letI hYiso : IsIso (Y.singularHomology₀ε R) := by infer_instance
    have hnat := singularHomology₀ε_natural f R
    let φ := ((singularChainComplexFunctor
      (ModuleCat.{0} k)).obj R).map f
    change IsIso (homologyMap φ 0)
    letI hcomp : IsIso
        (homologyMap φ 0 ≫ Y.singularHomology₀ε R) := by
      rw [hnat]
      exact hXiso
    exact @IsIso.of_isIso_comp_right _ _ _ _ _
      (homologyMap φ 0) (Y.singularHomology₀ε R) hYiso hcomp
  · apply IsZero.isIso
      (isZero_singularHomology_of_contractible R hn)
    exact isZero_singularHomology_of_contractible R hn

noncomputable instance boundaryTwoFirstFace_realization_contractible :
    ContractibleSpace |(boundaryTwoFirstFace : SSet.{0})| := by
  letI : ContractibleSpace _root_.unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  letI : ContractibleSpace TopCat.I :=
    TopCat.I.homeomorph.contractibleSpace
  exact (TopCat.homeoOfIso lastEdgeIsoI).contractibleSpace

noncomputable instance boundaryTwoRemainingFaces_realization_contractible :
    ContractibleSpace |(boundaryTwoRemainingFaces : SSet.{0})| := by
  letI : ContractibleSpace |(Λ[2, 0] : SSet.{0})| :=
    realization_horn_two_zero_contractible
  exact (TopCat.homeoOfIso
    (SSet.toTop.mapIso boundaryTwoRemainingFacesIsoHorn)).contractibleSpace

/-- The comparison from the last-edge simplicial chains to singular chains
of its open neighborhood. -/
noncomputable def boundaryTwoLastEdgeOpenComparison
    (R : ModuleCat.{0} k) :
    (boundaryTwoFirstFace : SSet.{0}).chainComplex R ⟶
      ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
        (TopCat.of ↥boundaryTwoLastEdgeOpen) :=
  simplicialSingularComparison R (boundaryTwoFirstFace : SSet.{0}) ≫
    ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
      boundaryTwoLastEdgeToOpen

noncomputable instance boundaryTwoLastEdgeOpenComparison_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso (boundaryTwoLastEdgeOpenComparison R) := by
  dsimp [boundaryTwoLastEdgeOpenComparison]
  letI : QuasiIso
      (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
        boundaryTwoLastEdgeToOpen) :=
    singularChainMap_quasiIso_of_contractible R _
  infer_instance

/-- The comparison from the horn simplicial chains to singular chains of
its open neighborhood. -/
noncomputable def boundaryTwoHornOpenComparison
    (R : ModuleCat.{0} k) :
    (boundaryTwoRemainingFaces : SSet.{0}).chainComplex R ⟶
      ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
        (TopCat.of ↥boundaryTwoHornOpen) :=
  simplicialSingularComparison R (boundaryTwoRemainingFaces : SSet.{0}) ≫
    ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
      boundaryTwoHornToOpen

noncomputable instance boundaryTwoHornOpenComparison_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso (boundaryTwoHornOpenComparison R) := by
  dsimp [boundaryTwoHornOpenComparison]
  letI : QuasiIso
      (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
        boundaryTwoHornToOpen) :=
    singularChainMap_quasiIso_of_contractible R _
  infer_instance

/-! ## The two-component open intersection -/

abbrev boundaryTwoOpenIntersection : Set |boundaryTwoSSet| :=
  boundaryTwoLastEdgeOpen ∩ boundaryTwoHornOpen

/-- Inclusion of the two simplicial vertices in the whole boundary. -/
def boundaryTwoVerticesInclBoundary :
    |(boundaryTwoVertices : SSet.{0})| ⟶ |boundaryTwoSSet| :=
  SSet.toTop.map (SSet.Subcomplex.homOfLE
    (boundaryTwoVertices_le_firstFace.trans
      (by
        rw [boundary_two_eq_face_sup]
        exact le_sup_left)))

lemma boundaryTwoVerticesInclBoundary_circle :
    boundaryTwoVerticesInclBoundary ≫ boundaryTwoToBoundaryCircle =
      SSet.toTop.map
          (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_firstFace) ≫
        lastEdgeToBoundaryCircle := by
  rw [← boundaryTwoLastEdgeIncl_circle]
  simp only [← Category.assoc]
  congr 1
  unfold boundaryTwoVerticesInclBoundary boundaryTwoLastEdgeIncl
  rw [← SSet.toTop.map_comp]
  rfl

lemma boundaryTwoVerticesInclBoundary_circle_vertex_one :
    boundaryTwoToBoundaryCircle
        (boundaryTwoVerticesInclBoundary boundaryTwoVertexOnePoint) =
      ((2 : ℝ) : AddCircle (3 : ℝ)) := by
  have h := congrArg
    (fun f : |(boundaryTwoVertices : SSet.{0})| ⟶ boundaryCircle =>
      f boundaryTwoVertexOnePoint)
    boundaryTwoVerticesInclBoundary_circle
  change
    boundaryTwoToBoundaryCircle
        (boundaryTwoVerticesInclBoundary boundaryTwoVertexOnePoint) =
      lastEdgeToBoundaryCircle
        (SSet.toTop.map
          (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_firstFace)
          boundaryTwoVertexOnePoint) at h
  rw [h]
  have hmap :
      SSet.toTop.map
          ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
            SSet.Subcomplex.homOfLE
              (le_sup_left :
                SSet.stdSimplex.face ({1} : Finset (Fin 3)) ≤
                  boundaryTwoVertices)) ≫
        SSet.toTop.map
          (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_firstFace) =
      SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE face_one_le_boundaryTwoFirstFace) := by
    simp only [← SSet.toTop.map_comp]
    rfl
  have heval := congrArg
    (fun f : |(Δ[0] : SSet.{0})| ⟶
        |(boundaryTwoFirstFace : SSet.{0})| =>
      f (default : |(Δ[0] : SSet.{0})|)) hmap
  change
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_firstFace)
        boundaryTwoVertexOnePoint =
      SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (1 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE face_one_le_boundaryTwoFirstFace)
        default at heval
  rw [heval]
  have hv := congrArg
    (fun f : |(Δ[0] : SSet.{0})| ⟶ boundaryCircle =>
      f (default : |(Δ[0] : SSet.{0})|))
    lastEdgeToBoundaryCircle_vertex_one
  simpa [boundaryTwoVertexOnePoint, SSet.toTop.map_comp,
    CategoryTheory.comp_apply] using hv

lemma boundaryTwoVerticesInclBoundary_circle_vertex_two :
    boundaryTwoToBoundaryCircle
        (boundaryTwoVerticesInclBoundary boundaryTwoVertexTwoPoint) =
      (0 : AddCircle (3 : ℝ)) := by
  have h := congrArg
    (fun f : |(boundaryTwoVertices : SSet.{0})| ⟶ boundaryCircle =>
      f boundaryTwoVertexTwoPoint)
    boundaryTwoVerticesInclBoundary_circle
  change
    boundaryTwoToBoundaryCircle
        (boundaryTwoVerticesInclBoundary boundaryTwoVertexTwoPoint) =
      lastEdgeToBoundaryCircle
        (SSet.toTop.map
          (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_firstFace)
          boundaryTwoVertexTwoPoint) at h
  rw [h]
  have hmap :
      SSet.toTop.map
          ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
            SSet.Subcomplex.homOfLE
              (le_sup_right :
                SSet.stdSimplex.face ({2} : Finset (Fin 3)) ≤
                  boundaryTwoVertices)) ≫
        SSet.toTop.map
          (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_firstFace) =
      SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE face_two_le_boundaryTwoFirstFace) := by
    simp only [← SSet.toTop.map_comp]
    rfl
  have heval := congrArg
    (fun f : |(Δ[0] : SSet.{0})| ⟶
        |(boundaryTwoFirstFace : SSet.{0})| =>
      f (default : |(Δ[0] : SSet.{0})|)) hmap
  change
    SSet.toTop.map
        (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_firstFace)
        boundaryTwoVertexTwoPoint =
      SSet.toTop.map
        ((SSet.stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫
          SSet.Subcomplex.homOfLE face_two_le_boundaryTwoFirstFace)
        default at heval
  rw [heval]
  have hv := congrArg
    (fun f : |(Δ[0] : SSet.{0})| ⟶ boundaryCircle =>
      f (default : |(Δ[0] : SSet.{0})|))
    lastEdgeToBoundaryCircle_vertex_two
  simpa [boundaryTwoVertexTwoPoint, SSet.toTop.map_comp,
    CategoryTheory.comp_apply] using hv

lemma boundaryTwoVerticesInclBoundary_mem_intersection
    (x : |(boundaryTwoVertices : SSet.{0})|) :
    boundaryTwoVerticesInclBoundary x ∈ boundaryTwoOpenIntersection := by
  have hx := congrArg
    (fun f : |(boundaryTwoVertices : SSet.{0})| ⟶
        |(boundaryTwoVertices : SSet.{0})| => f x)
    boundaryTwoVerticesToBool_comp_boolToBoundaryTwoVertices
  change boolToBoundaryTwoVertices
      (boundaryTwoVerticesToBool x) = x at hx
  constructor
  · change boundaryTwoToBoundaryCircle
      (boundaryTwoVerticesInclBoundary x) ≠ hornInteriorPoint
    rw [← hx]
    cases h : boundaryTwoVerticesToBool x
    · change boundaryTwoToBoundaryCircle
        (boundaryTwoVerticesInclBoundary boundaryTwoVertexOnePoint) ≠
          hornInteriorPoint
      rw [boundaryTwoVerticesInclBoundary_circle_vertex_one]
      intro hbad
      have : (2 : ℝ) = 1 := by
        apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
          (p := (3 : ℝ)) (a := (0 : ℝ))
          (x := (2 : ℝ)) (y := (1 : ℝ))
          (by norm_num) (by norm_num)).1
        exact hbad
      norm_num at this
    · change boundaryTwoToBoundaryCircle
        (boundaryTwoVerticesInclBoundary boundaryTwoVertexTwoPoint) ≠
          hornInteriorPoint
      rw [boundaryTwoVerticesInclBoundary_circle_vertex_two]
      intro hbad
      have : (0 : ℝ) = 1 := by
        apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
          (p := (3 : ℝ)) (a := (0 : ℝ))
          (x := (0 : ℝ)) (y := (1 : ℝ))
          (by norm_num) (by norm_num)).1
        exact hbad
      norm_num at this
  · change boundaryTwoToBoundaryCircle
      (boundaryTwoVerticesInclBoundary x) ≠ lastEdgeInteriorPoint
    rw [← hx]
    cases h : boundaryTwoVerticesToBool x
    · change boundaryTwoToBoundaryCircle
        (boundaryTwoVerticesInclBoundary boundaryTwoVertexOnePoint) ≠
          lastEdgeInteriorPoint
      rw [boundaryTwoVerticesInclBoundary_circle_vertex_one]
      intro hbad
      have : (2 : ℝ) = 5 / 2 := by
        apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
          (p := (3 : ℝ)) (a := (0 : ℝ))
          (x := (2 : ℝ)) (y := (5 / 2 : ℝ))
          (by norm_num) (by norm_num)).1
        exact hbad
      norm_num at this
    · change boundaryTwoToBoundaryCircle
        (boundaryTwoVerticesInclBoundary boundaryTwoVertexTwoPoint) ≠
          lastEdgeInteriorPoint
      rw [boundaryTwoVerticesInclBoundary_circle_vertex_two]
      intro hbad
      have : (0 : ℝ) = 5 / 2 := by
        apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
          (p := (3 : ℝ)) (a := (0 : ℝ))
          (x := (0 : ℝ)) (y := (5 / 2 : ℝ))
          (by norm_num) (by norm_num)).1
        exact hbad
      norm_num at this

/-- The realized two vertices land in the two components of the open
intersection. -/
def boundaryTwoVerticesToOpenIntersection :
    |(boundaryTwoVertices : SSet.{0})| ⟶
      TopCat.of ↥boundaryTwoOpenIntersection :=
  TopCat.ofHom
    { toFun := fun x =>
        ⟨boundaryTwoVerticesInclBoundary x,
          boundaryTwoVerticesInclBoundary_mem_intersection x⟩
      continuous_toFun := by fun_prop }

/-- A linear coordinate model for a circle punctured at `1` and `5/2`. -/
abbrev puncturedBoundaryIoo :=
  {x : ℝ // x ∈ Ioo (1 : ℝ) 4 ∧ x ≠ 5 / 2}

def puncturedBoundaryBase (b : Bool) : puncturedBoundaryIoo :=
  if b then
    ⟨3, by constructor <;> norm_num⟩
  else
    ⟨2, by constructor <;> norm_num⟩

def puncturedBoundarySide (x : puncturedBoundaryIoo) : Bool :=
  if 5 / 2 < (x : ℝ) then true else false

lemma continuous_puncturedBoundarySide :
    Continuous puncturedBoundarySide := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : (x : ℝ) < 5 / 2
  · apply (continuousAt_const :
      ContinuousAt (fun _ : puncturedBoundaryIoo => false) x).congr_of_eventuallyEq
    filter_upwards
      [(isOpen_lt continuous_subtype_val continuous_const).mem_nhds hx]
      with y hy
    simp [puncturedBoundarySide, not_lt.mpr (le_of_lt hy)]
  · have hx' : 5 / 2 < (x : ℝ) :=
      lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm x.property.2)
    apply (continuousAt_const :
      ContinuousAt (fun _ : puncturedBoundaryIoo => true) x).congr_of_eventuallyEq
    filter_upwards
      [(isOpen_lt continuous_const continuous_subtype_val).mem_nhds hx']
      with y hy
    simp [puncturedBoundarySide, hy]

def puncturedBoundarySideMap : C(puncturedBoundaryIoo, Bool) :=
  ⟨puncturedBoundarySide, continuous_puncturedBoundarySide⟩

def puncturedBoundaryBaseMap : C(Bool, puncturedBoundaryIoo) :=
  ⟨puncturedBoundaryBase, continuous_of_discreteTopology⟩

lemma puncturedBoundarySide_base (b : Bool) :
    puncturedBoundarySide (puncturedBoundaryBase b) = b := by
  cases b <;> simp [puncturedBoundarySide, puncturedBoundaryBase] <;> norm_num

/-- Contract each of the two punctured-interval components to its selected
endpoint vertex. -/
def puncturedBoundaryContraction :
    ContinuousMap.Homotopy
      (puncturedBoundaryBaseMap.comp puncturedBoundarySideMap)
      (ContinuousMap.id puncturedBoundaryIoo) where
  toFun tx :=
    let t : ℝ := tx.1
    let x : ℝ := tx.2
    let b : ℝ := puncturedBoundaryBase
      (puncturedBoundarySide tx.2)
    ⟨(1 - t) * b + t * x, by
      have ht0 : 0 ≤ t := tx.1.property.1
      have ht1 : t ≤ 1 := tx.1.property.2
      have hx1 : 1 < x := tx.2.property.1.1
      have hx4 : x < 4 := tx.2.property.1.2
      constructor
      · constructor
        · by_cases hs : 5 / 2 < x
          · have hb : b = 3 := by
              change 5 / 2 < (tx.2 : ℝ) at hs
              simp [b, puncturedBoundarySide, puncturedBoundaryBase, hs]
            rw [hb]
            nlinarith
          · have hb : b = 2 := by
              change ¬5 / 2 < (tx.2 : ℝ) at hs
              simp [b, puncturedBoundarySide, puncturedBoundaryBase, hs]
            rw [hb]
            nlinarith
        · by_cases hs : 5 / 2 < x
          · have hb : b = 3 := by
              change 5 / 2 < (tx.2 : ℝ) at hs
              simp [b, puncturedBoundarySide, puncturedBoundaryBase, hs]
            rw [hb]
            nlinarith
          · have hb : b = 2 := by
              change ¬5 / 2 < (tx.2 : ℝ) at hs
              simp [b, puncturedBoundarySide, puncturedBoundaryBase, hs]
            rw [hb]
            nlinarith
      · by_cases hs : 5 / 2 < x
        · have hb : b = 3 := by
            change 5 / 2 < (tx.2 : ℝ) at hs
            simp [b, puncturedBoundarySide, puncturedBoundaryBase, hs]
          rw [hb]
          have hx : 5 / 2 < x := hs
          nlinarith
        · have hx : x < 5 / 2 :=
            lt_of_le_of_ne (le_of_not_gt hs) tx.2.property.2
          have hb : b = 2 := by
            change ¬5 / 2 < (tx.2 : ℝ) at hs
            simp [b, puncturedBoundarySide, puncturedBoundaryBase, hs]
          rw [hb]
          nlinarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    dsimp
    have ht : Continuous
        (fun tx : _root_.unitInterval × puncturedBoundaryIoo =>
          (tx.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous
        (fun tx : _root_.unitInterval × puncturedBoundaryIoo =>
          (tx.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hbsub : Continuous
        (fun tx : _root_.unitInterval × puncturedBoundaryIoo =>
          (puncturedBoundaryBaseMap.comp puncturedBoundarySideMap) tx.2) :=
      (puncturedBoundaryBaseMap.comp
        puncturedBoundarySideMap).continuous.comp continuous_snd
    have hb : Continuous
        (fun tx : _root_.unitInterval × puncturedBoundaryIoo =>
          ((puncturedBoundaryBaseMap.comp
            puncturedBoundarySideMap) tx.2).val) :=
      continuous_subtype_val.comp hbsub
    exact ((continuous_const.sub ht).mul hb).add (ht.mul hx)
  map_zero_left x := by
    ext
    simp [puncturedBoundaryBaseMap, puncturedBoundarySideMap]
  map_one_left x := by
    ext
    simp

/-- The punctured interval has exactly the two contractible components
selected by `Bool`. -/
def puncturedBoundaryHomotopyEquivBool :
    Bool ≃ₕ puncturedBoundaryIoo where
  toFun := puncturedBoundaryBaseMap
  invFun := puncturedBoundarySideMap
  left_inv := by
    have h :
        puncturedBoundarySideMap.comp puncturedBoundaryBaseMap =
          ContinuousMap.id Bool := by
      ext b
      exact puncturedBoundarySide_base b
    rw [h]
  right_inv := ⟨puncturedBoundaryContraction⟩

lemma boundaryTwoLastEdgeOpenHomeoIoo_coe
    (x : ↥boundaryTwoLastEdgeOpen) :
    (((boundaryTwoLastEdgeOpenHomeoIoo x : Ioo (1 : ℝ) 4) : ℝ) :
        AddCircle (3 : ℝ)) =
      homeomorph_boundaryTwo_addCircle x.1 := by
  change
    (((AddCircle.equivIco (3 : ℝ) (1 : ℝ)
      (homeomorph_boundaryTwo_addCircle x.1) : ℝ)) :
        AddCircle (3 : ℝ)) =
      homeomorph_boundaryTwo_addCircle x.1
  exact AddCircle.coe_equivIco

/-- Reassociate the subtype representing the intersection of the two
open neighborhoods. -/
def boundaryTwoIntersectionNestedHomeo :
    ↥boundaryTwoOpenIntersection ≃ₜ
      {x : ↥boundaryTwoLastEdgeOpen // x.1 ∈ boundaryTwoHornOpen} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def nestedPuncturedIooHomeo :
    {x : ↥(Ioo (1 : ℝ) 4) // (x : ℝ) ≠ 5 / 2} ≃ₜ
      puncturedBoundaryIoo where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The open intersection is the interval `(1,4)` with its midpoint
puncture `5/2` removed. -/
noncomputable def boundaryTwoOpenIntersectionHomeoPuncturedIoo :
    ↥boundaryTwoOpenIntersection ≃ₜ puncturedBoundaryIoo :=
  boundaryTwoIntersectionNestedHomeo.trans
    ((boundaryTwoLastEdgeOpenHomeoIoo.subtype
      (p := fun x : ↥boundaryTwoLastEdgeOpen =>
        x.1 ∈ boundaryTwoHornOpen)
      (q := fun x : ↥(Ioo (1 : ℝ) 4) => (x : ℝ) ≠ 5 / 2)
      (fun x => by
        change homeomorph_boundaryTwo_addCircle x.1 ≠
            ((5 / 2 : ℝ) : AddCircle (3 : ℝ)) ↔
          (boundaryTwoLastEdgeOpenHomeoIoo x : ℝ) ≠ 5 / 2
        rw [← boundaryTwoLastEdgeOpenHomeoIoo_coe]
        have hm :
            (boundaryTwoLastEdgeOpenHomeoIoo x : ℝ) ∈
              Ioo (1 : ℝ) (1 + 3) := by
          convert (boundaryTwoLastEdgeOpenHomeoIoo x).property using 1 <;>
            norm_num
        exact not_congr (AddCircle.coe_eq_coe_iff_of_mem_Ico
          (p := (3 : ℝ)) (a := (1 : ℝ))
          (Ioo_subset_Ico_self hm)
          (by norm_num)))).trans nestedPuncturedIooHomeo)

lemma homeomorph_boundaryTwo_addCircle_apply
    (x : |boundaryTwoSSet|) :
    homeomorph_boundaryTwo_addCircle x =
      boundaryTwoToBoundaryCircle x := rfl

lemma boundaryTwoOpenIntersectionHomeo_vertex_one :
    boundaryTwoOpenIntersectionHomeoPuncturedIoo
        (boundaryTwoVerticesToOpenIntersection boundaryTwoVertexOnePoint) =
      puncturedBoundaryBase false := by
  apply Subtype.ext
  change
    ((AddCircle.equivIco (3 : ℝ) (1 : ℝ))
      (homeomorph_boundaryTwo_addCircle
        (boundaryTwoVerticesInclBoundary boundaryTwoVertexOnePoint))).1 = 2
  rw [homeomorph_boundaryTwo_addCircle_apply]
  rw [boundaryTwoVerticesInclBoundary_circle_vertex_one]
  rw [AddCircle.equivIco_coe_eq (by norm_num)]

lemma boundaryTwoOpenIntersectionHomeo_vertex_two :
    boundaryTwoOpenIntersectionHomeoPuncturedIoo
        (boundaryTwoVerticesToOpenIntersection boundaryTwoVertexTwoPoint) =
      puncturedBoundaryBase true := by
  apply Subtype.ext
  change
    ((AddCircle.equivIco (3 : ℝ) (1 : ℝ))
      (homeomorph_boundaryTwo_addCircle
        (boundaryTwoVerticesInclBoundary boundaryTwoVertexTwoPoint))).1 = 3
  rw [homeomorph_boundaryTwo_addCircle_apply]
  rw [boundaryTwoVerticesInclBoundary_circle_vertex_two]
  have hzero : (0 : AddCircle (3 : ℝ)) = ((3 : ℝ) : AddCircle (3 : ℝ)) := by
    exact (AddCircle.coe_period (3 : ℝ)).symm
  rw [hzero, AddCircle.equivIco_coe_eq (by norm_num)]

/-- The open intersection deformation-retracts onto the two realized
vertices. -/
noncomputable def boundaryTwoVerticesOpenIntersectionHomotopyEquiv :
    |(boundaryTwoVertices : SSet.{0})| ≃ₕ
      ↥boundaryTwoOpenIntersection := by
  let e :
      |(boundaryTwoVertices : SSet.{0})| ≃ₕ
        ↥boundaryTwoOpenIntersection :=
    homeomorph_boundaryTwoVertices_bool.toHomotopyEquiv.trans
      (puncturedBoundaryHomotopyEquivBool.trans
        boundaryTwoOpenIntersectionHomeoPuncturedIoo.toHomotopyEquiv.symm)
  have hfun :
      e.toFun =
        boundaryTwoVerticesToOpenIntersection.hom := by
    apply ContinuousMap.ext
    intro x
    apply boundaryTwoOpenIntersectionHomeoPuncturedIoo.injective
    have hx := congrArg
      (fun f : |(boundaryTwoVertices : SSet.{0})| ⟶
          |(boundaryTwoVertices : SSet.{0})| => f x)
      boundaryTwoVerticesToBool_comp_boolToBoundaryTwoVertices
    change boolToBoundaryTwoVertices
        (boundaryTwoVerticesToBool x) = x at hx
    rw [← hx]
    cases h : boundaryTwoVerticesToBool x
    · have hs := congrArg
        (fun f : TopCat.of Bool ⟶ TopCat.of Bool => f false)
        boolToBoundaryTwoVertices_comp_boundaryTwoVerticesToBool
      change homeomorph_boundaryTwoVertices_bool
          (boolToBoundaryTwoVertices false) = false at hs
      calc
        boundaryTwoOpenIntersectionHomeoPuncturedIoo
            (e.toFun (boolToBoundaryTwoVertices false)) =
            puncturedBoundaryBase
              (homeomorph_boundaryTwoVertices_bool
                (boolToBoundaryTwoVertices false)) := by
              change boundaryTwoOpenIntersectionHomeoPuncturedIoo
                  (boundaryTwoOpenIntersectionHomeoPuncturedIoo.symm
                    (puncturedBoundaryBase
                      (homeomorph_boundaryTwoVertices_bool
                        (boolToBoundaryTwoVertices false)))) =
                puncturedBoundaryBase
                  (homeomorph_boundaryTwoVertices_bool
                    (boolToBoundaryTwoVertices false))
              rw [Homeomorph.apply_symm_apply]
        _ = puncturedBoundaryBase false := by rw [hs]
        _ = boundaryTwoOpenIntersectionHomeoPuncturedIoo
            (boundaryTwoVerticesToOpenIntersection
              (boolToBoundaryTwoVertices false)) := by
              simpa using boundaryTwoOpenIntersectionHomeo_vertex_one.symm
    · have hs := congrArg
        (fun f : TopCat.of Bool ⟶ TopCat.of Bool => f true)
        boolToBoundaryTwoVertices_comp_boundaryTwoVerticesToBool
      change homeomorph_boundaryTwoVertices_bool
          (boolToBoundaryTwoVertices true) = true at hs
      calc
        boundaryTwoOpenIntersectionHomeoPuncturedIoo
            (e.toFun (boolToBoundaryTwoVertices true)) =
            puncturedBoundaryBase
              (homeomorph_boundaryTwoVertices_bool
                (boolToBoundaryTwoVertices true)) := by
              change boundaryTwoOpenIntersectionHomeoPuncturedIoo
                  (boundaryTwoOpenIntersectionHomeoPuncturedIoo.symm
                    (puncturedBoundaryBase
                      (homeomorph_boundaryTwoVertices_bool
                        (boolToBoundaryTwoVertices true)))) =
                puncturedBoundaryBase
                  (homeomorph_boundaryTwoVertices_bool
                    (boolToBoundaryTwoVertices true))
              rw [Homeomorph.apply_symm_apply]
        _ = puncturedBoundaryBase true := by rw [hs]
        _ = boundaryTwoOpenIntersectionHomeoPuncturedIoo
            (boundaryTwoVerticesToOpenIntersection
              (boolToBoundaryTwoVertices true)) := by
              simpa using boundaryTwoOpenIntersectionHomeo_vertex_two.symm
  exact
    { toFun := boundaryTwoVerticesToOpenIntersection.hom
      invFun := e.invFun
      left_inv := by
        rw [← hfun]
        exact e.left_inv
      right_inv := by
        rw [← hfun]
        exact e.right_inv }

noncomputable instance boundaryTwoVerticesToOpenIntersection_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso
      (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
        boundaryTwoVerticesToOpenIntersection) := by
  change QuasiIso
    (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
      (TopCat.ofHom boundaryTwoVerticesOpenIntersectionHomotopyEquiv.toFun))
  exact
    (singularChainHomotopyEquiv
      boundaryTwoVerticesOpenIntersectionHomotopyEquiv R).quasiIso_hom

/-- The comparison from the simplicial edge--horn intersection to
singular chains of the open intersection. -/
noncomputable def boundaryTwoOpenIntersectionComparison
    (R : ModuleCat.{0} k) :
    (boundaryTwoVertices : SSet.{0}).chainComplex R ⟶
      ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
        (TopCat.of ↥boundaryTwoOpenIntersection) :=
  simplicialSingularComparison R (boundaryTwoVertices : SSet.{0}) ≫
    ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
      boundaryTwoVerticesToOpenIntersection

noncomputable instance boundaryTwoOpenIntersectionComparison_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso (boundaryTwoOpenIntersectionComparison R) := by
  dsimp [boundaryTwoOpenIntersectionComparison]
  infer_instance

/-! ## Compatibility with the simplicial Mayer--Vietoris cover -/

/-- The realized edge--horn intersection lands in the intersection of the
two open neighborhoods. -/
noncomputable def boundaryTwoIntersectionToOpenIntersection :
    |((boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces : _) : SSet.{0})| ⟶
      TopCat.of boundaryTwoOpenIntersection :=
  SSet.toTop.map boundaryTwoIntersectionIsoVertices.hom ≫
    boundaryTwoVerticesToOpenIntersection

/-- The intersection landing map agrees with the last-edge landing map. -/
lemma boundaryTwoIntersectionToOpenIntersection_left :
    boundaryTwoIntersectionToOpenIntersection ≫
        interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen =
      SSet.toTop.map
          (SSet.Subcomplex.homOfLE
            (inf_le_left :
              boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
                boundaryTwoFirstFace)) ≫
        boundaryTwoLastEdgeToOpen := by
  apply (cancel_epi
    (SSet.toTop.map boundaryTwoIntersectionIsoVertices.inv)).1
  simp only [boundaryTwoIntersectionToOpenIntersection, ← Category.assoc,
    ← SSet.toTop.map_comp, Iso.inv_hom_id, SSet.toTop.map_id,
    Category.id_comp, boundaryTwoIntersectionIsoVertices_inv_comp_first]
  apply TopCat.hom_ext
  ext x
  change boundaryTwoVerticesInclBoundary x =
    boundaryTwoLastEdgeIncl
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_firstFace) x)
  unfold boundaryTwoVerticesInclBoundary boundaryTwoLastEdgeIncl
  rw [← CategoryTheory.comp_apply, ← SSet.toTop.map_comp]
  rfl

/-- The intersection landing map agrees with the horn landing map. -/
lemma boundaryTwoIntersectionToOpenIntersection_right :
    boundaryTwoIntersectionToOpenIntersection ≫
        interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen =
      SSet.toTop.map
          (SSet.Subcomplex.homOfLE
            (inf_le_right :
              boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
                boundaryTwoRemainingFaces)) ≫
        boundaryTwoHornToOpen := by
  apply (cancel_epi
    (SSet.toTop.map boundaryTwoIntersectionIsoVertices.inv)).1
  simp only [boundaryTwoIntersectionToOpenIntersection, ← Category.assoc,
    ← SSet.toTop.map_comp, Iso.inv_hom_id, SSet.toTop.map_id,
    Category.id_comp, boundaryTwoIntersectionIsoVertices_inv_comp_remaining]
  apply TopCat.hom_ext
  ext x
  change boundaryTwoVerticesInclBoundary x =
    boundaryTwoHornIncl
      (SSet.toTop.map
        (SSet.Subcomplex.homOfLE boundaryTwoVertices_le_remainingFaces) x)
  unfold boundaryTwoVerticesInclBoundary boundaryTwoHornIncl
  rw [← CategoryTheory.comp_apply, ← SSet.toTop.map_comp]
  rfl

/-- The realized simplicial intersection is homotopy equivalent to the
open-cover intersection. -/
noncomputable def boundaryTwoIntersectionOpenHomotopyEquiv :
    |((boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces : _) : SSet.{0})| ≃ₕ
      TopCat.of boundaryTwoOpenIntersection :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso boundaryTwoIntersectionIsoVertices)).toHomotopyEquiv.trans
    boundaryTwoVerticesOpenIntersectionHomotopyEquiv

/-- The singular-chain map induced by the intersection landing map is a
quasi-isomorphism. -/
noncomputable instance boundaryTwoIntersectionToOpenIntersection_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso
      (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
        boundaryTwoIntersectionToOpenIntersection) := by
  change QuasiIso
    (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
      (TopCat.ofHom boundaryTwoIntersectionOpenHomotopyEquiv.toFun))
  exact
    (singularChainHomotopyEquiv
      boundaryTwoIntersectionOpenHomotopyEquiv R).quasiIso_hom

/-- Comparison on the actual edge--horn intersection, factored through the
open-cover intersection. -/
noncomputable def boundaryTwoIntersectionOpenComparison
    (R : ModuleCat.{0} k) :
    ((boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces : _) : SSet.{0}).chainComplex R ⟶
      ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
        (TopCat.of boundaryTwoOpenIntersection) :=
  simplicialSingularComparison R
      ((boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces : _) : SSet.{0}) ≫
    ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
      boundaryTwoIntersectionToOpenIntersection

noncomputable instance boundaryTwoIntersectionOpenComparison_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso (boundaryTwoIntersectionOpenComparison R) := by
  dsimp [boundaryTwoIntersectionOpenComparison]
  infer_instance

lemma boundaryTwoIntersectionOpenComparison_left
    (R : ModuleCat.{0} k) :
    boundaryTwoIntersectionOpenComparison R ≫
        ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen) =
      SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE
            (inf_le_left :
              boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
                boundaryTwoFirstFace)) R ≫
        boundaryTwoLastEdgeOpenComparison R := by
  rw [boundaryTwoIntersectionOpenComparison,
    boundaryTwoLastEdgeOpenComparison]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [boundaryTwoIntersectionToOpenIntersection_left]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [simplicialSingularComparison_naturality]
  rfl

lemma boundaryTwoIntersectionOpenComparison_right
    (R : ModuleCat.{0} k) :
    boundaryTwoIntersectionOpenComparison R ≫
        ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen) =
      SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE
            (inf_le_right :
              boundaryTwoFirstFace ⊓ boundaryTwoRemainingFaces ≤
                boundaryTwoRemainingFaces)) R ≫
        boundaryTwoHornOpenComparison R := by
  rw [boundaryTwoIntersectionOpenComparison,
    boundaryTwoHornOpenComparison]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [boundaryTwoIntersectionToOpenIntersection_right]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [simplicialSingularComparison_naturality]
  rfl

/-- The direct sum of the comparison maps for the edge and horn pieces. -/
noncomputable def boundaryTwoPieceOpenComparison
    (R : ModuleCat.{0} k) :
    (boundaryTwoFirstFace : SSet.{0}).chainComplex R ⊞
        (boundaryTwoRemainingFaces : SSet.{0}).chainComplex R ⟶
      ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
          (TopCat.of boundaryTwoLastEdgeOpen) ⊞
        ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).obj
          (TopCat.of boundaryTwoHornOpen) :=
  biprod.map
    (boundaryTwoLastEdgeOpenComparison R)
    (boundaryTwoHornOpenComparison R)

/-- A binary biproduct of quasi-isomorphisms is a quasi-isomorphism. -/
lemma quasiIso_biprod_map
    {K₁ K₂ L₁ L₂ : ChainComplex (ModuleCat.{0} k) ℕ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [QuasiIso f] [QuasiIso g] :
    QuasiIso (biprod.map f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let F := homologyFunctor (ModuleCat.{0} k) (ComplexShape.down ℕ) n
  letI : PreservesBinaryBiproduct K₁ K₂ F :=
    preservesBinaryBiproduct_sset_homologyFunctor n K₁ K₂
  letI : PreservesBinaryBiproduct L₁ L₂ F :=
    preservesBinaryBiproduct_sset_homologyFunctor n L₁ L₂
  let eK := F.mapBiprod K₁ K₂
  let eL := F.mapBiprod L₁ L₂
  have h :
      homologyMap (biprod.map f g) n ≫ eL.hom =
        eK.hom ≫ biprod.map (homologyMap f n) (homologyMap g n) := by
    change F.map (biprod.map f g) ≫ eL.hom =
      eK.hom ≫ biprod.map (F.map f) (F.map g)
    apply biprod.hom_ext
    · calc
        (F.map (biprod.map f g) ≫ eL.hom) ≫ biprod.fst =
            F.map (biprod.map f g) ≫ (eL.hom ≫ biprod.fst) := by
              rw [Category.assoc]
        _ = F.map (biprod.map f g) ≫ F.map biprod.fst := by
              change _ ≫
                  ((F.mapBiprod L₁ L₂).hom ≫ biprod.fst) = _
              rw [Functor.mapBiprod_hom, biprod.lift_fst]
        _ = F.map (biprod.map f g ≫ biprod.fst) := by
              rw [F.map_comp]
        _ = F.map (biprod.fst ≫ f) := by rw [biprod.map_fst]
        _ = F.map biprod.fst ≫ F.map f := F.map_comp _ _
        _ = (eK.hom ≫ biprod.fst) ≫ F.map f := by
              change _ = (((F.mapBiprod K₁ K₂).hom ≫ biprod.fst) ≫ _)
              rw [Functor.mapBiprod_hom, biprod.lift_fst]
        _ = eK.hom ≫ (biprod.fst ≫ F.map f) := Category.assoc _ _ _
        _ = eK.hom ≫
            (biprod.map (F.map f) (F.map g) ≫ biprod.fst) := by
              rw [biprod.map_fst]
        _ = (eK.hom ≫ biprod.map (F.map f) (F.map g)) ≫ biprod.fst :=
              (Category.assoc _ _ _).symm
    · calc
        (F.map (biprod.map f g) ≫ eL.hom) ≫ biprod.snd =
            F.map (biprod.map f g) ≫ (eL.hom ≫ biprod.snd) := by
              rw [Category.assoc]
        _ = F.map (biprod.map f g) ≫ F.map biprod.snd := by
              change _ ≫
                  ((F.mapBiprod L₁ L₂).hom ≫ biprod.snd) = _
              rw [Functor.mapBiprod_hom, biprod.lift_snd]
        _ = F.map (biprod.map f g ≫ biprod.snd) := by
              rw [F.map_comp]
        _ = F.map (biprod.snd ≫ g) := by rw [biprod.map_snd]
        _ = F.map biprod.snd ≫ F.map g := F.map_comp _ _
        _ = (eK.hom ≫ biprod.snd) ≫ F.map g := by
              change _ = (((F.mapBiprod K₁ K₂).hom ≫ biprod.snd) ≫ _)
              rw [Functor.mapBiprod_hom, biprod.lift_snd]
        _ = eK.hom ≫ (biprod.snd ≫ F.map g) := Category.assoc _ _ _
        _ = eK.hom ≫
            (biprod.map (F.map f) (F.map g) ≫ biprod.snd) := by
              rw [biprod.map_snd]
        _ = (eK.hom ≫ biprod.map (F.map f) (F.map g)) ≫ biprod.snd :=
              (Category.assoc _ _ _).symm
  let ef := asIso (homologyMap f n)
  let eg := asIso (homologyMap g n)
  letI : IsIso (biprod.map (homologyMap f n) (homologyMap g n)) := by
    change IsIso (biprod.map ef.hom eg.hom)
    exact (biprod.mapIso ef eg).isIso_hom
  haveI : IsIso
      (homologyMap (biprod.map f g) n ≫ eL.hom) := by
    rw [h]
    change IsIso ((eK.trans (biprod.mapIso ef eg)).hom)
    exact (eK.trans (biprod.mapIso ef eg)).isIso_hom
  exact IsIso.of_isIso_comp_right _ eL.hom

noncomputable instance boundaryTwoPieceOpenComparison_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso (boundaryTwoPieceOpenComparison R) := by
  dsimp [boundaryTwoPieceOpenComparison]
  exact quasiIso_biprod_map _ _

/-- The source and target Mayer--Vietoris inclusion maps commute with the
three factored comparison maps. -/
lemma boundaryTwo_openCover_square_f
    (R : ModuleCat.{0} k) :
    (subcomplexChainShortComplex R boundaryTwoFirstFace
        boundaryTwoRemainingFaces).f ≫
      boundaryTwoPieceOpenComparison R =
    boundaryTwoIntersectionOpenComparison R ≫
      mvIncl (C := ModuleCat.{0} k) R
        (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
        (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen) := by
  change
    biprod.lift
        (SSet.chainComplexMap (SSet.Subcomplex.homOfLE inf_le_left) R)
        (-SSet.chainComplexMap (SSet.Subcomplex.homOfLE inf_le_right) R) ≫
      biprod.map
        (boundaryTwoLastEdgeOpenComparison R)
        (boundaryTwoHornOpenComparison R) =
    boundaryTwoIntersectionOpenComparison R ≫
      biprod.lift
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen))
        (-((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen))
  apply biprod.hom_ext
  · calc
      _ = SSet.chainComplexMap
            (SSet.Subcomplex.homOfLE inf_le_left) R ≫
          boundaryTwoLastEdgeOpenComparison R := by
            rw [Category.assoc, biprod.map_fst, ← Category.assoc,
              biprod.lift_fst]
      _ = boundaryTwoIntersectionOpenComparison R ≫
          ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
            (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen) :=
        (boundaryTwoIntersectionOpenComparison_left R).symm
      _ = _ := by rw [Category.assoc, biprod.lift_fst]
  · calc
      _ = -(SSet.chainComplexMap
            (SSet.Subcomplex.homOfLE inf_le_right) R ≫
          boundaryTwoHornOpenComparison R) := by
            rw [Category.assoc, biprod.map_snd, ← Category.assoc,
              biprod.lift_snd, Preadditive.neg_comp]
      _ = -(boundaryTwoIntersectionOpenComparison R ≫
          ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
            (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)) :=
        congrArg Neg.neg (boundaryTwoIntersectionOpenComparison_right R).symm
      _ = _ := by
        rw [Category.assoc, biprod.lift_snd, Preadditive.comp_neg]

/-- The singular-chain pushout associated to the two open neighborhoods. -/
abbrev boundaryTwoCoverChains (R : ModuleCat.{0} k) :
    ChainComplex (ModuleCat.{0} k) ℕ :=
  coverChains (C := ModuleCat.{0} k) R
    (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
    (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)

/-- The map from the simplicial-chain pushout to the singular open-cover
pushout. -/
noncomputable def boundaryTwoUnionToCoverChains
    (R : ModuleCat.{0} k) :
    ((boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces : _) :
        SSet.{0}).chainComplex R ⟶
      boundaryTwoCoverChains R :=
  (boundaryTwoChainIsPushout R).desc
    (boundaryTwoLastEdgeOpenComparison R ≫ biprod.inl ≫
      cokernel.π
        (mvIncl (C := ModuleCat.{0} k) R
          (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
          (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)))
    (boundaryTwoHornOpenComparison R ≫ biprod.inr ≫
      cokernel.π
        (mvIncl (C := ModuleCat.{0} k) R
          (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
          (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)))
    (by
      let iL := ((singularChainComplexFunctor
        (ModuleCat.{0} k)).obj R).map
          (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
      let iR := ((singularChainComplexFunctor
        (ModuleCat.{0} k)).obj R).map
          (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
      let htarget := SingularExcision.cokernelIsPushout iL iR
      calc
        SSet.chainComplexMap
              (SSet.Subcomplex.homOfLE inf_le_left) R ≫
            boundaryTwoLastEdgeOpenComparison R ≫ biprod.inl ≫
              cokernel.π (mvIncl (C := ModuleCat.{0} k) R
                (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
                (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)) =
          boundaryTwoIntersectionOpenComparison R ≫ iL ≫ biprod.inl ≫
              cokernel.π (mvIncl (C := ModuleCat.{0} k) R
                (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
                (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)) := by
            simp only [← Category.assoc]
            rw [boundaryTwoIntersectionOpenComparison_left]
        _ = boundaryTwoIntersectionOpenComparison R ≫ iR ≫ biprod.inr ≫
              cokernel.π (mvIncl (C := ModuleCat.{0} k) R
                (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
                (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)) := by
            simpa only [htarget, iL, iR,
              SingularExcision.cokernelPushoutInl,
              SingularExcision.cokernelPushoutInr,
              SingularExcision.mvIncl_eq_pushoutRelation,
              Category.assoc] using
              congrArg
                (fun q => boundaryTwoIntersectionOpenComparison R ≫ q)
                htarget.w
        _ = SSet.chainComplexMap
              (SSet.Subcomplex.homOfLE inf_le_right) R ≫
            boundaryTwoHornOpenComparison R ≫ biprod.inr ≫
              cokernel.π (mvIncl (C := ModuleCat.{0} k) R
                (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
                (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)) := by
            simp only [← Category.assoc]
            rw [boundaryTwoIntersectionOpenComparison_right])

/-- The quotient maps in the source and target Mayer--Vietoris short
complexes commute. -/
lemma boundaryTwo_openCover_square_g
    (R : ModuleCat.{0} k) :
    (subcomplexChainShortComplex R boundaryTwoFirstFace
        boundaryTwoRemainingFaces).g ≫
      boundaryTwoUnionToCoverChains R =
    boundaryTwoPieceOpenComparison R ≫
      cokernel.π
        (mvIncl (C := ModuleCat.{0} k) R
          (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
          (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)) := by
  apply biprod.hom_ext'
  · change
      (biprod.inl ≫
          biprod.desc
            (SSet.chainComplexMap
              (SSet.Subcomplex.homOfLE le_sup_left) R)
            (SSet.chainComplexMap
              (SSet.Subcomplex.homOfLE le_sup_right) R)) ≫
          boundaryTwoUnionToCoverChains R =
        (biprod.inl ≫
          biprod.map
            (boundaryTwoLastEdgeOpenComparison R)
            (boundaryTwoHornOpenComparison R)) ≫
          cokernel.π
            (mvIncl (C := ModuleCat.{0} k) R
              (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
              (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen))
    rw [biprod.inl_desc, biprod.inl_map]
    exact (boundaryTwoChainIsPushout R).inl_desc _ _ _
  · change
      (biprod.inr ≫
          biprod.desc
            (SSet.chainComplexMap
              (SSet.Subcomplex.homOfLE le_sup_left) R)
            (SSet.chainComplexMap
              (SSet.Subcomplex.homOfLE le_sup_right) R)) ≫
          boundaryTwoUnionToCoverChains R =
        (biprod.inr ≫
          biprod.map
            (boundaryTwoLastEdgeOpenComparison R)
            (boundaryTwoHornOpenComparison R)) ≫
          cokernel.π
            (mvIncl (C := ModuleCat.{0} k) R
              (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
              (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen))
    rw [biprod.inr_desc, biprod.inr_map]
    exact (boundaryTwoChainIsPushout R).inr_desc _ _ _

/-- Morphism from the simplicial Mayer--Vietoris short complex to the
singular open-cover short complex. -/
noncomputable def boundaryTwoOpenCoverShortComplexHom
    (R : ModuleCat.{0} k) :
    subcomplexChainShortComplex R boundaryTwoFirstFace
        boundaryTwoRemainingFaces ⟶
      triadShortComplex (C := ModuleCat.{0} k) R
        (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
        (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen) :=
  ShortComplex.Hom.mk
    (boundaryTwoIntersectionOpenComparison R)
    (boundaryTwoPieceOpenComparison R)
    (boundaryTwoUnionToCoverChains R)
    (boundaryTwo_openCover_square_f R).symm
    (boundaryTwo_openCover_square_g R).symm

/-- The map from the simplicial union to open-cover chains is a
quasi-isomorphism. -/
noncomputable instance boundaryTwoUnionToCoverChains_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso (boundaryTwoUnionToCoverChains R) := by
  letI : QuasiIso (boundaryTwoOpenCoverShortComplexHom R).τ₁ := by
    change QuasiIso (boundaryTwoIntersectionOpenComparison R)
    infer_instance
  letI : QuasiIso (boundaryTwoOpenCoverShortComplexHom R).τ₂ := by
    change QuasiIso (boundaryTwoPieceOpenComparison R)
    infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (boundaryTwoOpenCoverShortComplexHom R)
    (boundaryTwoChainShortExact R)
    (triad_shortExact (C := ModuleCat.{0} k) R
      (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
      (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen))
    inferInstance inferInstance

/-- Open-cover chains map canonically to singular chains of the whole
boundary. -/
noncomputable def boundaryTwoCoverComparison
    (R : ModuleCat.{0} k) :
    boundaryTwoCoverChains R ⟶ singularChainsOfRealization R boundaryTwoSSet :=
  coverComparison (C := ModuleCat.{0} k) R
    (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
    (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
    (subtypeIncl |boundaryTwoSSet| boundaryTwoLastEdgeOpen)
    (subtypeIncl |boundaryTwoSSet| boundaryTwoHornOpen)
    (subset_square_comm boundaryTwoLastEdgeOpen boundaryTwoHornOpen)

noncomputable instance boundaryTwoCoverComparison_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso (boundaryTwoCoverComparison R) := by
  exact SingularExcision.IsExcisiveSubspaces_of_openCover (R := R)
    isOpen_boundaryTwoLastEdgeOpen isOpen_boundaryTwoHornOpen
    boundaryTwo_open_cover

lemma boundaryTwoLastEdgeToOpen_subtype :
    boundaryTwoLastEdgeToOpen ≫
        subtypeIncl |boundaryTwoSSet| boundaryTwoLastEdgeOpen =
      boundaryTwoLastEdgeIncl := by
  ext x
  rfl

lemma boundaryTwoHornToOpen_subtype :
    boundaryTwoHornToOpen ≫
        subtypeIncl |boundaryTwoSSet| boundaryTwoHornOpen =
      boundaryTwoHornIncl := by
  ext x
  rfl

@[reassoc]
lemma boundaryTwoCoverComparison_π
    (R : ModuleCat.{0} k) :
    cokernel.π
          (mvIncl (C := ModuleCat.{0} k) R
            (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
            (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)) ≫
        boundaryTwoCoverComparison R =
      coverToX (C := ModuleCat.{0} k) R
        (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
        (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
        (subtypeIncl |boundaryTwoSSet| boundaryTwoLastEdgeOpen)
        (subtypeIncl |boundaryTwoSSet| boundaryTwoHornOpen)
        (subset_square_comm boundaryTwoLastEdgeOpen boundaryTwoHornOpen) := by
  unfold boundaryTwoCoverComparison coverComparison
  exact cokernel.π_desc _ _ _

lemma boundaryTwoUnionToCoverComparison_first
    (R : ModuleCat.{0} k) :
    SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE
            (le_sup_left :
              boundaryTwoFirstFace ≤
                boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)) R ≫
        boundaryTwoUnionToCoverChains R ≫
        boundaryTwoCoverComparison R =
      boundaryTwoLastEdgeOpenComparison R ≫
        ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (subtypeIncl |boundaryTwoSSet| boundaryTwoLastEdgeOpen) := by
  unfold boundaryTwoUnionToCoverChains
  rw [← Category.assoc,
    (boundaryTwoChainIsPushout R).inl_desc]
  calc
    _ = boundaryTwoLastEdgeOpenComparison R ≫ biprod.inl ≫
        coverToX (C := ModuleCat.{0} k) R
          (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
          (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
          (subtypeIncl |boundaryTwoSSet| boundaryTwoLastEdgeOpen)
          (subtypeIncl |boundaryTwoSSet| boundaryTwoHornOpen)
          (subset_square_comm boundaryTwoLastEdgeOpen
            boundaryTwoHornOpen) := by
      simpa only [Category.assoc] using congrArg
        (fun q => boundaryTwoLastEdgeOpenComparison R ≫ biprod.inl ≫ q)
        (boundaryTwoCoverComparison_π R)
    _ = _ := by
      rw [coverToX, biprod.inl_desc]

lemma boundaryTwoUnionToCoverComparison_remaining
    (R : ModuleCat.{0} k) :
    SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE
            (le_sup_right :
              boundaryTwoRemainingFaces ≤
                boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces)) R ≫
        boundaryTwoUnionToCoverChains R ≫
        boundaryTwoCoverComparison R =
      boundaryTwoHornOpenComparison R ≫
        ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
          (subtypeIncl |boundaryTwoSSet| boundaryTwoHornOpen) := by
  unfold boundaryTwoUnionToCoverChains
  rw [← Category.assoc,
    (boundaryTwoChainIsPushout R).inr_desc]
  calc
    _ = boundaryTwoHornOpenComparison R ≫ biprod.inr ≫
        coverToX (C := ModuleCat.{0} k) R
          (interInclLeft boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
          (interInclRight boundaryTwoLastEdgeOpen boundaryTwoHornOpen)
          (subtypeIncl |boundaryTwoSSet| boundaryTwoLastEdgeOpen)
          (subtypeIncl |boundaryTwoSSet| boundaryTwoHornOpen)
          (subset_square_comm boundaryTwoLastEdgeOpen
            boundaryTwoHornOpen) := by
      simpa only [Category.assoc] using congrArg
        (fun q => boundaryTwoHornOpenComparison R ≫ biprod.inr ≫ q)
        (boundaryTwoCoverComparison_π R)
    _ = _ := by
      rw [coverToX, biprod.inr_desc]

/-- Simplicial inclusion of the last edge into the whole boundary. -/
def boundaryTwoFirstFaceIncl :
    (boundaryTwoFirstFace : SSet.{0}) ⟶ boundaryTwoSSet :=
  SSet.Subcomplex.homOfLE (by
    rw [boundary_two_eq_face_sup]
    exact (le_sup_left :
      boundaryTwoFirstFace ≤
        boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))

/-- Simplicial inclusion of the horn into the whole boundary. -/
def boundaryTwoRemainingFacesIncl :
    (boundaryTwoRemainingFaces : SSet.{0}) ⟶ boundaryTwoSSet :=
  SSet.Subcomplex.homOfLE (by
    rw [boundary_two_eq_face_sup]
    exact (le_sup_right :
      boundaryTwoRemainingFaces ≤
        boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces))

lemma boundaryTwoFirstFace_sup_comp_iso_inv :
    SSet.Subcomplex.homOfLE
          (le_sup_left :
            boundaryTwoFirstFace ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces) ≫
        boundaryTwoIsoSup.inv =
      boundaryTwoFirstFaceIncl := rfl

lemma boundaryTwoRemainingFaces_sup_comp_iso_inv :
    SSet.Subcomplex.homOfLE
          (le_sup_right :
            boundaryTwoRemainingFaces ≤
              boundaryTwoFirstFace ⊔ boundaryTwoRemainingFaces) ≫
        boundaryTwoIsoSup.inv =
      boundaryTwoRemainingFacesIncl := rfl

/-- The open-cover factorization recombines to the canonical comparison on
the simplicial boundary. -/
lemma boundaryTwoUnion_cover_factor
    (R : ModuleCat.{0} k) :
    boundaryTwoUnionToCoverChains R ≫ boundaryTwoCoverComparison R =
      SSet.chainComplexMap boundaryTwoIsoSup.inv R ≫
        simplicialSingularComparison R boundaryTwoSSet := by
  apply (boundaryTwoChainIsPushout R).hom_ext
  · calc
      SSet.chainComplexMap
            (SSet.Subcomplex.homOfLE le_sup_left) R ≫
          boundaryTwoUnionToCoverChains R ≫
          boundaryTwoCoverComparison R =
        boundaryTwoLastEdgeOpenComparison R ≫
          ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
            (subtypeIncl |boundaryTwoSSet| boundaryTwoLastEdgeOpen) :=
        boundaryTwoUnionToCoverComparison_first R
      _ = simplicialSingularComparison R
            (boundaryTwoFirstFace : SSet.{0}) ≫
          ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
            (boundaryTwoLastEdgeToOpen ≫
              subtypeIncl |boundaryTwoSSet| boundaryTwoLastEdgeOpen) := by
        rw [boundaryTwoLastEdgeOpenComparison, Category.assoc,
          Functor.map_comp]
      _ = simplicialSingularComparison R
            (boundaryTwoFirstFace : SSet.{0}) ≫
          ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
            boundaryTwoLastEdgeIncl := by
        rw [boundaryTwoLastEdgeToOpen_subtype]
      _ = SSet.chainComplexMap boundaryTwoFirstFaceIncl R ≫
          simplicialSingularComparison R boundaryTwoSSet := by
        rw [simplicialSingularComparison_naturality]
        rfl
      _ = SSet.chainComplexMap
            (SSet.Subcomplex.homOfLE le_sup_left) R ≫
          SSet.chainComplexMap boundaryTwoIsoSup.inv R ≫
            simplicialSingularComparison R boundaryTwoSSet := by
        rw [← Category.assoc, ← Functor.map_comp,
          boundaryTwoFirstFace_sup_comp_iso_inv]
  · calc
      SSet.chainComplexMap
            (SSet.Subcomplex.homOfLE le_sup_right) R ≫
          boundaryTwoUnionToCoverChains R ≫
          boundaryTwoCoverComparison R =
        boundaryTwoHornOpenComparison R ≫
          ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
            (subtypeIncl |boundaryTwoSSet| boundaryTwoHornOpen) :=
        boundaryTwoUnionToCoverComparison_remaining R
      _ = simplicialSingularComparison R
            (boundaryTwoRemainingFaces : SSet.{0}) ≫
          ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
            (boundaryTwoHornToOpen ≫
              subtypeIncl |boundaryTwoSSet| boundaryTwoHornOpen) := by
        rw [boundaryTwoHornOpenComparison, Category.assoc,
          Functor.map_comp]
      _ = simplicialSingularComparison R
            (boundaryTwoRemainingFaces : SSet.{0}) ≫
          ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map
            boundaryTwoHornIncl := by
        rw [boundaryTwoHornToOpen_subtype]
      _ = SSet.chainComplexMap boundaryTwoRemainingFacesIncl R ≫
          simplicialSingularComparison R boundaryTwoSSet := by
        rw [simplicialSingularComparison_naturality]
        rfl
      _ = SSet.chainComplexMap
            (SSet.Subcomplex.homOfLE le_sup_right) R ≫
          SSet.chainComplexMap boundaryTwoIsoSup.inv R ≫
            simplicialSingularComparison R boundaryTwoSSet := by
        rw [← Category.assoc, ← Functor.map_comp,
          boundaryTwoRemainingFaces_sup_comp_iso_inv]

/-- The canonical adjunction-unit comparison is a quasi-isomorphism for
the boundary of the standard two-simplex. -/
theorem simplicialSingularComparison_boundaryTwo_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso (simplicialSingularComparison R boundaryTwoSSet) := by
  letI : QuasiIso
      (boundaryTwoUnionToCoverChains R ≫ boundaryTwoCoverComparison R) := by
    infer_instance
  letI : QuasiIso
      (SSet.chainComplexMap boundaryTwoIsoSup.inv R ≫
        simplicialSingularComparison R boundaryTwoSSet) := by
    rw [← boundaryTwoUnion_cover_factor]
    infer_instance
  exact quasiIso_of_comp_left
    (SSet.chainComplexMap boundaryTwoIsoSup.inv R)
    (simplicialSingularComparison R boundaryTwoSSet)

/-- Supporting normalized-chain version of the boundary comparison. -/
theorem normalizedSimplicialSingularComparison_boundaryTwo_quasiIso
    (R : ModuleCat.{0} k) :
    QuasiIso
      (normalizedSimplicialSingularComparison R boundaryTwoSSet) :=
  (normalizedSimplicialSingularComparison_quasiIso_iff R
    boundaryTwoSSet).2
    (simplicialSingularComparison_boundaryTwo_quasiIso R)

