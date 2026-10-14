import GaussBonnetChern.SubdivisionChainMap
import Mathlib.Algebra.Homology.Homotopy

/-! # Canonical affine cones for a subdivision homotopy

Cones are formed inside an actual standard simplex and are represented by
actual singular simplices. The cone boundary identity below is the geometric
input to the recursive construction of a support-preserving subdivision
homotopy; the full recursive homotopy is not asserted merely by defining a cone.
-/

noncomputable section

universe u

namespace GaussBonnetChern

open CategoryTheory Convexity
open scoped BigOperators Simplicial

variable {I : Type u} [Fintype I]

/-- The affine cone obtained by placing the apex first in the ordered vertices. -/
def affineSimplexCone {n : ℕ} (p : StdSimplex ℝ I)
    (v : Fin (n + 1) → StdSimplex ℝ I) :
    C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ I) :=
  simplexAffineContinuous (Fin.cons p v)

theorem affineSimplexCone_face_zero {n : ℕ} (p : StdSimplex ℝ I)
    (v : Fin (n + 1) → StdSimplex ℝ I) :
    (affineSimplexCone p v).comp (standardSimplexFace 0) = simplexAffineContinuous v := by
  change (simplexAffineContinuous (Fin.cons p v)).comp _ = _
  rw [standardSimplexFace, simplexAffineContinuous_comp_vertexMap]
  congr 1

theorem affineSimplexCone_face_succ {n : ℕ} (p : StdSimplex ℝ I)
    (v : Fin (n + 2) → StdSimplex ℝ I) (i : Fin (n + 2)) :
    (affineSimplexCone p v).comp (standardSimplexFace i.succ) =
      affineSimplexCone p (v ∘ i.succAbove) := by
  change (simplexAffineContinuous (Fin.cons p v)).comp _ = _
  rw [standardSimplexFace, simplexAffineContinuous_comp_vertexMap]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp [Function.comp_def]

/-- The boundary of an affine cone is the original affine simplex minus
the cones on its signed boundary faces. -/
theorem affineSimplexCone_boundary {n : ℕ} (p : StdSimplex ℝ I)
    (v : Fin (n + 2) → StdSimplex ℝ I) :
    singularSimplexGenerator (affineSimplexCone p v) ≫
        (singularChains (StdSimplex ℝ I)).d (n + 2) (n + 1) =
      singularSimplexGenerator (simplexAffineContinuous v) -
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          singularSimplexGenerator (affineSimplexCone p (v ∘ i.succAbove)) := by
  rw [singularSimplexGenerator_boundary, Fin.sum_univ_succ]
  simp only [singularSimplexFace, affineSimplexCone_face_zero, affineSimplexCone_face_succ,
    Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

/-- In degree zero the boundary of the cone is the point minus the apex. -/
theorem affineSimplexCone_boundary_zero (p : StdSimplex ℝ I)
    (v : Fin 1 → StdSimplex ℝ I) :
    singularSimplexGenerator (affineSimplexCone p v) ≫
        (singularChains (StdSimplex ℝ I)).d 1 0 =
      singularSimplexGenerator (simplexAffineContinuous v) -
        singularSimplexGenerator (simplexAffineContinuous (fun _ : Fin 1 ↦ p)) := by
  rw [singularSimplexGenerator_boundary, Fin.sum_univ_two]
  have hface : (affineSimplexCone p v).comp (standardSimplexFace 1) =
      simplexAffineContinuous (fun _ : Fin 1 ↦ p) := by
    change (simplexAffineContinuous (Fin.cons p v)).comp _ = _
    rw [standardSimplexFace, simplexAffineContinuous_comp_vertexMap]
    congr 1
    funext i
    fin_cases i
    rfl
  simp only [singularSimplexFace, affineSimplexCone_face_zero, hface]
  norm_num [sub_eq_add_neg]

/-- Ordered vertex values of an arbitrary singular simplex with simplex target. -/
def singularSimplexVertices {n : ℕ}
    (s : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ I)) :
    Fin (n + 1) → StdSimplex ℝ I := fun i ↦ s (.single i)

omit [Fintype I] in
theorem singularSimplexVertices_face {n : ℕ}
    (s : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ I)) (i : Fin (n + 2)) :
    singularSimplexVertices (singularSimplexFace s i) = singularSimplexVertices s ∘ i.succAbove := by
  funext j
  simp [singularSimplexVertices, singularSimplexFace, standardSimplexFace]

@[simp]
theorem singularSimplexVertices_affine {n : ℕ} (v : Fin (n + 1) → StdSimplex ℝ I) :
    singularSimplexVertices (simplexAffineContinuous v) = v := by
  funext i
  exact simplexAffineContinuous_single v i

/-- Affine interpolation of vertex values, linearly extended to actual singular chains. -/
def affineInterpolationDegree (I : Type u) [Fintype I] (n : ℕ) :
    (singularChains (StdSimplex ℝ I)).X n ⟶ (singularChains (StdSimplex ℝ I)).X n :=
  Limits.Sigma.desc (fun t ↦ singularSimplexGenerator (simplexAffineContinuous
    (singularSimplexVertices
      (TopCat.toSSetObjEquiv (TopCat.of (StdSimplex ℝ I)) (Opposite.op ⦋n⦌) t))))

/-- Cone on the affine interpolation, linearly extended to actual singular chains. -/
def affineConeDegree (p : StdSimplex ℝ I) (n : ℕ) :
    (singularChains (StdSimplex ℝ I)).X n ⟶ (singularChains (StdSimplex ℝ I)).X (n + 1) :=
  Limits.Sigma.desc (fun t ↦ singularSimplexGenerator (affineSimplexCone p
    (singularSimplexVertices
      (TopCat.toSSetObjEquiv (TopCat.of (StdSimplex ℝ I)) (Opposite.op ⦋n⦌) t))))

set_option backward.isDefEq.respectTransparency false in
theorem singularSimplexGenerator_comp_affineInterpolation {n : ℕ}
    (s : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ I)) :
    singularSimplexGenerator s ≫ affineInterpolationDegree I n =
      singularSimplexGenerator (simplexAffineContinuous (singularSimplexVertices s)) := by
  simp only [singularSimplexGenerator, affineInterpolationDegree, SSet.ιChainComplex]
  rw [Limits.Sigma.ι_comp_desc]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem singularSimplexGenerator_comp_affineCone {n : ℕ} (p : StdSimplex ℝ I)
    (s : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ I)) :
    singularSimplexGenerator s ≫ affineConeDegree p n =
      singularSimplexGenerator (affineSimplexCone p (singularSimplexVertices s)) := by
  simp only [singularSimplexGenerator, affineConeDegree, SSet.ιChainComplex]
  rw [Limits.Sigma.ι_comp_desc]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The genuine positive-degree cone identity on the actual singular chains.
The right side is affine interpolation, so this is not a contraction of arbitrary
singular simplices to their vertices by definitional fiat. -/
theorem affineConeDegree_boundary (p : StdSimplex ℝ I) (n : ℕ) :
    affineConeDegree p (n + 1) ≫ (singularChains (StdSimplex ℝ I)).d (n + 2) (n + 1) +
        (singularChains (StdSimplex ℝ I)).d (n + 1) n ≫ affineConeDegree p n =
      affineInterpolationDegree I (n + 1) := by
  apply (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ I))).chainComplex_hom_ext
    (R := ModuleCat.of ℝ (ULift.{u} ℝ))
  intro t
  let s := TopCat.toSSetObjEquiv (TopCat.of (StdSimplex ℝ I)) (Opposite.op ⦋n + 1⦌) t
  have ht : singularSimplexGenerator s =
      (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ I))).ιChainComplex t := by
    simp [s, singularSimplexGenerator]
  rw [← ht, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
    singularSimplexGenerator_comp_affineCone, affineSimplexCone_boundary,
    singularSimplexGenerator_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
    singularSimplexGenerator_comp_affineCone, singularSimplexVertices_face,
    singularSimplexGenerator_comp_affineInterpolation]
  exact sub_add_cancel _ _

set_option backward.isDefEq.respectTransparency false in
/-- An actual positive-degree cycle fixed by affine interpolation has the
explicit primitive obtained by applying the cone operator. -/
theorem affineCycle_cone_primitive (p : StdSimplex ℝ I) (n : ℕ)
    {A : ModuleCat.{u} ℝ} (z : A ⟶ (singularChains (StdSimplex ℝ I)).X (n + 1))
    (hcycle : z ≫ (singularChains (StdSimplex ℝ I)).d (n + 1) n = 0)
    (haffine : z ≫ affineInterpolationDegree I (n + 1) = z) :
    (z ≫ affineConeDegree p (n + 1)) ≫
      (singularChains (StdSimplex ℝ I)).d (n + 2) (n + 1) = z := by
  have h := congrArg (fun f ↦ z ≫ f) (affineConeDegree_boundary p n)
  simpa only [Preadditive.comp_add, ← Category.assoc, hcycle, Limits.zero_comp, add_zero, haffine] using h

/-- Affine interpolation fixes every genuinely affine singular generator. -/
theorem affineGenerator_comp_affineInterpolation {n : ℕ}
    (v : Fin (n + 1) → StdSimplex ℝ I) :
    singularSimplexGenerator (simplexAffineContinuous v) ≫ affineInterpolationDegree I n =
      singularSimplexGenerator (simplexAffineContinuous v) := by
  rw [singularSimplexGenerator_comp_affineInterpolation, singularSimplexVertices_affine]

set_option backward.isDefEq.respectTransparency false in
/-- Every chain produced by the cone is fixed by affine interpolation. -/
theorem affineConeDegree_comp_affineInterpolation (p : StdSimplex ℝ I) (n : ℕ) :
    affineConeDegree p n ≫ affineInterpolationDegree I (n + 1) = affineConeDegree p n := by
  apply (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ I))).chainComplex_hom_ext
    (R := ModuleCat.of ℝ (ULift.{u} ℝ))
  intro t
  let s := TopCat.toSSetObjEquiv (TopCat.of (StdSimplex ℝ I)) (Opposite.op ⦋n⦌) t
  have ht : singularSimplexGenerator s =
      (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ I))).ιChainComplex t := by
    simp [s, singularSimplexGenerator]
  rw [← ht, ← Category.assoc, singularSimplexGenerator_comp_affineCone,
    affineSimplexCone, affineGenerator_comp_affineInterpolation]

set_option backward.isDefEq.respectTransparency false in
/-- Affine interpolation is an actual idempotent operator on each singular-chain group. -/
theorem affineInterpolationDegree_idempotent (I : Type u) [Fintype I] (n : ℕ) :
    affineInterpolationDegree I n ≫ affineInterpolationDegree I n = affineInterpolationDegree I n := by
  apply (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ I))).chainComplex_hom_ext
    (R := ModuleCat.of ℝ (ULift.{u} ℝ))
  intro t
  let s := TopCat.toSSetObjEquiv (TopCat.of (StdSimplex ℝ I)) (Opposite.op ⦋n⦌) t
  have ht : singularSimplexGenerator s =
      (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ I))).ιChainComplex t := by
    simp [s, singularSimplexGenerator]
  rw [← ht, ← Category.assoc, singularSimplexGenerator_comp_affineInterpolation,
    affineGenerator_comp_affineInterpolation]

/-- Postcomposition of a canonical affine cone stays in the original singular
simplex image. This is the support control required by the later recursion. -/
theorem postcompose_affineCone_range_subset {n : ℕ} {X : Type*} [TopologicalSpace X]
    (s : C(StdSimplex ℝ I, X)) (p : StdSimplex ℝ I)
    (v : Fin (n + 1) → StdSimplex ℝ I) :
    Set.range (s.comp (affineSimplexCone p v)) ⊆ Set.range s := by
  rintro _ ⟨x, rfl⟩
  exact ⟨affineSimplexCone p v x, rfl⟩

/-- Affine maps of actual standard simplices are closed under composition. -/
theorem simplexAffineContinuous_comp {J K : Type*} [Fintype J] [Fintype K]
    (v : J → StdSimplex ℝ K) (w : I → StdSimplex ℝ J) :
    (simplexAffineContinuous v).comp (simplexAffineContinuous w) =
      simplexAffineContinuous (fun i ↦ simplexAffineContinuous v (w i)) := by
  have h : (StdSimplex.affineMapMk (R := ℝ) v).comp
      (StdSimplex.affineMapMk (R := ℝ) w) =
      StdSimplex.affineMapMk (R := ℝ) (fun i ↦ simplexAffineContinuous v (w i)) := by
    apply StdSimplex.affineMap_ext
    intro i
    simp [simplexAffineContinuous]
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ I) (StdSimplex ℝ K) ↦ f x) h

/-- Functorial postcomposition on the project's singular-chain complex. -/
def singularChainPostcompose {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : singularChains X ⟶ singularChains Y :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
    (ModuleCat.of ℝ (ULift.{u} ℝ))

set_option backward.isDefEq.respectTransparency false in
theorem singularSimplexGenerator_postcompose {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}
    (s : C(StdSimplex ℝ (Fin (n + 1)), X)) (f : C(X, Y)) :
    singularSimplexGenerator s ≫ (singularChainPostcompose f).f n =
      singularSimplexGenerator (f.comp s) := by
  rw [singularSimplexGenerator, singularChainPostcompose, SSet.ι_chainComplexMap_f]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Geometric subdivision is natural under continuous postcomposition. -/
theorem barycentricSubdivisionDegree_postcompose {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    barycentricSubdivisionDegree X n ≫ (singularChainPostcompose f).f n =
      (singularChainPostcompose f).f n ≫ barycentricSubdivisionDegree Y n := by
  apply (TopCat.toSSet.obj (TopCat.of X)).chainComplex_hom_ext
    (R := ModuleCat.of ℝ (ULift.{u} ℝ))
  intro t
  let s := TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌) t
  have ht : singularSimplexGenerator s =
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex t := by
    simp [s, singularSimplexGenerator]
  rw [← ht, ← Category.assoc, singularSimplexGenerator_comp_subdivision,
    Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, singularSimplexGenerator_postcompose]
  rw [← Category.assoc, singularSimplexGenerator_postcompose,
    singularSimplexGenerator_comp_subdivision]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The signed subdivision of an affine generator is still an affine chain. -/
theorem affineGenerator_subdivision_interpolation {n : ℕ}
    (v : Fin (n + 1) → StdSimplex ℝ I) :
    (singularSimplexGenerator (simplexAffineContinuous v) ≫
        barycentricSubdivisionDegree (StdSimplex ℝ I) n) ≫ affineInterpolationDegree I n =
      singularSimplexGenerator (simplexAffineContinuous v) ≫
        barycentricSubdivisionDegree (StdSimplex ℝ I) n := by
  rw [singularSimplexGenerator_comp_subdivision, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Preadditive.zsmul_comp]
  unfold barycentricSingularSimplex barycentricSimplex
  rw [simplexAffineContinuous_comp, affineGenerator_comp_affineInterpolation]

set_option backward.isDefEq.respectTransparency false in
/-- Affine interpolation commutes with the actual positive-degree boundary. -/
theorem affineInterpolationDegree_boundary (I : Type u) [Fintype I] (n : ℕ) :
    affineInterpolationDegree I (n + 1) ≫ (singularChains (StdSimplex ℝ I)).d (n + 1) n =
      (singularChains (StdSimplex ℝ I)).d (n + 1) n ≫ affineInterpolationDegree I n := by
  apply (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ I))).chainComplex_hom_ext
    (R := ModuleCat.of ℝ (ULift.{u} ℝ))
  intro t
  let s := TopCat.toSSetObjEquiv (TopCat.of (StdSimplex ℝ I)) (Opposite.op ⦋n + 1⦌) t
  have ht : singularSimplexGenerator s =
      (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ I))).ιChainComplex t := by
    simp [s, singularSimplexGenerator]
  rw [← ht, ← Category.assoc, singularSimplexGenerator_comp_affineInterpolation,
    singularSimplexGenerator_boundary, ← Category.assoc, singularSimplexGenerator_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
    singularSimplexGenerator_comp_affineInterpolation]
  simp only [singularSimplexVertices_face]
  simp only [singularSimplexFace, standardSimplexFace,
    simplexAffineContinuous_comp_vertexMap]

theorem simplexAffineContinuous_vertices_identity :
    simplexAffineContinuous (fun i : I ↦ (StdSimplex.single i : StdSimplex ℝ I)) =
      ContinuousMap.id _ := by
  have h : StdSimplex.affineMapMk (R := ℝ)
      (fun i : I ↦ (StdSimplex.single i : StdSimplex ℝ I)) =
      ConvexSpace.AffineMap.id (R := ℝ) (StdSimplex ℝ I) := by
    apply StdSimplex.affineMap_ext
    intro i
    simp
  exact ContinuousMap.ext (fun x ↦ congrArg
    (fun f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ I) (StdSimplex ℝ I) ↦ f x) h)

theorem barycentricSimplex_zero (σ : Equiv.Perm (Fin 1)) :
    barycentricSimplex σ = ContinuousMap.id _ := by
  have hv : barycentricFlagVertex σ = fun i : Fin 1 ↦ (StdSimplex.single i : StdSimplex ℝ (Fin 1)) := by
    funext i
    apply StdSimplex.ext
    ext j
    fin_cases i
    fin_cases j
    simp
  rw [barycentricSimplex, hv, simplexAffineContinuous_vertices_identity]

set_option backward.isDefEq.respectTransparency false in
/-- Degree zero subdivision equals identity; no augmentation error is discarded. -/
theorem barycentricSubdivisionDegree_zero (X : Type u) [TopologicalSpace X] :
    barycentricSubdivisionDegree X 0 = 𝟙 _ := by
  have hg (s : C(StdSimplex ℝ (Fin 1), X)) :
      singularSimplexGenerator s ≫ barycentricSubdivisionDegree X 0 =
        singularSimplexGenerator s := by
    rw [singularSimplexGenerator_comp_subdivision]
    simp [barycentricSingularSimplex, barycentricSimplex_zero]
  apply (TopCat.toSSet.obj (TopCat.of X)).chainComplex_hom_ext
    (R := ModuleCat.of ℝ (ULift.{u} ℝ))
  intro t
  let s := TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋0⦌) t
  have hi : singularSimplexGenerator s = singularSimplexGenerator s ≫ 𝟙 ((singularChains X).X 0) :=
    (Category.comp_id (singularSimplexGenerator s)).symm
  simpa only [s, singularSimplexGenerator, Equiv.symm_apply_apply] using (hg s).trans hi

/-- A universe-matched canonical simplex, so its coefficient object is exactly
the coefficient object of the ambient project's singular chains. -/
abbrev canonicalSingularSimplex (n : ℕ) := StdSimplex ℝ (ULift.{u} (Fin (n + 1)))

def canonicalSimplexInclusion (n : ℕ) :
    C(StdSimplex ℝ (Fin (n + 1)), canonicalSingularSimplex.{u} n) :=
  simplexAffineContinuous (fun i ↦ StdSimplex.single (ULift.up i))

def canonicalSimplexProjection (n : ℕ) :
    C(canonicalSingularSimplex.{u} n, StdSimplex ℝ (Fin (n + 1))) :=
  simplexAffineContinuous (fun i ↦ StdSimplex.single i.down)

theorem canonicalSimplexProjection_comp_inclusion (n : ℕ) :
    (canonicalSimplexProjection.{u} n).comp (canonicalSimplexInclusion n) =
      ContinuousMap.id _ := by
  rw [canonicalSimplexProjection, canonicalSimplexInclusion, simplexAffineContinuous_comp]
  simp only [simplexAffineContinuous_single]
  exact simplexAffineContinuous_vertices_identity

def canonicalSimplexPostcompose {X : Type u} [TopologicalSpace X] {n : ℕ}
    (s : C(StdSimplex ℝ (Fin (n + 1)), X)) : C(canonicalSingularSimplex.{u} n, X) :=
  s.comp (canonicalSimplexProjection n)

theorem canonicalSimplexPostcompose_comp_inclusion {X : Type u}
    [TopologicalSpace X] {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 1)), X)) :
    (canonicalSimplexPostcompose s).comp (canonicalSimplexInclusion n) = s := by
  rw [canonicalSimplexPostcompose, ContinuousMap.comp_assoc,
    canonicalSimplexProjection_comp_inclusion, ContinuousMap.comp_id]

theorem singularChainPostcompose_comp {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    singularChainPostcompose f ≫ singularChainPostcompose g =
      singularChainPostcompose (g.comp f) := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℝ)).obj
    (ModuleCat.of ℝ (ULift.{u} ℝ))
  change F.map (TopCat.ofHom f) ≫ F.map (TopCat.ofHom g) = F.map (TopCat.ofHom (g.comp f))
  rw [← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem affineConeDegree_postcompose_interpolation {J : Type u} [Fintype J]
    (p : StdSimplex ℝ I) (n : ℕ) (v : I → StdSimplex ℝ J) :
    (affineConeDegree p n ≫ (singularChainPostcompose (simplexAffineContinuous v)).f (n + 1)) ≫
        affineInterpolationDegree J (n + 1) =
      affineConeDegree p n ≫ (singularChainPostcompose (simplexAffineContinuous v)).f (n + 1) := by
  apply (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ I))).chainComplex_hom_ext
    (R := ModuleCat.of ℝ (ULift.{u} ℝ))
  intro t
  let s := TopCat.toSSetObjEquiv (TopCat.of (StdSimplex ℝ I)) (Opposite.op ⦋n⦌) t
  have ht : singularSimplexGenerator s =
      (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ I))).ιChainComplex t := by
    simp [s, singularSimplexGenerator]
  rw [← ht, ← Category.assoc, ← Category.assoc,
    singularSimplexGenerator_comp_affineCone, singularSimplexGenerator_postcompose]
  unfold affineSimplexCone
  rw [simplexAffineContinuous_comp, affineGenerator_comp_affineInterpolation]

/-- Recursive canonical residual-cone construction. Every component is defined
on actual singular-chain coproduct generators and then continuously postcomposed.
The chain homotopy law is a separate theorem, not a structure assumption. -/
def subdivisionHomotopyDegree (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (singularChains X).X n ⟶ (singularChains X).X (n + 1) := match n with
  | 0 => 0
  | n + 1 =>
    let U := canonicalSingularSimplex.{u} (n + 1)
    let q := singularSimplexGenerator (canonicalSimplexInclusion.{u} (n + 1))
    let z := q ≫ barycentricSubdivisionDegree U (n + 1) - q -
      (q ≫ (singularChains U).d (n + 1) n) ≫ subdivisionHomotopyDegree n U
    let P := z ≫ affineConeDegree (StdSimplex.single (ULift.up (0 : Fin (n + 2)))) (n + 1)
    Limits.Sigma.desc (fun t ↦ P ≫
      (singularChainPostcompose (canonicalSimplexPostcompose
        (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n + 1⦌) t))).f (n + 2))

def canonicalSubdivisionHomotopyResidual (n : ℕ) :
    ModuleCat.of ℝ (ULift.{u} ℝ) ⟶ (singularChains (canonicalSingularSimplex.{u} (n + 1))).X (n + 1) :=
  let U := canonicalSingularSimplex.{u} (n + 1)
  let q := singularSimplexGenerator (canonicalSimplexInclusion.{u} (n + 1))
  q ≫ barycentricSubdivisionDegree U (n + 1) - q -
    (q ≫ (singularChains U).d (n + 1) n) ≫ subdivisionHomotopyDegree n U

def canonicalSubdivisionHomotopyPrimitive (n : ℕ) :
    ModuleCat.of ℝ (ULift.{u} ℝ) ⟶ (singularChains (canonicalSingularSimplex.{u} (n + 1))).X (n + 2) :=
  canonicalSubdivisionHomotopyResidual.{u} n ≫
    affineConeDegree (StdSimplex.single (ULift.up (0 : Fin (n + 2)))) (n + 1)

set_option backward.isDefEq.respectTransparency false in
theorem singularSimplexGenerator_subdivisionHomotopy_succ {X : Type u}
    [TopologicalSpace X] {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 2)), X)) :
    singularSimplexGenerator s ≫ subdivisionHomotopyDegree (n + 1) X =
      canonicalSubdivisionHomotopyPrimitive.{u} n ≫
        (singularChainPostcompose (canonicalSimplexPostcompose s)).f (n + 2) := by
  simp only [singularSimplexGenerator, subdivisionHomotopyDegree, SSet.ιChainComplex]
  rw [Limits.Sigma.ι_comp_desc]
  simp only [Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The recursively defined homotopy sends affine generators to affine chains. -/
theorem affineGenerator_subdivisionHomotopy_interpolation (n : ℕ)
    (v : Fin (n + 1) → StdSimplex ℝ I) :
    (singularSimplexGenerator (simplexAffineContinuous v) ≫
        subdivisionHomotopyDegree n (StdSimplex ℝ I)) ≫ affineInterpolationDegree I (n + 1) =
      singularSimplexGenerator (simplexAffineContinuous v) ≫
        subdivisionHomotopyDegree n (StdSimplex ℝ I) := by
  cases n with
  | zero => simp [subdivisionHomotopyDegree]
  | succ n =>
    rw [singularSimplexGenerator_subdivisionHomotopy_succ]
    simp only [canonicalSubdivisionHomotopyPrimitive, canonicalSimplexPostcompose,
      canonicalSimplexProjection, simplexAffineContinuous_comp, simplexAffineContinuous_single]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ canonicalSubdivisionHomotopyResidual.{u} n ≫ f)
      (affineConeDegree_postcompose_interpolation
        (StdSimplex.single (ULift.up (0 : Fin (n + 2)))) (n + 1)
        (fun i : ULift.{u} (Fin (n + 2)) ↦ v i.down))

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the recursively defined homotopy under continuous maps. -/
theorem subdivisionHomotopyDegree_postcompose {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    subdivisionHomotopyDegree n X ≫ (singularChainPostcompose f).f (n + 1) =
      (singularChainPostcompose f).f n ≫ subdivisionHomotopyDegree n Y := by
  cases n with
  | zero => simp [subdivisionHomotopyDegree]
  | succ n =>
    apply (TopCat.toSSet.obj (TopCat.of X)).chainComplex_hom_ext
      (R := ModuleCat.of ℝ (ULift.{u} ℝ))
    intro t
    let s := TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n + 1⦌) t
    have ht : singularSimplexGenerator s =
        (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex t := by
      simp [s, singularSimplexGenerator]
    rw [← ht, ← Category.assoc, singularSimplexGenerator_subdivisionHomotopy_succ,
      ← Category.assoc, singularSimplexGenerator_postcompose,
      singularSimplexGenerator_subdivisionHomotopy_succ, Category.assoc]
    have hm := congrArg (fun h ↦ h.f (n + 2))
      (singularChainPostcompose_comp (canonicalSimplexPostcompose s) f)
    rw [HomologicalComplex.comp_f] at hm
    rw [hm]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical recursive residual is an affine chain, with no contractibility premise. -/
theorem canonicalSubdivisionHomotopyResidual_interpolation (n : ℕ) :
    canonicalSubdivisionHomotopyResidual.{u} n ≫
        affineInterpolationDegree (ULift.{u} (Fin (n + 2))) (n + 1) =
      canonicalSubdivisionHomotopyResidual.{u} n := by
  unfold canonicalSubdivisionHomotopyResidual
  dsimp only
  simp only [Preadditive.sub_comp, canonicalSimplexInclusion,
    affineGenerator_subdivision_interpolation, affineGenerator_comp_affineInterpolation]
  congr 1
  rw [singularSimplexGenerator_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  unfold singularSimplexFace standardSimplexFace
  rw [simplexAffineContinuous_comp_vertexMap,
    affineGenerator_subdivisionHomotopy_interpolation]

def subdivisionHomotopyLowerTerm (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (singularChains X).X n ⟶ (singularChains X).X n := match n with
  | 0 => 0
  | n + 1 => (singularChains X).d (n + 1) n ≫ subdivisionHomotopyDegree n X

theorem subdivisionHomotopyLowerTerm_boundary (X : Type u) [TopologicalSpace X] (n : ℕ) :
    (singularChains X).d (n + 1) n ≫ subdivisionHomotopyLowerTerm n X = 0 := by
  cases n with
  | zero => simp [subdivisionHomotopyLowerTerm]
  | succ n =>
    simp only [subdivisionHomotopyLowerTerm, ← Category.assoc,
      HomologicalComplex.d_comp_d, Limits.zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The residual is a cycle once the actual lower degree homotopy law has been proved. -/
theorem canonicalSubdivisionHomotopyResidual_cycle (n : ℕ)
    (hprev :
      subdivisionHomotopyDegree n (canonicalSingularSimplex.{u} (n + 1)) ≫
          (singularChains (canonicalSingularSimplex.{u} (n + 1))).d (n + 1) n +
        subdivisionHomotopyLowerTerm n (canonicalSingularSimplex.{u} (n + 1)) =
        barycentricSubdivisionDegree (canonicalSingularSimplex.{u} (n + 1)) n - 𝟙 _) :
    canonicalSubdivisionHomotopyResidual.{u} n ≫
      (singularChains (canonicalSingularSimplex.{u} (n + 1))).d (n + 1) n = 0 := by
  let U := canonicalSingularSimplex.{u} (n + 1)
  let q := singularSimplexGenerator (canonicalSimplexInclusion.{u} (n + 1))
  have hz : (q ≫ (singularChains U).d (n + 1) n) ≫ subdivisionHomotopyLowerTerm n U = 0 := by
    rw [Category.assoc, subdivisionHomotopyLowerTerm_boundary, Limits.comp_zero]
  have hb := congrArg (fun f ↦ (q ≫ (singularChains U).d (n + 1) n) ≫ f) hprev
  simp only [Preadditive.comp_add, Preadditive.comp_sub, ← Category.assoc] at hb
  change ((q ≫ (singularChains U).d (n + 1) n) ≫ subdivisionHomotopyDegree n U) ≫
        (singularChains U).d (n + 1) n +
      (q ≫ (singularChains U).d (n + 1) n) ≫ subdivisionHomotopyLowerTerm n U =
      (q ≫ (singularChains U).d (n + 1) n) ≫ barycentricSubdivisionDegree U n -
        (q ≫ (singularChains U).d (n + 1) n) ≫ 𝟙 ((singularChains U).X n) at hb
  rw [hz, add_zero, Category.comp_id] at hb
  change (q ≫ barycentricSubdivisionDegree U (n + 1) - q -
      (q ≫ (singularChains U).d (n + 1) n) ≫ subdivisionHomotopyDegree n U) ≫
        (singularChains U).d (n + 1) n = 0
  rw [Preadditive.sub_comp, Preadditive.sub_comp, Category.assoc,
    barycentricSubdivisionDegree_comm, ← Category.assoc, hb, sub_self]

set_option backward.isDefEq.respectTransparency false in
theorem canonicalSubdivisionHomotopyResidual_postcompose {X : Type u}
    [TopologicalSpace X] {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 2)), X)) :
    canonicalSubdivisionHomotopyResidual.{u} n ≫
        (singularChainPostcompose (canonicalSimplexPostcompose s)).f (n + 1) =
      singularSimplexGenerator s ≫ barycentricSubdivisionDegree X (n + 1) -
        singularSimplexGenerator s -
          (singularSimplexGenerator s ≫ (singularChains X).d (n + 1) n) ≫
            subdivisionHomotopyDegree n X := by
  let U := canonicalSingularSimplex.{u} (n + 1)
  let q := singularSimplexGenerator (canonicalSimplexInclusion.{u} (n + 1))
  let F := singularChainPostcompose (canonicalSimplexPostcompose s)
  have hq : q ≫ F.f (n + 1) = singularSimplexGenerator s := by
    rw [singularSimplexGenerator_postcompose, canonicalSimplexPostcompose_comp_inclusion]
  have hsd : (q ≫ barycentricSubdivisionDegree U (n + 1)) ≫ F.f (n + 1) =
      singularSimplexGenerator s ≫ barycentricSubdivisionDegree X (n + 1) := by
    rw [Category.assoc, barycentricSubdivisionDegree_postcompose, ← Category.assoc, hq]
  have hdm : (q ≫ (singularChains U).d (n + 1) n) ≫ F.f n =
      singularSimplexGenerator s ≫ (singularChains X).d (n + 1) n := by
    rw [Category.assoc, ← F.comm (n + 1) n, ← Category.assoc, hq]
  have hh : ((q ≫ (singularChains U).d (n + 1) n) ≫ subdivisionHomotopyDegree n U) ≫
      F.f (n + 1) =
      (singularSimplexGenerator s ≫ (singularChains X).d (n + 1) n) ≫
        subdivisionHomotopyDegree n X := by
    rw [Category.assoc, subdivisionHomotopyDegree_postcompose, ← Category.assoc, hdm]
  change (q ≫ barycentricSubdivisionDegree U (n + 1) - q -
      (q ≫ (singularChains U).d (n + 1) n) ≫ subdivisionHomotopyDegree n U) ≫ F.f (n + 1) = _
  rw [Preadditive.sub_comp, Preadditive.sub_comp, hsd, hq, hh]

theorem canonicalSubdivisionHomotopyPrimitive_boundary (n : ℕ)
    (hprev :
      subdivisionHomotopyDegree n (canonicalSingularSimplex.{u} (n + 1)) ≫
          (singularChains (canonicalSingularSimplex.{u} (n + 1))).d (n + 1) n +
        subdivisionHomotopyLowerTerm n (canonicalSingularSimplex.{u} (n + 1)) =
        barycentricSubdivisionDegree (canonicalSingularSimplex.{u} (n + 1)) n - 𝟙 _) :
    canonicalSubdivisionHomotopyPrimitive.{u} n ≫
        (singularChains (canonicalSingularSimplex.{u} (n + 1))).d (n + 2) (n + 1) =
      canonicalSubdivisionHomotopyResidual.{u} n :=
  affineCycle_cone_primitive (StdSimplex.single (ULift.up (0 : Fin (n + 2)))) n
    (canonicalSubdivisionHomotopyResidual.{u} n) (canonicalSubdivisionHomotopyResidual_cycle n hprev)
    (canonicalSubdivisionHomotopyResidual_interpolation n)

set_option backward.isDefEq.respectTransparency false in
/-- The residual-cone recursion proves the actual subdivision-minus-identity
chain homotopy law in every degree, with zero lower term in degree zero. -/
theorem subdivisionHomotopyDegree_boundary (n : ℕ) (X : Type u) [TopologicalSpace X] :
    subdivisionHomotopyDegree n X ≫ (singularChains X).d (n + 1) n +
      subdivisionHomotopyLowerTerm n X = barycentricSubdivisionDegree X n - 𝟙 _ := by
  induction n generalizing X with
  | zero => simp [subdivisionHomotopyDegree, subdivisionHomotopyLowerTerm,
      barycentricSubdivisionDegree_zero]
  | succ n ih =>
    have hp := canonicalSubdivisionHomotopyPrimitive_boundary.{u} n
      (ih (canonicalSingularSimplex.{u} (n + 1)))
    have hg (s : C(StdSimplex ℝ (Fin (n + 2)), X)) :
        (singularSimplexGenerator s ≫ subdivisionHomotopyDegree (n + 1) X) ≫
            (singularChains X).d (n + 2) (n + 1) +
          (singularSimplexGenerator s ≫ (singularChains X).d (n + 1) n) ≫
            subdivisionHomotopyDegree n X =
          singularSimplexGenerator s ≫ (barycentricSubdivisionDegree X (n + 1) - 𝟙 _) := by
      rw [singularSimplexGenerator_subdivisionHomotopy_succ, Category.assoc,
        (singularChainPostcompose (canonicalSimplexPostcompose s)).comm (n + 2) (n + 1),
        ← Category.assoc, hp, canonicalSubdivisionHomotopyResidual_postcompose,
        sub_add_cancel, Preadditive.comp_sub, Category.comp_id]
    apply (TopCat.toSSet.obj (TopCat.of X)).chainComplex_hom_ext
      (R := ModuleCat.of ℝ (ULift.{u} ℝ))
    intro t
    simpa only [singularSimplexGenerator, Equiv.symm_apply_apply, Category.assoc,
      Preadditive.comp_add, subdivisionHomotopyLowerTerm] using
      hg (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n + 1⦌) t)

/-- Two-index components of the actual degree-raising subdivision homotopy. -/
def subdivisionHomotopyHom (X : Type u) [TopologicalSpace X] (i j : ℕ) :
    (singularChains X).X i ⟶ (singularChains X).X j :=
  if h : i + 1 = j then
    subdivisionHomotopyDegree i X ≫ eqToHom (congrArg (singularChains X).X h)
  else 0

@[simp]
theorem subdivisionHomotopyHom_succ (X : Type u) [TopologicalSpace X] (i : ℕ) :
    subdivisionHomotopyHom X i (i + 1) = subdivisionHomotopyDegree i X := by
  simp [subdivisionHomotopyHom]

/-- Geometric subdivision is homotopic to identity on the actual singular chains.
Its components are the explicitly constructed, natural residual-cone operators. -/
def barycentricSubdivisionHomotopy (X : Type u) [TopologicalSpace X] :
    Homotopy (barycentricSubdivision X) (𝟙 (singularChains X)) where
  hom := subdivisionHomotopyHom X
  zero i j h := by
    have h' : ¬ i + 1 = j := by simpa only [ComplexShape.down_Rel] using h
    simp [subdivisionHomotopyHom, h']
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [subdivisionHomotopyHom_succ, zero_add,
        HomologicalComplex.id_f, barycentricSubdivision_f]
      have h := subdivisionHomotopyDegree_boundary 0 X
      simp only [subdivisionHomotopyLowerTerm, add_zero] at h
      exact ((eq_sub_iff_add_eq).mp h).symm
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [subdivisionHomotopyHom_succ,
        HomologicalComplex.id_f, barycentricSubdivision_f]
      have h := subdivisionHomotopyDegree_boundary (n + 1) X
      simp only [subdivisionHomotopyLowerTerm] at h
      calc
        _ = (subdivisionHomotopyDegree (n + 1) X ≫ (singularChains X).d (n + 2) (n + 1) +
            (singularChains X).d (n + 1) n ≫ subdivisionHomotopyDegree n X) + 𝟙 _ :=
          ((eq_sub_iff_add_eq).mp h).symm
        _ = _ := congrArg (fun f ↦ f + 𝟙 _) (add_comm
          (subdivisionHomotopyDegree (n + 1) X ≫ (singularChains X).d (n + 2) (n + 1))
          ((singularChains X).d (n + 1) n ≫ subdivisionHomotopyDegree n X))

theorem barycentricSubdivision_homologyMap (X : Type u) [TopologicalSpace X] (n : ℕ) :
    HomologicalComplex.homologyMap (barycentricSubdivision X) n = 𝟙 _ := by
  rw [(barycentricSubdivisionHomotopy X).homologyMap_eq, HomologicalComplex.homologyMap_id]

end GaussBonnetChern
