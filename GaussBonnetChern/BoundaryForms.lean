import GaussBonnetChern.CoordinateStokes
import Mathlib.LinearAlgebra.Determinant

/-! # Actual coordinate face pullbacks and boundary orientation

The map of a coordinate face is affine, its derivative is the coordinate
insertion linear map, and the pullback below uses exactly that derivative.
The determinant calculations prove the outward-normal-first orientation
sign on both sides of every face in arbitrary dimension.
-/

noncomputable section
open scoped ContDiff Manifold BigOperators

namespace GaussBonnetChern.CoordinateStokes

variable {n k : ℕ}

def faceTangentMap (i : Fin (n + 1)) :
    CoordinateSpace n →L[ℝ] CoordinateSpace (n + 1) :=
  ContinuousLinearMap.pi (i.insertNth 0 (fun j ↦ ContinuousLinearMap.proj j))

@[simp] theorem faceTangentMap_apply (i : Fin (n + 1)) (y : CoordinateSpace n) :
    faceTangentMap i y = i.insertNth 0 y := by
  funext j
  refine Fin.succAboveCases i ?_ (fun l ↦ ?_) j <;> simp [faceTangentMap]

theorem faceTangentMap_basis (i : Fin (n + 1)) (j : Fin n) :
    faceTangentMap i (coordinateBasis n j) = coordinateBasis (n + 1) (i.succAbove j) := by
  rw [faceTangentMap_apply]
  funext l
  refine Fin.succAboveCases i ?_ (fun l ↦ ?_) l
  · simp [coordinateBasis, Fin.succAbove_ne]
  · simp [coordinateBasis, Pi.single_apply, Fin.succAbove_right_injective.eq_iff]

theorem faceInclusion_eq (i : Fin (n + 1)) (t : ℝ) :
    (fun z : CoordinateSpace n ↦ Fin.insertNth (α := fun _ ↦ ℝ) i t z) =
      fun z : CoordinateSpace n ↦ faceTangentMap i z + t • coordinateBasis (n + 1) i := by
  funext z l
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) l <;>
    simp [coordinateBasis, Pi.single_apply, Fin.succAbove_ne]

theorem contDiff_faceInclusion (i : Fin (n + 1)) (t : ℝ) :
    ContDiff ℝ ∞ (fun z : CoordinateSpace n ↦ Fin.insertNth (α := fun _ ↦ ℝ) i t z) := by
  rw [faceInclusion_eq]
  exact (faceTangentMap i).contDiff.add contDiff_const

theorem hasFDerivAt_faceInclusion (i : Fin (n + 1)) (t : ℝ) (y : CoordinateSpace n) :
    HasFDerivAt (fun z : CoordinateSpace n ↦ Fin.insertNth (α := fun _ ↦ ℝ) i t z) (faceTangentMap i) y := by
  rw [faceInclusion_eq]
  simpa using (faceTangentMap i).hasFDerivAt.add_const
    (t • coordinateBasis (n + 1) i)

/-- Pullback along the affine inclusion of a coordinate face. -/
def facePullback
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin k))
    (i : Fin (n + 1)) (t : ℝ) (y : CoordinateSpace n) :
    ContinuousAlternatingMap ℝ (CoordinateSpace n) ℝ (Fin k) :=
  (α (i.insertNth t y)).compContinuousLinearMap (faceTangentMap i)

theorem facePullback_eq_fderiv
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin k))
    (i : Fin (n + 1)) (t : ℝ) (y : CoordinateSpace n) :
    facePullback α i t y = (α (i.insertNth t y)).compContinuousLinearMap
      (fderiv ℝ (fun z : CoordinateSpace n ↦ Fin.insertNth (α := fun _ ↦ ℝ) i t z) y) := by
  rw [(hasFDerivAt_faceInclusion i t y).fderiv]
  rfl

theorem facePullback_coordinateBasis
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n))
    (i : Fin (n + 1)) (t : ℝ) (y : CoordinateSpace n) :
    facePullback α i t y (coordinateBasis n) = α (i.insertNth t y) (faceBasis i) := by
  change α (i.insertNth t y) (fun j ↦ faceTangentMap i (coordinateBasis n j)) = _
  simp only [faceTangentMap_basis]
  rfl

/-- Restriction to a face commutes with the actual exterior derivative. -/
theorem extDeriv_facePullback
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin k))
    (i : Fin (n + 1)) (t : ℝ) (y : CoordinateSpace n)
    (hα : DifferentiableAt ℝ α (i.insertNth t y)) :
    extDeriv (facePullback α i t) y = facePullback (extDeriv α) i t y := by
  have heq : facePullback α i t = fun z : CoordinateSpace n ↦
      (α (i.insertNth t z)).compContinuousLinearMap
        (fderiv ℝ (fun w : CoordinateSpace n ↦ Fin.insertNth (α := fun _ ↦ ℝ) i t w) z) :=
    funext (facePullback_eq_fderiv α i t)
  rw [heq, extDeriv_pullback hα (contDiff_faceInclusion i t).contDiffAt (by simp)]
  rw [(hasFDerivAt_faceInclusion i t y).fderiv]
  rfl

/-- The oriented volume alternating map for the ordered coordinate basis. -/
def coordinateVolume (d : ℕ) :
    AlternatingMap ℝ (CoordinateSpace d) ℝ (Fin d) :=
  (Pi.basisFun ℝ (Fin d)).det

@[simp] theorem coordinateVolume_basis (d : ℕ) :
    coordinateVolume d (coordinateBasis d) = 1 := by
  have hb : (Pi.basisFun ℝ (Fin d) : Fin d → CoordinateSpace d) = coordinateBasis d := by
    funext i
    simp only [Pi.basisFun_apply, coordinateBasis]
  rw [coordinateVolume, ← hb]
  exact (Pi.basisFun ℝ (Fin d)).det_self

/-- Inserting the upper outward normal first contributes `(-1)^i`. -/
theorem coordinateVolume_upper_normal (i : Fin (n + 1)) :
    coordinateVolume (n + 1)
      (Fin.cons (coordinateBasis (n + 1) i) (faceBasis i)) = (-1 : ℝ)^i.val := by
  have h := (coordinateVolume (n + 1)).neg_one_pow_smul_map_insertNth i
    (coordinateBasis (n + 1) i) (faceBasis i)
  rw [faceBasis, Fin.insertNth_removeNth, Function.update_eq_self, coordinateVolume_basis] at h
  simpa only [Matrix.vecCons, faceBasis, smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    mul_one] using h.symm

/-- Inserting the lower outward normal first contributes `-(-1)^i`. -/
theorem coordinateVolume_lower_normal (i : Fin (n + 1)) :
    coordinateVolume (n + 1)
      (Fin.cons (-coordinateBasis (n + 1) i) (faceBasis i)) = -((-1 : ℝ)^i.val) := by
  have h := (coordinateVolume (n + 1)).map_vecCons_smul (faceBasis i) (-1 : ℝ)
    (coordinateBasis (n + 1) i)
  simpa only [Matrix.vecCons, neg_one_smul, smul_eq_mul, neg_one_mul,
    coordinateVolume_upper_normal] using h

end GaussBonnetChern.CoordinateStokes
