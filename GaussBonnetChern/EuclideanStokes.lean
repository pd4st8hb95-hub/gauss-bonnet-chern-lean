import GaussBonnetChern.BoundaryForms
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace GaussBonnetChern.CoordinateStokes
variable {n k : ℕ}

def toEuclidean (d : ℕ) : CoordinateSpace d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).symm

def euclideanCoordinateForm
    (α : EuclideanSpace ℝ (Fin (n + 1)) →
      ContinuousAlternatingMap ℝ (EuclideanSpace ℝ (Fin (n + 1))) ℝ (Fin k))
    (x : CoordinateSpace (n + 1)) :
    ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin k) :=
  (α (toEuclidean (n + 1) x)).compContinuousLinearMap (toEuclidean (n + 1)).toContinuousLinearMap

theorem contDiff_euclideanCoordinateForm
    (α : EuclideanSpace ℝ (Fin (n + 1)) →
      ContinuousAlternatingMap ℝ (EuclideanSpace ℝ (Fin (n + 1))) ℝ (Fin k))
    (hα : ContDiff ℝ ∞ α) : ContDiff ℝ ∞ (euclideanCoordinateForm α) :=
  (ContinuousAlternatingMap.compContinuousLinearMapCLM
    (toEuclidean (n + 1)).toContinuousLinearMap).contDiff.comp
      (hα.comp (toEuclidean (n + 1)).contDiff)

theorem hasCompactSupport_euclideanCoordinateForm
    (α : EuclideanSpace ℝ (Fin (n + 1)) →
      ContinuousAlternatingMap ℝ (EuclideanSpace ℝ (Fin (n + 1))) ℝ (Fin k))
    (hα : HasCompactSupport α) : HasCompactSupport (euclideanCoordinateForm α) := by
  exact (hα.comp_homeomorph (toEuclidean (n + 1)).toHomeomorph).comp_left
    (g := ContinuousAlternatingMap.compContinuousLinearMapCLM
      (toEuclidean (n + 1)).toContinuousLinearMap) (map_zero _)

theorem toEuclidean_coordinateBasis (d : ℕ) (j : Fin d) :
    toEuclidean d (coordinateBasis d j) = EuclideanSpace.basisFun (Fin d) ℝ j := by
  simp [toEuclidean, coordinateBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.single]

theorem extDeriv_euclideanCoordinateForm
    (α : EuclideanSpace ℝ (Fin (n + 1)) →
      ContinuousAlternatingMap ℝ (EuclideanSpace ℝ (Fin (n + 1))) ℝ (Fin k))
    (hα : ContDiff ℝ ∞ α) (x : CoordinateSpace (n + 1)) :
    extDeriv (euclideanCoordinateForm α) x = euclideanCoordinateForm (extDeriv α) x := by
  unfold euclideanCoordinateForm
  have h := extDeriv_pullback (r := ∞)
    ((hα.contDiffAt).differentiableAt (by simp))
    ((toEuclidean (n + 1)).contDiff.contDiffAt (x := x)) (by simp)
  simpa only [(toEuclidean (n + 1)).hasFDerivAt.fderiv] using h

/-- Half-space Stokes transported to the project's Euclidean model. The
coordinate equivalence preserves the actual normalized Lebesgue measures. -/
theorem stokes_euclidean_halfspace
    (α : EuclideanSpace ℝ (Fin (n + 1)) →
      ContinuousAlternatingMap ℝ (EuclideanSpace ℝ (Fin (n + 1))) ℝ (Fin n))
    (hα : ContDiff ℝ ∞ α) (hcompact : HasCompactSupport α) (i : Fin (n + 1)) :
    (∫ x in {x : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ x i},
      extDeriv α x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)) =
      -(∫ y : CoordinateSpace n, (-1 : ℝ)^i.val *
        α (toEuclidean (n + 1) (i.insertNth 0 y))
          (fun j ↦ EuclideanSpace.basisFun (Fin (n + 1)) ℝ (i.succAbove j))) := by
  have hc := stokes_halfspace (euclideanCoordinateForm α)
    (contDiff_euclideanCoordinateForm α hα) (hasCompactSupport_euclideanCoordinateForm α hcompact) i
  have hev (x : CoordinateSpace (n + 1)) :
      extDeriv (euclideanCoordinateForm α) x (coordinateBasis (n + 1)) =
        extDeriv α (toEuclidean (n + 1) x) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ) := by
    rw [extDeriv_euclideanCoordinateForm α hα]
    change extDeriv α (toEuclidean (n + 1) x)
      (fun j ↦ toEuclidean (n + 1) (coordinateBasis (n + 1) j)) = _
    simp only [toEuclidean_coordinateBasis]
  simp_rw [hev] at hc
  have hvol := (PiLp.volume_preserving_toLp (Fin (n + 1))).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).measurableEmbedding
    (fun x ↦ extDeriv α x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ))
    {x : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ x i}
  change (∫ x in {x : CoordinateSpace (n + 1) | 0 ≤ x i},
    extDeriv α (toEuclidean (n + 1) x) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)) = _ at hvol
  rw [← hvol, hc]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  change (-1 : ℝ)^i.val * α (toEuclidean (n + 1) (i.insertNth 0 y))
    (fun j ↦ toEuclidean (n + 1) (coordinateBasis (n + 1) (i.succAbove j))) = _
  simp only [toEuclidean_coordinateBasis]

end GaussBonnetChern.CoordinateStokes
