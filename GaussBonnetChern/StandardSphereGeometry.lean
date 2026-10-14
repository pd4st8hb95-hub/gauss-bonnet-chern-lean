import GaussBonnetChern.SphereChartIntegralAtlas
import GaussBonnetChern.SphereHomology
import GaussBonnetChern.MainTheorem
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Bounded

/-! # The standard induced geometry of actual even-dimensional unit spheres

The inner product is the pullback of the ambient Euclidean inner product by
the actual derivative of the inclusion. Neither a metric nor a curvature
identity is supplied as a hypothesis. The finite atlas uses the previously
constructed actual outward positive sphere atlas. The final GBC regression
uses the project's main theorem and actual singular homology; it is not an
independent calculation of the constant-curvature Pfaffian or sphere area.

Writer status: SOURCE_READY, pending root elaboration and dependency audit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle Module Metric MeasureTheory Filter Bornology
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.StandardSphereGeometry

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n + 1))
abbrev Sphere (n : ℕ) := Metric.sphere (0 : Ambient n) 1

instance ambientDimension (n : ℕ) : Fact (finrank ℝ (Ambient n) = 2 * n + 1) :=
  ⟨by simp [Ambient]⟩

instance compactSphere (n : ℕ) : CompactSpace (Sphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient n) 1)

def inclusion (n : ℕ) : Sphere n → Ambient n := Subtype.val

theorem inclusion_contMDiff (n : ℕ) :
    ContMDiff (model n) 𝓘(ℝ, Ambient n) ω (inclusion n) :=
  contMDiff_coe_sphere

/-- The actual sphere inclusion derivative, with its target identified with
the ambient vector space rather than an auxiliary tangent-space norm. -/
def inclusionDerivative (n : ℕ) (x : Sphere n) :
    TangentSpace (model n) x →L[ℝ] Ambient n :=
  mvfderiv (model n) (inclusion n) x

theorem inclusionDerivative_injective (n : ℕ) (x : Sphere n) :
    Function.Injective (inclusionDerivative n x) :=
  injective_mvfderiv_subtypeVal_sphere x

theorem inclusionDerivative_range (n : ℕ) (x : Sphere n) :
    (inclusionDerivative n x).range = (ℝ ∙ (x : Ambient n))ᗮ :=
  range_mvfderiv_subtypeVal x

private def ambientInner (n : ℕ) : Ambient n →L[ℝ] Ambient n →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (innerₗ (Ambient n)) 1 (fun v w ↦ by
    simpa only [innerₗ_apply_apply, one_mul] using norm_inner_le_norm v w)

/-- The actual bilinear form induced by the actual ambient inclusion. -/
def inducedInner (n : ℕ) (x : Sphere n) :
    TangentSpace (model n) x →L[ℝ] TangentSpace (model n) x →L[ℝ] ℝ :=
  ((inclusionDerivative n x).precomp ℝ).comp
    ((ambientInner n).comp (inclusionDerivative n x))

theorem inducedInner_apply (n : ℕ) (x : Sphere n)
    (v w : TangentSpace (model n) x) :
    inducedInner n x v w =
      inner ℝ (inclusionDerivative n x v) (inclusionDerivative n x w) := rfl

theorem inducedInner_symm (n : ℕ) (x : Sphere n)
    (v w : TangentSpace (model n) x) :
    inducedInner n x v w = inducedInner n x w v := by
  rw [inducedInner_apply, inducedInner_apply]
  exact real_inner_comm _ _

theorem inducedInner_pos (n : ℕ) (x : Sphere n)
    (v : TangentSpace (model n) x) (hv : v ≠ 0) :
    0 < inducedInner n x v v := by
  rw [inducedInner_apply]
  apply real_inner_self_pos.mpr
  intro h
  apply hv
  apply inclusionDerivative_injective n x
  simpa using h

/-- The subunit ellipsoid is bounded in the existing tangent topology. The
proof transports an actual bounded ball through the continuous inverse onto
the inclusion derivative's finite-dimensional range, without introducing a
different norm or metric on the sphere. -/
theorem inducedInner_isVonNBounded (n : ℕ) (x : Sphere n) :
    IsVonNBounded ℝ {v : TangentSpace (model n) x | inducedInner n x v v < 1} := by
  let D := inclusionDerivative n x
  let e : TangentSpace (model n) x ≃L[ℝ] LinearMap.range D.toLinearMap :=
    (LinearEquiv.ofInjective D.toLinearMap (inclusionDerivative_injective n x)).toContinuousLinearEquiv
  have hball : IsVonNBounded ℝ
      (Metric.closedBall (0 : LinearMap.range D.toLinearMap) 1) :=
    (isCompact_closedBall _ _).isVonNBounded ℝ
  apply (hball.image e.symm.toContinuousLinearMap).subset
  intro v hv
  refine ⟨e v, ?_, e.symm_apply_apply v⟩
  change inducedInner n x v v < 1 at hv
  have hv' : ‖D v‖ ^ 2 < 1 := by
    simpa only [inducedInner_apply, real_inner_self_eq_norm_sq, D] using hv
  have hnorm : ‖D v‖ ≤ 1 := by nlinarith [norm_nonneg (D v)]
  simp only [Metric.mem_closedBall, dist_zero_right]
  change ‖((e v : LinearMap.range D.toLinearMap) : Ambient n)‖ ≤ 1
  have heval : ((e v : LinearMap.range D.toLinearMap) : Ambient n) = D v := by
    simp [e, LinearEquiv.ofInjective_apply]
  rw [heval]
  exact hnorm

private def modelPullbackInner (n : ℕ) (A : Model n →L[ℝ] Ambient n) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  (A.precomp ℝ).comp ((ambientInner n).comp A)

/-- Smoothness of the actual induced bilinear form as a section of the
bilinear Hom bundle. Only the actual analytic sphere inclusion is used. -/
theorem inducedInner_contMDiff (n : ℕ) :
    ContMDiff (model n)
      ((model n).prod 𝓘(ℝ, Model n →L[ℝ] Model n →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (Model n →L[ℝ] Model n →L[ℝ] ℝ) x (inducedInner n x)) := by
  intro p
  rw [contMDiffAt_section]
  let e := trivializationAt (Model n) (TangentSpace (model n) : Sphere n → Type _) p
  let A (x : Sphere n) : Model n →L[ℝ] Ambient n :=
    (inclusionDerivative n x).comp (e.symmL ℝ x)
  have hA : ContMDiffAt (model n) 𝓘(ℝ, Model n →L[ℝ] Ambient n) ∞ A p := by
    have h := (inclusion_contMDiff n p).mfderiv_const (m := ∞) (by simp)
    convert h using 1
    ext x v
    simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, A, e,
      inclusionDerivative, mvfderiv, NormedSpace.fromTangentSpace,
      tangentSpaceCastModel, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply] <;> rfl
  have hP : ContMDiffAt (model n)
      𝓘(ℝ, (Ambient n →L[ℝ] ℝ) →L[ℝ] Model n →L[ℝ] ℝ) ∞
      (fun x ↦ (A x).precomp ℝ) p := hA.clm_precomp
  have hI : ContMDiffAt (model n)
      𝓘(ℝ, Model n →L[ℝ] Ambient n →L[ℝ] ℝ) ∞
      (fun x ↦ (ambientInner n).comp (A x)) p :=
    (contMDiffAt_const (c := ambientInner n)).clm_comp hA
  have hQ : ContMDiffAt (model n)
      𝓘(ℝ, Model n →L[ℝ] Model n →L[ℝ] ℝ) ∞
      (fun x ↦ modelPullbackInner n (A x)) p := hP.clm_comp hI
  apply hQ.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt (Model n)
    (TangentSpace (model n) : Sphere n → Type _) p)] with x hx
  ext v w
  simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.linearMapAt_trivialization, modelPullbackInner, inducedInner, ambientInner,
    A, e, Trivialization.symmL_apply e hx]

/-- The standard round induced smooth metric. No metric hypothesis is present. -/
def inducedMetric (n : ℕ) : SmoothMetric n (Sphere n) where
  inner := inducedInner n
  symm := inducedInner_symm n
  pos := inducedInner_pos n
  isVonNBounded := inducedInner_isVonNBounded n
  contMDiff := inducedInner_contMDiff n

/-- Exact geometric identity for the constructed metric's inner product. -/
theorem inducedMetric_inner (n : ℕ) (x : Sphere n)
    (v w : TangentSpace (model n) x) :
    (inducedMetric n).inner x v w =
      inner ℝ (mvfderiv (model n) (inclusion n) x v)
        (mvfderiv (model n) (inclusion n) x w) := rfl

def outwardBasis (n : ℕ) : OrthonormalBasis (Fin (2 * n + 1)) ℝ (Ambient n) :=
  EuclideanSpace.basisFun _ _

/-- Actual outward-oriented finite atlas, transported along the definitional
identity of the sphere's Euclidean model and the original `Model n`. -/
def orientedAtlas (n : ℕ) (hn : 1 ≤ n) : FiniteOrientedAtlas n (Sphere n) := by
  let a := sphereOrientedAtlas (outwardBasis n) (by omega : 0 < 2 * n)
  exact {
    card := a.card
    chart := a.chart
    smooth := a.smooth
    covers := a.covers
    positive_transition := a.positive_transition (outwardBasis n) }

theorem orientedAtlas_exists_partition (n : ℕ) (hn : 1 ≤ n) :
    ∃ ρ : SmoothPartitionOfUnity (Fin (orientedAtlas n hn).card)
      (model n) (Sphere n) Set.univ,
      ρ.IsSubordinate (fun i ↦ ((orientedAtlas n hn).chart i).source) := by
  let a := sphereOrientedAtlas (outwardBasis n) (by omega : 0 < 2 * n)
  exact a.exists_partition (outwardBasis n)

/-- The actual standard round sphere, with the constructed metric and atlas,
instantiates the unchanged all-dimensional GBC theorem. -/
theorem standardSphere_statement (n : ℕ) (hn : 1 ≤ n) :
    StatementFor n (Sphere n) (orientedAtlas n hn) (inducedMetric n) :=
  gaussBonnetChern n hn (Sphere n) (orientedAtlas n hn) (inducedMetric n)

/-- The curvature integral of the actual induced sphere metric is two,
using actual singular homology. This regression depends on GBC; it does not
claim an independent constant-curvature or sphere-area computation. -/
theorem standardSphere_curvatureIntegral (n : ℕ) (hn : 1 ≤ n) :
    letI : RiemannianBundle (TangentSpace (model n) : Sphere n → Type _) :=
      ⟨(inducedMetric n).toRiemannianMetric⟩
    ∀ ρ : SmoothPartitionOfUnity (Fin (orientedAtlas n hn).card)
        (model n) (Sphere n) Set.univ,
      ρ.IsSubordinate (fun i ↦ ((orientedAtlas n hn).chart i).source) →
        curvatureIntegral n (Sphere n) (orientedAtlas n hn) ρ = 2 := by
  letI : RiemannianBundle (TangentSpace (model n) : Sphere n → Type _) :=
    ⟨(inducedMetric n).toRiemannianMetric⟩
  intro ρ hρ
  have h := standardSphere_statement n hn ρ hρ
  have hEuler : topologicalEulerCharacteristic (Sphere n) = 2 := by
    rw [unitSphere_topologicalEulerCharacteristic (E := Ambient n) (2 * n)
      (by simp [Ambient])]
    simp [pow_mul]
  simpa only [hEuler, Int.cast_ofNat] using h

end GaussBonnetChern.StandardSphereGeometry
