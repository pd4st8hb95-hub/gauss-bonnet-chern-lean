import GaussBonnetChern.DifferentialForms
import GaussBonnetChern.ExteriorDerivativeNaturality
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The actual outward volume form of a unit sphere

The ambient orthonormal basis specifies orientation. The normal occupies the
first determinant slot. Every top form has a unique scalar coefficient relative
to this nonvanishing form. Integration of that coefficient uses the genuine
polar sphere measure; comparison with coordinate integration is separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module MeasureTheory Metric
open scoped Manifold BigOperators RealInnerProductSpace ContDiff Topology

namespace GaussBonnetChern

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (finrank ℝ E = d+1)]

/-- The ambient determinant as a continuous alternating map. -/
def sphereAmbientVolume (b : OrthonormalBasis (Fin (d+1)) ℝ E) :
    E [⋀^Fin (d+1)]→L[ℝ] ℝ :=
  b.toBasis.det.mkContinuous 1 (fun v ↦ by
    have h := b.toBasis.orientation.abs_volumeForm_apply_le v
    rw [b.toBasis.orientation.volumeForm_robust b rfl] at h
    simpa only [Real.norm_eq_abs, one_mul] using h)

@[simp] theorem sphereAmbientVolume_apply (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (v : Fin (d+1) → E) : sphereAmbientVolume b v = b.toBasis.det v := rfl

/-- The genuine outward-normal-first area form, on actual sphere tangent spaces. -/
def sphereVolumeForm (b : OrthonormalBasis (Fin (d+1)) ℝ E) :
    DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d :=
  fun u ↦ ((sphereAmbientVolume b).curryLeft (u:E)).compContinuousLinearMap
    (mvfderiv (𝓡 d) ((↑) : sphere (0:E) 1 → E) u)

@[simp] theorem sphereVolumeForm_apply (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (u : sphere (0:E) 1) (v : Fin d → TangentSpace (𝓡 d) u) :
    sphereVolumeForm b u v = b.toBasis.det
      (Fin.cons (u:E) (fun i ↦ mvfderiv (𝓡 d) ((↑) : sphere (0:E) 1 → E) u (v i))) := rfl

/-- The normal and the image of any tangent basis form an ambient basis. -/
theorem sphere_normal_tangent_linearIndependent (u : sphere (0:E) 1)
    (e : Basis (Fin d) ℝ (TangentSpace (𝓡 d) u)) :
    LinearIndependent ℝ (Fin.cons (u:E)
      (fun i ↦ mvfderiv (𝓡 d) ((↑) : sphere (0:E) 1 → E) u (e i))) := by
  let D := mvfderiv (𝓡 d) ((↑) : sphere (0:E) 1 → E) u
  apply linearIndependent_finCons.mpr
  constructor
  · exact e.linearIndependent.map' D.toLinearMap
      (LinearMap.ker_eq_bot.mpr (injective_mvfderiv_subtypeVal_sphere u))
  · have hs : Submodule.span ℝ (Set.range (fun i ↦ D (e i))) ≤ (ℝ ∙ (u:E))ᗮ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      rw [← range_mvfderiv_subtypeVal (n := d) u]
      exact ⟨e i,rfl⟩
    intro hu
    have hz := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hs hu)
    have hn : ‖(u:E)‖ = 1 := norm_eq_of_mem_sphere u
    simpa [real_inner_self_eq_norm_sq, hn] using hz

theorem sphereVolumeForm_basis_ne_zero (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (u : sphere (0:E) 1) (e : Basis (Fin d) ℝ (TangentSpace (𝓡 d) u)) :
    sphereVolumeForm b u e ≠ 0 := by
  rw [sphereVolumeForm_apply]
  have hi := sphere_normal_tangent_linearIndependent u e
  have hs := hi.span_eq_top_of_card_eq_finrank (by simpa using (Fact.out : finrank ℝ E = d+1).symm)
  exact ((b.toBasis.is_basis_iff_det).mp ⟨hi,hs⟩).ne_zero

theorem sphereVolumeForm_ne_zero (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (u : sphere (0:E) 1) : sphereVolumeForm b u ≠ 0 := by
  intro h
  have hn := sphereVolumeForm_basis_ne_zero b u (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  exact hn (by rw [h]; rfl)

/-- The coefficient is defined using a tangent basis, and proved independent
of that choice by its exact scalar-multiple characterization below. -/
def sphereFormCoefficient (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) (u : sphere (0:E) 1) : ℝ :=
  α u (EuclideanSpace.basisFun (Fin d) ℝ) /
    sphereVolumeForm b u (EuclideanSpace.basisFun (Fin d) ℝ)

theorem sphereForm_eq_coefficient_smul (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) (u : sphere (0:E) 1) :
    α u = sphereFormCoefficient b α u • sphereVolumeForm b u := by
  let e := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  have hn := sphereVolumeForm_basis_ne_zero b u e
  ext v
  have ha := congrArg (fun A ↦ A v) ((α u).toAlternatingMap.eq_smul_basis_det e)
  have hw := congrArg (fun A ↦ A v) ((sphereVolumeForm b u).toAlternatingMap.eq_smul_basis_det e)
  change α u v = α u e * e.det v at ha
  change sphereVolumeForm b u v = sphereVolumeForm b u e * e.det v at hw
  change α u v = (α u e / sphereVolumeForm b u e) * sphereVolumeForm b u v
  rw [ha,hw]
  calc
    α u e * e.det v = ((α u e / sphereVolumeForm b u e) * sphereVolumeForm b u e) * e.det v :=
      congrArg (fun r : ℝ ↦ r * e.det v) (div_mul_cancel₀ (α u e) hn).symm
    _ = _ := mul_assoc _ _ _

theorem sphereFormCoefficient_eq_iff (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) (u : sphere (0:E) 1) (c : ℝ) :
    sphereFormCoefficient b α u = c ↔ α u = c • sphereVolumeForm b u := by
  constructor
  · intro h
    rw [← h]
    exact sphereForm_eq_coefficient_smul b α u
  · intro h
    unfold sphereFormCoefficient
    rw [h, ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_div_cancel_right₀]
    exact sphereVolumeForm_basis_ne_zero b u (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

/-- The ratio agrees with evaluation on every nondegenerate tangent tuple. -/
theorem sphereFormCoefficient_eq_ratio (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) (u : sphere (0:E) 1)
    (v : Fin d → TangentSpace (𝓡 d) u) (hv : sphereVolumeForm b u v ≠ 0) :
    sphereFormCoefficient b α u = α u v / sphereVolumeForm b u v := by
  have h := congrArg (fun A ↦ A v) (sphereForm_eq_coefficient_smul b α u)
  change α u v = sphereFormCoefficient b α u * sphereVolumeForm b u v at h
  exact (eq_div_iff hv).mpr h.symm

theorem sphereVolumeForm_orientation_independent
    (b c : OrthonormalBasis (Fin (d+1)) ℝ E)
    (h : b.toBasis.orientation = c.toBasis.orientation) :
    sphereVolumeForm b = sphereVolumeForm c := by
  funext u
  ext v
  simp only [sphereVolumeForm_apply]
  rw [OrthonormalBasis.same_orientation_iff_det_eq_det.mpr h]

theorem sphereFormCoefficient_orientation_independent
    (b c : OrthonormalBasis (Fin (d+1)) ℝ E)
    (h : b.toBasis.orientation = c.toBasis.orientation)
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) :
    sphereFormCoefficient b α = sphereFormCoefficient c α := by
  funext u
  unfold sphereFormCoefficient
  rw [sphereVolumeForm_orientation_independent b c h]

theorem sphereFormCoefficient_fsmul
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (f : sphere (0:E) 1 → ℝ)
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) (u : sphere (0:E) 1) :
    sphereFormCoefficient b (fun x ↦ f x • α x) u = f u * sphereFormCoefficient b α u := by
  apply (sphereFormCoefficient_eq_iff b _ u _).mpr
  rw [sphereForm_eq_coefficient_smul b α u, smul_smul]

@[simp] theorem sphereFormCoefficient_fsmul_volume
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (f : sphere (0:E) 1 → ℝ)
    (u : sphere (0:E) 1) :
    sphereFormCoefficient b (fun x ↦ f x • sphereVolumeForm b x) u = f u :=
  (sphereFormCoefficient_eq_iff b _ u (f u)).mpr rfl

@[simp] theorem sphereFormCoefficient_zero
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (u : sphere (0:E) 1) :
    sphereFormCoefficient b (0 : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) u = 0 :=
  (sphereFormCoefficient_eq_iff b _ u 0).mpr (by simp)

@[simp] theorem sphereFormCoefficient_volume
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (u : sphere (0:E) 1) :
    sphereFormCoefficient b (sphereVolumeForm b) u = 1 :=
  (sphereFormCoefficient_eq_iff b _ u 1).mpr (by simp)

section Coordinates

open DifferentialForm

/-- The actual coordinate coefficient, with no geometric imports needed. -/
def sphereCoordinateCoefficient
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (α : Form (𝓡 d) (sphere (0:E) 1) d) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  chartRepresentation e α y (EuclideanSpace.basisFun (Fin d) ℝ)

/-- The chart density is evaluation of the genuine outward area form. -/
def sphereChartDensity (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sphereCoordinateCoefficient e (sphereVolumeForm b) y

theorem sphereForm_coefficient_in_chart (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (α : Form (𝓡 d) (sphere (0:E) 1) d) (y : EuclideanSpace ℝ (Fin d)) :
    sphereCoordinateCoefficient e α y =
      sphereFormCoefficient b α (e.symm y) * sphereChartDensity b e y := by
  change α (e.symm y) _ = sphereFormCoefficient b α (e.symm y) * sphereVolumeForm b (e.symm y) _
  rw [sphereForm_eq_coefficient_smul b α (e.symm y)]
  rfl

theorem sphereChartDensity_ne_zero (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ e.target) :
    sphereChartDensity b e y ≠ 0 := by
  let hd : e.MDifferentiable (𝓡 d) (𝓡 d) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  exact sphereVolumeForm_basis_ne_zero b (e.symm y)
    ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.map (hd.symm.mfderiv hy).toLinearEquiv)

/-- The intrinsic coefficient equals the quotient of actual chart coefficients. -/
theorem sphereFormCoefficient_chart_ratio (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (α : Form (𝓡 d) (sphere (0:E) 1) d) (y : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ e.target) :
    sphereFormCoefficient b α (e.symm y) =
      sphereCoordinateCoefficient e α y / sphereChartDensity b e y := by
  apply (eq_div_iff (sphereChartDensity_ne_zero b e he y hy)).mpr
  exact (sphereForm_coefficient_in_chart b e α y).symm

/-- The chart expression uses the actual ambient derivative of the inverse
chart. This is the density appearing in polar change of variables. -/
theorem sphereChartDensity_eq_det (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ e.target) :
    sphereChartDensity b e y = b.toBasis.det
      (Fin.cons (e.symm y : E) (fun i ↦
        fderiv ℝ (fun z ↦ (e.symm z : E)) y (EuclideanSpace.basisFun (Fin d) ℝ i))) := by
  have hc := mvfderiv_comp y
    ((contMDiff_coe_sphere (n := d) (m := ∞) (e.symm y)).mdifferentiableAt (by simp))
    ((contMDiffAt_symm_of_mem_maximalAtlas he hy).mdifferentiableAt (by simp))
  rw [mvfderiv_eq_fderiv] at hc
  change b.toBasis.det (Fin.cons (e.symm y:E) (fun i ↦
    mvfderiv (𝓡 d) ((↑) : sphere (0:E) 1 → E) (e.symm y)
      (mfderiv (𝓡 d) (𝓡 d) e.symm y (EuclideanSpace.basisFun (Fin d) ℝ i)))) = _
  apply congrArg b.toBasis.det
  funext i
  refine Fin.cases rfl (fun j ↦ ?_) i
  exact (congrArg (fun L ↦ L (EuclideanSpace.basisFun (Fin d) ℝ j)) hc).symm

theorem chartRepresentation_sphereVolumeForm (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ e.target) :
    chartRepresentation e (sphereVolumeForm b) y =
      ((sphereAmbientVolume b).curryLeft (e.symm y:E)).compContinuousLinearMap
        (fderiv ℝ (fun z ↦ (e.symm z:E)) y) := by
  have hc := mvfderiv_comp y
    ((contMDiff_coe_sphere (n := d) (m := ∞) (e.symm y)).mdifferentiableAt (by simp))
    ((contMDiffAt_symm_of_mem_maximalAtlas he hy).mdifferentiableAt (by simp))
  rw [mvfderiv_eq_fderiv] at hc
  ext v
  change b.toBasis.det (Fin.cons (e.symm y:E) (fun i ↦
    mvfderiv (𝓡 d) ((↑) : sphere (0:E) 1 → E) (e.symm y)
      (mfderiv (𝓡 d) (𝓡 d) e.symm y (v i)))) =
    b.toBasis.det (Fin.cons (e.symm y:E) (fun i ↦
      fderiv ℝ (fun z ↦ (e.symm z:E)) y (v i)))
  apply congrArg b.toBasis.det
  funext i
  refine Fin.cases rfl (fun j ↦ ?_) i
  exact (congrArg (fun L ↦ L (v j)) hc).symm

theorem isSmooth_sphereVolumeForm (b : OrthonormalBasis (Fin (d+1)) ℝ E) :
    IsSmooth (sphereVolumeForm b) := by
  intro e he y hy
  have hf : ContDiffAt ℝ ∞ (fun z ↦ (e.symm z:E)) y :=
    ((contMDiff_coe_sphere (n := d) (m := ∞) (e.symm y)).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas he hy)).contDiffAt
  have ha := (sphereAmbientVolume b).curryLeft.contDiff.contDiffAt.comp y hf
  have hD := hf.fderiv_right (m := ∞) (by simp)
  have hpoly := contDiffAt_compContinuousLinearMap ha hD
  apply (hpoly.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [e.open_target.mem_nhds hy] with z hz
  exact chartRepresentation_sphereVolumeForm b e he z hz

theorem contDiffOn_sphereChartDensity (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1)) :
    ContDiffOn ℝ ∞ (sphereChartDensity b e) e.target :=
  (ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℝ (Fin d)) ℝ (EuclideanSpace.basisFun (Fin d) ℝ)).contDiff.comp_contDiffOn
    (isSmooth_sphereVolumeForm b e he)

theorem contMDiff_sphereFormCoefficient (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (α : Form (𝓡 d) (sphere (0:E) 1) d) (hα : IsSmooth α) :
    ContMDiff (𝓡 d) 𝓘(ℝ,ℝ) ∞ (sphereFormCoefficient b α) := by
  intro u
  let e := chartAt (EuclideanSpace ℝ (Fin d)) u
  have he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1) :=
    IsManifold.chart_mem_maximalAtlas u
  have hu : u ∈ e.source := mem_chart_source _ _
  have hnum : ContDiffOn ℝ ∞ (sphereCoordinateCoefficient e α) e.target :=
    (ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℝ (Fin d)) ℝ (EuclideanSpace.basisFun (Fin d) ℝ)).contDiff.comp_contDiffOn (hα e he)
  have hden := contDiffOn_sphereChartDensity b e he
  have hquot := (hnum.contDiffAt (e.open_target.mem_nhds (e.map_source hu))).div
    (hden.contDiffAt (e.open_target.mem_nhds (e.map_source hu)))
    (sphereChartDensity_ne_zero b e he (e u) (e.map_source hu))
  have hc := hquot.contMDiffAt.comp u (contMDiffAt_of_mem_maximalAtlas he hu)
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hu] with x hx
  simpa only [e.left_inv hx, Function.comp_apply, Pi.div_apply] using
    sphereFormCoefficient_chart_ratio b e he α (e x) (e.map_source hx)

end Coordinates

section Integral
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Integrate the actual top-form coefficient against the polar sphere measure. -/
def sphereFormIntegral (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) : ℝ :=
  ∫ u, sphereFormCoefficient b α u ∂(volume : Measure E).toSphere

@[simp] theorem sphereFormIntegral_fsmul_volume
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (f : sphere (0:E) 1 → ℝ) :
    sphereFormIntegral b (fun u ↦ f u • sphereVolumeForm b u) =
      ∫ u, f u ∂(volume : Measure E).toSphere := by
  simp [sphereFormIntegral]

theorem sphereFormIntegral_orientation_independent
    (b c : OrthonormalBasis (Fin (d+1)) ℝ E)
    (h : b.toBasis.orientation = c.toBasis.orientation)
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) :
    sphereFormIntegral b α = sphereFormIntegral c α := by
  unfold sphereFormIntegral
  rw [sphereFormCoefficient_orientation_independent b c h α]

@[simp] theorem sphereFormIntegral_volume
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) :
    sphereFormIntegral b (sphereVolumeForm b) = (volume : Measure E).toSphere.real Set.univ := by
  simp [sphereFormIntegral]

theorem integrable_sphereFormCoefficient (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d)
    (hα : DifferentialForm.IsSmooth α) :
    Integrable (sphereFormCoefficient b α) (volume : Measure E).toSphere := by
  letI : CompactSpace (sphere (0:E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  simpa only [integrableOn_univ] using
    (contMDiff_sphereFormCoefficient b α hα).continuous.continuousOn.integrableOn_compact
      isCompact_univ

end Integral
end GaussBonnetChern
