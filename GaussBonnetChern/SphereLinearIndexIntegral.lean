import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Basic.Real.Sign

/-! # The scalar sphere integral for an invertible linear map

This uses the genuine polar measure `Measure.toSphere`. It is the scalar
calculation needed for local index normalization; identifying a differential
form pullback with this scalar density is a separate geometric obligation.
-/

noncomputable section

open MeasureTheory Set Metric Function
open scoped ENNReal NNReal Topology

namespace GaussBonnetChern

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

section Haar

variable [MeasurableSpace E] [BorelSpace E]

theorem norm_linearEquiv_unitSphere_pos (L : E ≃L[ℝ] E) (u : sphere (0 : E) 1) :
    0 < ‖L u‖ := by
  apply norm_pos_iff.mpr
  intro hz
  apply ne_of_mem_sphere u.property one_ne_zero
  apply L.injective
  simpa using hz

theorem continuous_sphere_inverse_norm_pow (L : E ≃L[ℝ] E) (d : ℕ) :
    Continuous (fun u : sphere (0 : E) 1 ↦ (‖L u‖⁻¹) ^ d) :=
  ((L.continuous.comp continuous_subtype_val).norm.inv₀
    (fun u ↦ (norm_linearEquiv_unitSphere_pos L u).ne')).pow d

theorem integrable_sphere_inverse_norm_pow (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E ≃L[ℝ] E) (d : ℕ) :
    Integrable (fun u : sphere (0 : E) 1 ↦ (‖L u‖⁻¹) ^ d) μ.toSphere := by
  letI : CompactSpace (sphere (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  simpa only [integrableOn_univ] using
    (continuous_sphere_inverse_norm_pow L d).continuousOn.integrableOn_compact isCompact_univ

/-- Polar slicing of the actual ellipsoid gives the radial inverse-power integral. -/
theorem ellipsoid_volume_eq_sphere_lintegral [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (L : E ≃L[ℝ] E) :
    μ (L ⁻¹' ball (0 : E) 1) =
      ∫⁻ u : sphere (0 : E) 1,
        ENNReal.ofReal ((‖L u‖⁻¹) ^ Module.finrank ℝ E / Module.finrank ℝ E) ∂μ.toSphere := by
  let T : Set E := L ⁻¹' ball 0 1
  let P := homeomorphUnitSphereProd E
  let S : Set (sphere (0 : E) 1 × Ioi (0 : ℝ)) :=
    (Subtype.val ∘ P.symm) ⁻¹' T
  have hT : MeasurableSet T := L.continuous.measurable measurableSet_ball
  have hS : MeasurableSet S := hT.preimage (measurable_subtype_coe.comp P.symm.measurable)
  have himage : Subtype.val '' (P ⁻¹' S) = T \ {0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, y.property⟩
      simpa only [S, mem_preimage, Function.comp_apply, P.symm_apply_apply] using hy
    · rintro ⟨hx, hx0⟩
      refine ⟨⟨x, hx0⟩, ?_, rfl⟩
      simpa only [S, mem_preimage, Function.comp_apply, P.symm_apply_apply] using hx
  have hpolar := μ.measurePreserving_homeomorphUnitSphereProd.measure_preimage hS.nullMeasurableSet
  rw [comap_subtype_coe_apply (measurableSet_singleton _).compl,
    himage, measure_sdiff_null (measure_singleton _)] at hpolar
  rw [hpolar, Measure.prod_apply hS]
  apply lintegral_congr
  intro u
  have hnorm := norm_linearEquiv_unitSphere_pos L u
  have hslice : Prod.mk u ⁻¹' S = Iio (⟨‖L u‖⁻¹, inv_pos.mpr hnorm⟩ : Ioi (0 : ℝ)) := by
    ext r
    simp only [S, T, P, mem_preimage, Function.comp_apply,
      homeomorphUnitSphereProd_symm_apply_coe, mem_ball, dist_zero_right,
      map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos r.property.out,
      mem_Iio, Subtype.mk_lt_mk]
    change (r : ℝ) * ‖L u‖ < 1 ↔ (r : ℝ) < ‖L u‖⁻¹
    rw [← one_div]
    exact (lt_div_iff₀ hnorm).symm
  rw [hslice, Measure.volumeIoiPow_apply_Iio, Nat.sub_add_cancel Module.finrank_pos]
  simp only [Nat.cast_sub Module.finrank_pos, Nat.cast_one, sub_add_cancel]

/-- The real radial integral, proved using genuine integrability rather than default values. -/
theorem ellipsoid_measureReal_eq_sphere_integral [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (L : E ≃L[ℝ] E) :
    μ.real (L ⁻¹' ball (0 : E) 1) =
      (∫ u : sphere (0 : E) 1, (‖L u‖⁻¹) ^ Module.finrank ℝ E ∂μ.toSphere) /
        Module.finrank ℝ E := by
  have hfi := (integrable_sphere_inverse_norm_pow μ L (Module.finrank ℝ E)).div_const
    (Module.finrank ℝ E : ℝ)
  have hnonneg : ∀ u : sphere (0 : E) 1,
      0 ≤ (‖L u‖⁻¹) ^ Module.finrank ℝ E / (Module.finrank ℝ E : ℝ) := by
    intro u
    positivity
  have h := ellipsoid_volume_eq_sphere_lintegral μ L
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hnonneg)] at h
  apply_fun ENNReal.toReal at h
  rw [ENNReal.toReal_ofReal (integral_nonneg hnonneg), integral_div] at h
  exact h

/-- Inverse radial-power mass is the determinant-scaled actual polar sphere mass. -/
theorem integral_sphere_inverse_norm_finrank [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (L : E ≃L[ℝ] E) :
    (∫ u : sphere (0 : E) 1, (‖L u‖⁻¹) ^ Module.finrank ℝ E ∂μ.toSphere) =
      |LinearMap.det L.toLinearMap|⁻¹ * μ.toSphere.real univ := by
  have hdet : LinearMap.det L.toLinearMap ≠ 0 := L.toLinearEquiv.isUnit_det'.ne_zero
  have hcov := μ.addHaar_preimage_continuousLinearMap
    (f := (L : E →L[ℝ] E)) hdet (ball (0 : E) 1)
  have hcovReal := congrArg ENNReal.toReal hcov
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv] at hcovReal
  have hradial := ellipsoid_measureReal_eq_sphere_integral μ L
  have hd : (Module.finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [eq_div_iff hd] at hradial
  rw [← hradial, μ.toSphere_real_apply_univ]
  change _ = _ at hcovReal
  rw [show μ.real (L ⁻¹' ball (0 : E) 1) =
    |LinearMap.det L.toLinearMap|⁻¹ * μ.real (ball (0 : E) 1) from hcovReal]
  ring

theorem integrable_sphere_linearIndex_density (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E ≃L[ℝ] E) :
    Integrable (fun u : sphere (0 : E) 1 ↦
      LinearMap.det L.toLinearMap / ‖L u‖ ^ Module.finrank ℝ E) μ.toSphere := by
  simpa only [div_eq_mul_inv, inv_pow] using
    (integrable_sphere_inverse_norm_pow μ L (Module.finrank ℝ E)).const_mul
      (LinearMap.det L.toLinearMap)

/-- The scalar local-index formula for every positive finite dimension. -/
theorem integral_sphere_linearIndex_density [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (L : E ≃L[ℝ] E) :
    (∫ u : sphere (0 : E) 1,
      LinearMap.det L.toLinearMap / ‖L u‖ ^ Module.finrank ℝ E ∂μ.toSphere) =
        Real.sign (LinearMap.det L.toLinearMap) * μ.toSphere.real univ := by
  simp only [div_eq_mul_inv, ← inv_pow]
  rw [integral_const_mul, integral_sphere_inverse_norm_finrank, ← mul_assoc]
  congr 1
  have hdet : LinearMap.det L.toLinearMap ≠ 0 := L.toLinearEquiv.isUnit_det'.ne_zero
  rcases hdet.lt_or_gt with hn | hp
  · rw [abs_of_neg hn, Real.sign_of_neg hn]
    field_simp
  · rw [abs_of_pos hp, Real.sign_of_pos hp]
    exact mul_inv_cancel₀ hdet

end Haar

/-- Specialization to `volume`, with dimension positivity explicit. -/
theorem integral_volumeSphere_linearIndex [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)] (hdim : 0 < Module.finrank ℝ E)
    (L : E ≃L[ℝ] E) :
    (∫ u : sphere (0 : E) 1,
      LinearMap.det L.toLinearMap / ‖L u‖ ^ Module.finrank ℝ E
        ∂(volume : Measure E).toSphere) =
      Real.sign (LinearMap.det L.toLinearMap) * (volume : Measure E).toSphere.real univ := by
  letI : Nontrivial E := Module.finrank_pos_iff.mp hdim
  exact integral_sphere_linearIndex_density volume L

end GaussBonnetChern
