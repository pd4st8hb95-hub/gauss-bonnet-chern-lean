import GaussBonnetChern.SphereFormIntegration
import GaussBonnetChern.GenericFormIntegration
import GaussBonnetChern.SphereMeasureCoordinates
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Agreement of sphere forms, polar area and coordinate integration

The normal-first determinant is the actual density of the canonical polar
sphere measure in every smooth chart. Restriction and pushforward turn that
proved measure identity into a Bochner change-of-variables formula. Positive
charts and a subordinate finite partition then reproduce the literal sum of
top-form coordinate integrals, including genuine integrability of each term.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology Manifold ContDiff BigOperators

namespace GaussBonnetChern

theorem map_inverse_chart_restrict_of_image_measure
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : OpenPartialHomeomorph X Y) (μ : Measure X) (ν : Measure Y)
    (h : ∀ t : Set Y, MeasurableSet t → t ⊆ e.target → μ (e.symm '' t) = ν t) :
    Measure.map e.symm (ν.restrict e.target) = μ.restrict e.source := by
  have hm : AEMeasurable e.symm (ν.restrict e.target) :=
    e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply_of_aemeasurable hm hs,
    Measure.restrict_apply' e.open_target.measurableSet, Measure.restrict_apply hs]
  have hf : Continuous (fun y : e.target ↦ e.symm y) :=
    e.continuousOn_symm.comp_continuous continuous_subtype_val (fun y ↦ y.property)
  have ht : MeasurableSet (e.symm ⁻¹' s ∩ e.target) := by
    have ht' := (MeasurableEmbedding.subtype_coe e.open_target.measurableSet).measurableSet_image.mpr
      (hf.measurable hs)
    convert ht' using 1
    ext y
    simp [and_comm]
  have hi : e.symm '' (e.symm ⁻¹' s ∩ e.target) = s ∩ e.source := by
    ext x
    constructor
    · rintro ⟨y,⟨hys,hyt⟩,rfl⟩
      exact ⟨hys,e.map_target hyt⟩
    · rintro ⟨hxs,hxe⟩
      refine ⟨e x,⟨?_,e.map_source hxe⟩,e.left_inv hxe⟩
      simpa only [mem_preimage,e.left_inv hxe] using hxs
  rw [← hi]
  exact (h _ ht inter_subset_right).symm

section Sphere

open Module Metric DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {d : ℕ} [Fact (finrank ℝ E = d+1)]

theorem sphereCoordinateCoefficient_eq_generic
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (α : Form (𝓡 d) (sphere (0:E) 1) d) :
    sphereCoordinateCoefficient e α = GenericFormIntegration.coefficient e α := rfl

/-- Actual polar area measure in a smooth sphere chart. -/
theorem sphereMeasure_map_inverse_chart
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1)) :
    Measure.map e.symm (((volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
      (fun y ↦ ENNReal.ofReal |sphereChartDensity b e y|)).restrict e.target) =
      (volume : Measure E).toSphere.restrict e.source := by
  apply map_inverse_chart_restrict_of_image_measure
  intro t ht hte
  rw [withDensity_apply _ ht,
    SphereMeasureCoordinates.toSphere_image_symm_chart b e he ht hte]
  apply setLIntegral_congr_fun ht
  intro y hy
  exact congrArg (fun r : ℝ ↦ ENNReal.ofReal |r|)
    (sphereChartDensity_eq_det b e he y (hte hy)).symm

/-- The scalar substitution theorem follows from the proved polar area
measure formula, with the genuine absolute normal Jacobian. -/
theorem sphere_setIntegral_eq_chart
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (f : sphere (0:E) 1 → ℝ) (hf : Continuous f) :
    (∫ u in e.source, f u ∂(volume : Measure E).toSphere) =
      ∫ y in e.target, |sphereChartDensity b e y| * f (e.symm y) := by
  rw [← sphereMeasure_map_inverse_chart b e he,
    integral_map (e.continuousOn_symm.aemeasurable e.open_target.measurableSet)
      hf.aestronglyMeasurable]
  have hJ : AEMeasurable (fun y ↦ ENNReal.ofReal |sphereChartDensity b e y|)
      (volume.restrict e.target) :=
    ((contDiffOn_sphereChartDensity b e he).continuousOn.abs.aemeasurable
      e.open_target.measurableSet).ennreal_ofReal
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hJ
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) _ e.open_target.measurableSet]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

/-- The transformed scalar integrand is genuinely integrable. This excludes
any use of a default value for a divergent coordinate integral. -/
theorem integrableOn_sphere_chart_scalar
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (f : sphere (0:E) 1 → ℝ) (hf : Continuous f) :
    IntegrableOn (fun y ↦ |sphereChartDensity b e y| * f (e.symm y)) e.target := by
  letI : CompactSpace (sphere (0:E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  have hfi : Integrable f (volume : Measure E).toSphere := by
    simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact isCompact_univ
  have hm := sphereMeasure_map_inverse_chart b e he
  have hmap : Integrable f (Measure.map e.symm
      ((volume.withDensity (fun y ↦ ENNReal.ofReal |sphereChartDensity b e y|)).restrict e.target)) := by
    rw [hm]
    exact hfi.restrict
  have hcomp := (integrable_map_measure hf.aestronglyMeasurable
    (e.continuousOn_symm.aemeasurable e.open_target.measurableSet)).mp hmap
  rw [restrict_withDensity e.open_target.measurableSet] at hcomp
  have hJ : AEMeasurable (fun y ↦ ENNReal.ofReal |sphereChartDensity b e y|)
      (volume.restrict e.target) :=
    ((contDiffOn_sphereChartDensity b e he).continuousOn.abs.aemeasurable
      e.open_target.measurableSet).ennreal_ofReal
  have h := (integrable_withDensity_iff_integrable_smul₀' hJ
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))).mp hcomp
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, Function.comp_apply,
    IntegrableOn] using h

theorem integrableOn_sphere_weighted_chart
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (hp : ∀ y ∈ e.target, 0 < sphereChartDensity b e y)
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Continuous ρ)
    (α : Form (𝓡 d) (sphere (0:E) 1) d) (hα : IsSmooth α) :
    IntegrableOn (fun y ↦ ρ (e.symm y) * GenericFormIntegration.coefficient e α y) e.target := by
  have h := integrableOn_sphere_chart_scalar b e he
    (fun u ↦ ρ u * sphereFormCoefficient b α u)
    (hρ.mul (contMDiff_sphereFormCoefficient b α hα).continuous)
  apply h.congr
  filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
  rw [← sphereCoordinateCoefficient_eq_generic,
    sphereForm_coefficient_in_chart b e α y, abs_of_pos (hp y hy)]
  ring

/-- A positively oriented chart integrates a supported top form exactly as
its intrinsic coefficient against the canonical polar sphere measure. -/
theorem sphere_weighted_chart_integral
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (hp : ∀ y ∈ e.target, 0 < sphereChartDensity b e y)
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Continuous ρ) (hs : Function.support ρ ⊆ e.source)
    (α : Form (𝓡 d) (sphere (0:E) 1) d) (hα : IsSmooth α) :
    (∫ y in e.target, ρ (e.symm y) * GenericFormIntegration.coefficient e α y) =
      sphereFormIntegral b (fun u ↦ ρ u • α u) := by
  have hc : Continuous (fun u ↦ ρ u * sphereFormCoefficient b α u) :=
    hρ.mul (contMDiff_sphereFormCoefficient b α hα).continuous
  have hchange := sphere_setIntegral_eq_chart b e he _ hc
  have hsupp : (∫ u in e.source, ρ u * sphereFormCoefficient b α u
      ∂(volume : Measure E).toSphere) =
      ∫ u, ρ u * sphereFormCoefficient b α u ∂(volume : Measure E).toSphere := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hz : ρ u = 0 := by
      by_contra hz
      exact hu (hs hz)
    simp only [hz,zero_mul]
  rw [hsupp] at hchange
  rw [sphereFormIntegral]
  simp_rw [sphereFormCoefficient_fsmul]
  rw [hchange]
  apply setIntegral_congr_fun e.open_target.measurableSet
  intro y hy
  change ρ (e.symm y) * sphereCoordinateCoefficient e α y =
    |sphereChartDensity b e y| * (ρ (e.symm y) * sphereFormCoefficient b α (e.symm y))
  rw [sphereForm_coefficient_in_chart b e α y, abs_of_pos (hp y hy)]
  ring

/-- Equality with the literal finite atlas-and-partition integral. Every
orientation and support condition is checked for the actual chart and weight;
the polar measure identity is proved above from change of variables. -/
theorem sphereFormIntegral_eq_finite_chart_integral
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) {q : ℕ}
    (e : Fin q → OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (hp : ∀ i y, y ∈ (e i).target → 0 < sphereChartDensity b (e i) y)
    (ρ : Fin q → sphere (0:E) 1 → ℝ) (hρ : ∀ i, Continuous (ρ i))
    (hs : ∀ i, Function.support (ρ i) ⊆ (e i).source)
    (hpart : ∀ u, ∑ i, ρ i u = 1)
    (α : Form (𝓡 d) (sphere (0:E) 1) d) (hα : IsSmooth α) :
    GenericFormIntegration.integral e ρ α = sphereFormIntegral b α := by
  letI : CompactSpace (sphere (0:E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  have hfi : ∀ i, Integrable (fun u ↦ ρ i u * sphereFormCoefficient b α u)
      (volume : Measure E).toSphere := by
    intro i
    have hc : Continuous (fun u ↦ ρ i u * sphereFormCoefficient b α u) :=
      (hρ i).mul (contMDiff_sphereFormCoefficient b α hα).continuous
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  unfold GenericFormIntegration.integral
  calc
    _ = ∑ i, sphereFormIntegral b (fun u ↦ ρ i u • α u) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sphere_weighted_chart_integral b (e i) (he i) (hp i) (ρ i) (hρ i) (hs i) α hα
    _ = _ := by
      simp only [sphereFormIntegral]
      simp_rw [sphereFormCoefficient_fsmul]
      rw [← integral_finsetSum Finset.univ (fun i _ ↦ hfi i)]
      apply integral_congr_ae
      filter_upwards with u
      rw [← Finset.sum_mul,hpart u,one_mul]

end Sphere
end GaussBonnetChern
