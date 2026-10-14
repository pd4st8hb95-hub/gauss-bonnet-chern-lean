import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! # Equal-dimensional Sard and simultaneous regular values

This uses Mathlib's proved differentiable equal-dimensional Sard theorem.  In
particular no full unequal-dimensional Sard theorem is imported as a premise.
The countable-family version is intended for local normal-endpoint charts.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter

namespace GaussBonnetChern.Morse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem det_ne_zero_iff_injective (L : E →L[ℝ] E) :
    L.det ≠ 0 ↔ Function.Injective L := by
  have h := not_congr (LinearMap.det_eq_zero_iff_ker_ne_bot (f := L.toLinearMap))
  simpa only [ContinuousLinearMap.det, not_not, LinearMap.ker_eq_bot] using! h

/-- Critical values from a specified region, using the actual Fréchet derivative. -/
def criticalValuesOn (f : E → E) (s : Set E) : Set E :=
  f '' {x | x ∈ s ∧ (fderiv ℝ f x).det = 0}

theorem measure_criticalValuesOn (μ : Measure E) [IsAddHaarMeasure μ]
    {f : E → E} {s : Set E} (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    μ (criticalValuesOn f s) = 0 := by
  exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun x hx => (hf x hx.1).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx.2)

/-- Almost every target is a regular value simultaneously for countably many
equal-dimensional differentiable parametrizations. -/
theorem ae_regularValue_countable (μ : Measure E) [IsAddHaarMeasure μ]
    {ι : Type*} [Countable ι] (f : ι → E → E) (s : ι → Set E)
    (hf : ∀ i x, x ∈ s i → DifferentiableAt ℝ (f i) x) :
    ∀ᵐ a ∂μ, ∀ i x, x ∈ s i → f i x = a → (fderiv ℝ (f i) x).det ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  have h : ∀ᵐ a ∂μ, a ∉ criticalValuesOn (f i) (s i) := by
    apply ae_iff.mpr
    simpa only [not_not, Set.setOf_mem_eq] using measure_criticalValuesOn μ (hf i)
  filter_upwards [h] with a ha
  intro x hx hxa hdet
  exact ha ⟨x, ⟨hx, hdet⟩, hxa⟩

theorem exists_regularValue_countable (μ : Measure E) [IsAddHaarMeasure μ]
    {ι : Type*} [Countable ι] (f : ι → E → E) (s : ι → Set E)
    (hf : ∀ i x, x ∈ s i → DifferentiableAt ℝ (f i) x) :
    ∃ a, ∀ i x, x ∈ s i → f i x = a → (fderiv ℝ (f i) x).det ≠ 0 :=
  (ae_regularValue_countable μ f s hf).exists

/-- The source models may vary from chart to chart, provided each is linearly
equivalent to the fixed target. This is the equal-dimensional situation of
normal endpoint charts; the conclusion concerns their actual derivatives. -/
theorem exists_injective_fderiv_fibers_countable (μ : Measure E) [IsAddHaarMeasure μ]
    {ι : Type*} [Countable ι] (G : ι → Type*)
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
    (c : ∀ i, G i ≃L[ℝ] E) (f : ∀ i, G i → E) (s : ∀ i, Set (G i))
    (hf : ∀ i x, x ∈ s i → DifferentiableAt ℝ (f i) x) :
    ∃ a, ∀ i x, x ∈ s i → f i x = a → Function.Injective (fderiv ℝ (f i) x) := by
  let f' : ι → E → E := fun i => f i ∘ (c i).symm
  let s' : ι → Set E := fun i => (c i) '' s i
  have hdiff : ∀ i y, y ∈ s' i → DifferentiableAt ℝ (f' i) y := by
    intro i y hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply DifferentiableAt.comp
    · simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf i x hx
    · exact (c i).symm.differentiableAt
  obtain ⟨a, ha⟩ := exists_regularValue_countable μ f' s' hdiff
  refine ⟨a, ?_⟩
  intro i x hx hxa
  have hcrit := ha i ((c i) x) ⟨x, hx, rfl⟩ (by simpa [f'] using hxa)
  have hinj := (det_ne_zero_iff_injective _).mp hcrit
  have hd : fderiv ℝ (f' i) ((c i) x) =
      (fderiv ℝ (f i) x).comp ((c i).symm : E →L[ℝ] G i) := by
    simpa only [f', ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.fderiv]
      using fderiv_comp ((c i) x)
        (show DifferentiableAt ℝ (f i) ((c i).symm ((c i) x)) from by
          simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf i x hx)
        (c i).symm.differentiableAt
  rw [hd] at hinj
  exact (Function.Injective.of_comp_iff' _ (c i).symm.bijective).mp hinj

end GaussBonnetChern.Morse
