import GaussBonnetChern.CriticalHessian
import GaussBonnetChern.HessianInertia

/-! # Coordinate and metric Morse indices at critical points

The equivalence is induced by the actual derivative of the parametrization.
The index in a Euclidean Morse normal form therefore agrees with the original
metric Morse index; the factor one half in Taylor's formula preserves it.
-/

noncomputable section
open Bundle
open scoped Manifold ContDiff
namespace GaussBonnetChern
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem coordinate_hessian_equivalent_metric_hessian
    {f : M → ℝ} {g : E → M} {s : Set E} {y : E}
    (hs : IsOpen s) (hy : y ∈ s)
    (hg : ContMDiffOn 𝓘(ℝ, E) (model n) ∞ g s)
    (hgi : ∀ z ∈ s, (mfderiv 𝓘(ℝ, E) (model n) g z).IsInvertible)
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f (g y))
    (hcritical : mvfderiv (model n) f (g y) = 0) :
    (hessianBilinear n M f (g y)).toBilinForm.toQuadraticMap.Equivalent
      (fderiv ℝ (fderiv ℝ (f ∘ g)) y).toBilinForm.toQuadraticMap := by
  obtain ⟨j, hj⟩ := hgi y hy
  let e : E ≃L[ℝ] TangentSpace (model n) (g y) :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm.trans j
  have he (v : E) : e v = mfderiv 𝓘(ℝ, E) (model n) g y v := by
    change j v = _
    exact congrArg (fun L : TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace (model n) (g y) ↦ L v) hj
  have hQ : (fderiv ℝ (fderiv ℝ (f ∘ g)) y).toBilinForm.toQuadraticMap =
      (hessianBilinear n M f (g y)).toBilinForm.toQuadraticMap.comp e.toLinearEquiv.toLinearMap := by
    ext v
    change fderiv ℝ (fderiv ℝ (f ∘ g)) y v v = hessian n M f (g y) (e v) (e v)
    rw [he]
    exact hessian_pullback_at_critical n M hs hy hg hgi hf hcritical v v
  rw [hQ]
  exact ⟨(hessianBilinear n M f (g y)).toBilinForm.toQuadraticMap.isometryEquivOfCompLinearEquiv
    e.toLinearEquiv⟩

theorem morseIndex_eq_sigNeg_coordinate_hessian
    {f : M → ℝ} {g : E → M} {s : Set E} {y : E}
    (hs : IsOpen s) (hy : y ∈ s)
    (hg : ContMDiffOn 𝓘(ℝ, E) (model n) ∞ g s)
    (hgi : ∀ z ∈ s, (mfderiv 𝓘(ℝ, E) (model n) g z).IsInvertible)
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f (g y))
    (hcritical : mvfderiv (model n) f (g y) = 0) :
    morseIndex n M hf = sigNeg (fderiv ℝ (fderiv ℝ (f ∘ g)) y).toBilinForm.toQuadraticMap := by
  rw [morseIndex_eq_sigNeg_hessian n M hf]
  exact (coordinate_hessian_equivalent_metric_hessian n M hs hy hg hgi hf hcritical).sigNeg_eq

theorem morseIndex_eq_sigNeg_coordinate_half_hessian
    {f : M → ℝ} {g : E → M} {s : Set E} {y : E}
    (hs : IsOpen s) (hy : y ∈ s)
    (hg : ContMDiffOn 𝓘(ℝ, E) (model n) ∞ g s)
    (hgi : ∀ z ∈ s, (mfderiv 𝓘(ℝ, E) (model n) g z).IsInvertible)
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f (g y))
    (hcritical : mvfderiv (model n) f (g y) = 0) :
    morseIndex n M hf =
      sigNeg ((1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ (f ∘ g)) y).toBilinForm.toQuadraticMap) := by
  rw [sigNeg_smul_pos _ (by norm_num)]
  exact morseIndex_eq_sigNeg_coordinate_hessian n M hs hy hg hgi hf hcritical

end GaussBonnetChern
