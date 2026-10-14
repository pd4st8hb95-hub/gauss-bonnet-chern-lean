import GaussBonnetChern.CriticalHessian
import GaussBonnetChern.GradientLinearization
import GaussBonnetChern.MorseExistence
import GaussBonnetChern.NondegenerateZeros

/-! # A gradient with finitely many nondegenerate zeros

The function is constructed using the actual compact Euclidean embedding and
Sard theorem. Its gradient uses the given metric, and nondegeneracy is transported
from the actual coordinate Hessian to the actual local linearization.
The index sum's equality with Euler characteristic is a subsequent theorem.
-/

noncomputable section
open Bundle
open scoped Manifold ContDiff
namespace GaussBonnetChern
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M] [CompactSpace M] [T2Space M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

theorem exists_smooth_function_nondegenerate_gradient :
    ∃ f : M → ℝ, ContMDiff (model n) 𝓘(ℝ) ∞ f ∧
      ∀ p, mvfderiv (model n) f p = 0 →
        Function.Injective (connection n M (gradient n M f) p) := by
  obtain ⟨N, e, a, Γ, hf, hcover, hH⟩ :=
    Morse.exists_smooth_function_nondegenerate_graph_charts (E := Model n) (M := M)
  refine ⟨Morse.squaredDistance e a, hf, ?_⟩
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hcover p
  have hy := q.chart.map_source hpq
  have hd : q.chart.MDifferentiable (model n) 𝓘(ℝ, q.tangent) :=
    ⟨q.smooth_chart.mdifferentiableOn (by simp), q.smooth_inverse.mdifferentiableOn (by simp)⟩
  have hgi : ∀ y ∈ q.chart.target,
      (mfderiv 𝓘(ℝ, q.tangent) (model n) q.chart.symm y).IsInvertible := by
    intro y hy
    exact ⟨hd.symm.mfderiv hy, rfl⟩
  have hp' : mvfderiv (model n) (Morse.squaredDistance e a) (q.chart.symm (q.chart p)) = 0 := by
    rw [q.chart.left_inv hpq]
    exact hp
  have hi := connection_gradient_injective_of_coordinate_hessian n M
    q.chart.open_target hy q.smooth_inverse hgi (hf _) hp' (hH q hq p hpq hp)
  have heq : q.chart.symm (q.chart p) = p := q.chart.left_inv hpq
  rw [heq] at hi
  exact hi

theorem exists_smooth_gradient_nondegenerate_zeros :
    ∃ f : M → ℝ, ContMDiff (model n) 𝓘(ℝ) ∞ f ∧
      ContMDiff (model n) (model n).tangent ∞ (T% (gradient n M f)) ∧
      ∀ p, gradient n M f p = 0 →
        Function.Injective (fieldLinearization n M p (gradient n M f)) := by
  obtain ⟨f, hf, hnondeg⟩ := exists_smooth_function_nondegenerate_gradient n M
  refine ⟨f, hf, contMDiff_gradient n M hf, ?_⟩
  intro p hp
  have hc := (gradient_eq_zero_iff n M f p).mp hp
  rw [gradientLinearization_eq_connection n M (hf p) hc]
  exact hnondeg p hc

theorem exists_smooth_gradient_finite_nondegenerate_zeros :
    ∃ f : M → ℝ, ContMDiff (model n) 𝓘(ℝ) ∞ f ∧
      ContMDiff (model n) (model n).tangent ∞ (T% (gradient n M f)) ∧
      {p : M | gradient n M f p = 0}.Finite ∧
      ∀ p, gradient n M f p = 0 →
        Function.Injective (fieldLinearization n M p (gradient n M f)) := by
  obtain ⟨f, hf, hX, hnondeg⟩ := exists_smooth_gradient_nondegenerate_zeros n M
  exact ⟨f, hf, hX, finite_field_zeroSet_of_injective n M hX hnondeg, hnondeg⟩

/-- The actual function, critical points and determinant-index sign in one
existence statement. No Poincaré--Hopf identity is assumed here. -/
theorem exists_morse_function_with_index_sign :
    ∃ (f : M → ℝ) (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f),
      {p : M | mvfderiv (model n) f p = 0}.Finite ∧
      ∀ p, mvfderiv (model n) f p = 0 →
        LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap ≠ 0 ∧
          Real.sign (LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap) =
            (-1 : ℝ) ^ morseIndex n M (hf p) := by
  obtain ⟨f, hf, hX, hfin, hnondeg⟩ := exists_smooth_gradient_finite_nondegenerate_zeros n M
  refine ⟨f, hf, ?_, ?_⟩
  · simpa only [gradient_eq_zero_iff] using hfin
  · intro p hp
    have hdet : LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap ≠ 0 := by
      intro hz
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz)
        (LinearMap.ker_eq_bot.mpr (hnondeg p ((gradient_eq_zero_iff n M f p).mpr hp)))
    exact ⟨hdet, sign_gradientLinearization_det n M (hf p) hp hdet⟩
end GaussBonnetChern
