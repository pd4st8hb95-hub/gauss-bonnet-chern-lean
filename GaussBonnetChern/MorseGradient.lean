import GaussBonnetChern.ConnectionSmoothness

/-! # The actual metric gradient for the Morse branch

The gradient uses the Riesz isomorphism of the given Riemannian metric and the
actual manifold derivative. No vector field or Morse function is assumed to
exist here. Existence of a suitable Morse function remains a later obligation.
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

/-- Riesz representative of the real differential, for precisely the original
metric used in the main statement. -/
def gradient (f : M → ℝ) (x : M) : TangentSpace (model n) x :=
  (InnerProductSpace.toDual ℝ (TangentSpace (model n) x)).symm (mvfderiv (model n) f x)

@[simp] theorem inner_gradient (f : M → ℝ) (x : M) (v : TangentSpace (model n) x) :
    inner ℝ (gradient n M f x) v = mvfderiv (model n) f x v :=
  InnerProductSpace.toDual_symm_apply

theorem gradient_eq_zero_iff (f : M → ℝ) (x : M) :
    gradient n M f x = 0 ↔ mvfderiv (model n) f x = 0 := by
  exact (InnerProductSpace.toDual ℝ (TangentSpace (model n) x)).symm.map_eq_zero_iff

theorem contMDiffAt_gradient {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) :
    ContMDiffAt (model n) (model n).tangent ∞ (T% (gradient n M f)) x := by
  apply contMDiffAt_section_of_inner_localFrame n M
  intro v
  simpa only [inner_gradient] using
    contMDiffAt_directionalDerivative n M hf (contMDiffAt_localFrameVector n M x v)

theorem contMDiff_gradient {f : M → ℝ}
    (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f) :
    ContMDiff (model n) (model n).tangent ∞ (T% (gradient n M f)) :=
  fun x ↦ contMDiffAt_gradient n M (hf x)

/-- The covariant Hessian, computed by the actual Levi-Civita connection. -/
def hessian (f : M → ℝ) (x : M) (v w : TangentSpace (model n) x) : ℝ :=
  inner ℝ (connection n M (gradient n M f) x v) w

end GaussBonnetChern
