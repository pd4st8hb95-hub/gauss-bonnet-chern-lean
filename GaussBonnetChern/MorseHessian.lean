import GaussBonnetChern.MorseGradient
import GaussBonnetChern.CurvatureTensor

/-! # Symmetry of the actual metric Hessian

This connects the chosen metric gradient to the Levi-Civita connection.
No critical-point or Morse-function existence assumption is used in the
symmetry theorem; torsion zero and the scalar commutator identity suffice.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

namespace GaussBonnetChern

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

def hessianBilinear (f : M → ℝ) (x : M) :
    TangentSpace (model n) x →L[ℝ] TangentSpace (model n) x →L[ℝ] ℝ :=
  (innerSL ℝ).comp (connection n M (gradient n M f) x)

@[simp] theorem hessianBilinear_apply (f : M → ℝ) (x : M)
    (v w : TangentSpace (model n) x) :
    hessianBilinear n M f x v w = hessian n M f x v w := rfl

/-- Raising the second Hessian index by the given metric recovers the
covariant derivative of its gradient. -/
theorem connection_gradient_eq_raise_hessian (f : M → ℝ) (x : M)
    (v : TangentSpace (model n) x) :
    connection n M (gradient n M f) x v =
      (InnerProductSpace.toDual ℝ (TangentSpace (model n) x)).symm
        (hessianBilinear n M f x v) := by
  change _ = (InnerProductSpace.toDual ℝ (TangentSpace (model n) x)).symm
    ((InnerProductSpace.toDual ℝ (TangentSpace (model n) x))
      (connection n M (gradient n M f) x v))
  exact ((InnerProductSpace.toDual ℝ (TangentSpace (model n) x)).symm_apply_apply _).symm

theorem hessian_symm {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x)
    (u v : TangentSpace (model n) x) :
    hessian n M f x u v = hessian n M f x v u := by
  letI : IsContMDiffRiemannianBundle (model n) 1 (Model n)
      (TangentSpace (model n) : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  let U := extend (Model n) (x := x) u
  let V := extend (Model n) (x := x) v
  have hU : ContMDiffAt (model n) (model n).tangent ∞ (T% U) x := contMDiffAt_extend ..
  have hV : ContMDiffAt (model n) (model n).tangent ∞ (T% V) x := contMDiffAt_extend ..
  have hG := contMDiffAt_gradient n M hf
  have hUV := (connection_isMetricCompatible n M).mvfderiv_inner_eq U
    (hG.mdifferentiableAt (by simp)) (hV.mdifferentiableAt (by simp))
  have hVU := (connection_isMetricCompatible n M).mvfderiv_inner_eq V
    (hG.mdifferentiableAt (by simp)) (hU.mdifferentiableAt (by simp))
  simp only [inner_gradient] at hUV hVU
  have ht := connection_torsion_apply n M (hU.mdifferentiableAt (by simp))
    (hV.mdifferentiableAt (by simp))
  have hb := mvfderiv_mlieBracket_scalar n M hU hV hf
  rw [← ht, map_sub] at hb
  have hs : inner ℝ (connection n M (gradient n M f) x (U x)) (V x) =
      inner ℝ (connection n M (gradient n M f) x (V x)) (U x) := by
    linarith [hUV, hVU, hb]
  simpa only [hessian, U, V, extend_apply_self] using hs

end GaussBonnetChern
