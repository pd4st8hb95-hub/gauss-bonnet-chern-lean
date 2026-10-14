import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Smooth dependence of an integral on finite-dimensional parameters

The interval is fixed and compact. All domination bounds are obtained inside
the proof from a compact parameter ball; no global derivative bound is assumed.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace GaussBonnetChern.ParametricIntegration

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- Partial derivative in the parameter, expressed using the actual Fréchet derivative. -/
def parameterDerivative (f : E × ℝ → F) (p : E × ℝ) : E →L[ℝ] F :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)

theorem continuous_integral {f : E × ℝ → F} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun x => ∫ t in a..b, f (x, t)) := by
  have ha : Continuous (fun x => ∫ t in Icc a b, f (x, t)) :=
    continuous_parametric_integral_of_continuous (f := fun x t => f (x, t))
      (μ := volume) hf isCompact_Icc
  have hb : Continuous (fun x => ∫ t in Icc b a, f (x, t)) :=
    continuous_parametric_integral_of_continuous (f := fun x t => f (x, t))
      (μ := volume) hf isCompact_Icc
  simp_rw [intervalIntegral, restrict_Ioc_eq_restrict_Icc]
  exact ha.sub hb

theorem continuous_parameterDerivative {f : E × ℝ → F} (hf : ContDiff ℝ 1 f) :
    Continuous (parameterDerivative f) := by
  have hD : Continuous (fderiv ℝ f) := (contDiff_one_iff_fderiv.mp hf).2
  exact hD.clm_comp continuous_const

theorem hasFDerivAt_integral {f : E × ℝ → F} (hf : ContDiff ℝ 1 f)
    (a b : ℝ) (x : E) :
    HasFDerivAt (fun y => ∫ t in a..b, f (y, t))
      (∫ t in a..b, parameterDerivative f (x, t)) x := by
  have hD := continuous_parameterDerivative hf
  have hK : IsCompact (closedBall x 1 ×ˢ uIcc a b) :=
    (isCompact_closedBall x 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hD.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y t => parameterDerivative f (y, t))
    (s := ball x 1) (bound := fun _ => C) (ball_mem_nhds _ zero_lt_one)
  · filter_upwards with y
    exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards with t ht y hy
    exact hC (y, t) ⟨ball_subset_closedBall hy, uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · filter_upwards with t ht y hy
    have hpair : HasFDerivAt (fun z : E => (z, t))
        (ContinuousLinearMap.inl ℝ E ℝ) y := by
      have heq : (ContinuousLinearMap.id ℝ E).prod
          (0 : E →L[ℝ] ℝ) = ContinuousLinearMap.inl ℝ E ℝ := by ext v <;> rfl
      rw [← heq]
      exact ((hasFDerivAt_id (𝕜 := ℝ) y).prodMk (hasFDerivAt_const (𝕜 := ℝ) t y))
    exact ((hf.differentiable one_ne_zero (y, t)).hasFDerivAt).comp y hpair

theorem fderiv_integral {f : E × ℝ → F} (hf : ContDiff ℝ 1 f) (a b : ℝ) (x : E) :
    fderiv ℝ (fun y => ∫ t in a..b, f (y, t)) x =
      ∫ t in a..b, parameterDerivative f (x, t) :=
  (hasFDerivAt_integral hf a b x).fderiv

/-- Integration over a compact interval preserves every finite differentiability order. -/
theorem contDiff_integral_nat (k : ℕ) {f : E × ℝ → F} (hf : ContDiff ℝ k f)
    (a b : ℝ) : ContDiff ℝ k (fun x => ∫ t in a..b, f (x, t)) := by
  induction k generalizing f with
  | zero => exact contDiff_zero.mpr (continuous_integral hf.continuous a b)
  | succ k ih =>
    have h1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_pos k)
    have hd : ContDiff ℝ k (parameterDerivative f) :=
      (hf.fderiv_right (m := k) (by simp)).clm_comp contDiff_const
    rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp,
      contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (hasFDerivAt_integral h1 a b x).differentiableAt, by simp, ?_⟩
    intro v
    have heq : (fun x => fderiv ℝ (fun y => ∫ t in a..b, f (y, t)) x v) =
        fun x => ∫ t in a..b, parameterDerivative f (x, t) v := by
      funext x
      rw [fderiv_integral h1, ContinuousLinearMap.intervalIntegral_apply]
      exact ((continuous_parameterDerivative h1).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    rw [heq]
    exact ih (hd.clm_apply contDiff_const)

/-- A jointly smooth Banach-valued integrand has a smooth parameter integral. -/
theorem contDiff_integral {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, f (x, t)) := by
  rw [contDiff_infty]
  intro k
  exact contDiff_integral_nat k (hf.of_le (by simp)) a b

end GaussBonnetChern.ParametricIntegration
