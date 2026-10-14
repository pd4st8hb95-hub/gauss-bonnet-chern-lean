import GaussBonnetChern.DifferentialForms
import GaussBonnetChern.NondegenerateScaling
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! # Actual radial pullback factors for differential forms

These are identities and uniform estimates for the existing pullback.
In particular a pulled-back connection one-form has
one radial factor, while a curvature two-form has two. No asymptotic estimate
is added to the hypotheses of the geometric main theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set Metric
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern



namespace AngularScaling
open DifferentialForm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pullback of a genuine model-space form along the actual dilation. -/
theorem pullback_dilation (r : ℝ) {k : ℕ} (α : Form 𝓘(ℝ, E) E k) (x : E) :
    pullback (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (fun y : E => r • y) α x =
      r ^ k • α (r • x) := by
  ext v
  have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : E => r • y) x =
      r • ContinuousLinearMap.id ℝ E := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id x).const_smul r).fderiv
  change α (r • x) (fun j => mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
      (fun y : E => r • y) x (v j)) = (r ^ k • α (r • x)) v
  rw [hd]
  change α (r • x) (fun j => r • v j) = r ^ k • α (r • x) v
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (α (r • x)).map_smul_univ (fun _ => r) v

theorem uniform_eventually_bounded_of_continuousAt {g : E → F} (hg : ContinuousAt g 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u ∈ sphere (0 : E) 1, ‖g (r • u)‖ ≤ ‖g 0‖ + 1 := by
  have hu := LocalIndex.tendstoUniformlyOn_smul_of_continuousAt hg
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) 1 zero_lt_one] with r hr
  intro u hu
  have h := hr u hu
  rw [dist_eq_norm, norm_sub_rev] at h
  have hn := norm_sub_norm_le (g (r • u)) (g 0)
  linarith

/-- Uniform decay of a genuinely bounded family multiplied by a scalar
converging to zero. This estimate is also used for connection correction terms. -/
theorem uniform_smul_zero_of_bounded {T X : Type*} {l : Filter T} {s : Set X}
    {f : T → X → F} {c : T → ℝ} (hc : Tendsto c l (𝓝 0)) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ t in l, ∀ x ∈ s, ‖f t x‖ ≤ C) :
    TendstoUniformlyOn (fun t x => c t • f t x) (fun _ => (0 : F)) l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hden : 0 < C + 1 := by linarith
  have hsmall := hc.eventually (ball_mem_nhds (0 : ℝ) (div_pos hε hden))
  filter_upwards [hf, hsmall] with t ht hct
  have hct' : ‖c t‖ < ε / (C + 1) := by simpa only [mem_ball, dist_zero_right] using hct
  intro x hx
  rw [dist_zero_left, norm_smul]
  calc
    ‖c t‖ * ‖f t x‖ ≤ ‖c t‖ * C := mul_le_mul_of_nonneg_left (ht x hx) (norm_nonneg _)
    _ ≤ ‖c t‖ * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ < ε := (lt_div_iff₀ hden).mp hct'

theorem uniform_radial_power_zero {g : E → F} (hg : ContinuousAt g 0)
    {k : ℕ} (hk : 0 < k) :
    TendstoUniformlyOn (fun r : ℝ => fun u : E => r ^ k • g (r • u))
      (fun _ => (0 : F)) (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
  apply uniform_smul_zero_of_bounded (C := ‖g 0‖ + 1) _ (by positivity)
    (uniform_eventually_bounded_of_continuousAt hg)
  simpa only [id_eq, zero_pow hk.ne'] using
    (tendsto_id.mono_left inf_le_left : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0)).pow k

/-- Every positive-degree smooth base form vanishes uniformly when pulled
back along shrinking coordinate spheres, in its actual ambient operator norm. -/
theorem uniform_pullback_dilation_zero {k : ℕ} (hk : 0 < k)
    {α : Form 𝓘(ℝ, E) E k}
    (hα : ContinuousAt (fun x : E => (show E [⋀^Fin k]→L[ℝ] ℝ from α x)) (0 : E)) :
    TendstoUniformlyOn (fun r : ℝ => fun x : E =>
      (show E [⋀^Fin k]→L[ℝ] ℝ from pullback (I := 𝓘(ℝ, E))
        (I' := 𝓘(ℝ, E)) (fun y : E => r • y) α x))
      (fun _ => (0 : E [⋀^Fin k]→L[ℝ] ℝ)) (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
  simpa only [pullback_dilation] using uniform_radial_power_zero hα hk

/-- Continuous finite-dimensional polynomial operations preserve a uniform
limit on a compact parameter set. A compact bound on all nearby inputs is
deduced here from the convergence and continuity of the limit. -/
theorem uniform_comp_continuous_of_compact {T X A B : Type*} [TopologicalSpace X]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [PseudoMetricSpace B] {l : Filter T} {s : Set X} (hs : IsCompact s)
    {f : T → X → A} {g : X → A} (hg : ContinuousOn g s)
    (hf : TendstoUniformlyOn f g l s) {G : A → B} (hG : Continuous G) :
    TendstoUniformlyOn (fun t x => G (f t x)) (fun x => G (g x)) l s := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hg
  let R := max C 0 + 1
  let K := closedBall (0 : A) R
  have hgK : ∀ x ∈ s, g x ∈ K := by
    intro x hx
    change dist (g x) 0 ≤ R
    rw [dist_zero_right]
    exact (hC x hx).trans ((le_max_left C 0).trans (by dsimp [R]; linarith))
  have hfK : ∀ᶠ t in l, ∀ x ∈ s, f t x ∈ K := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hf) 1 zero_lt_one] with t ht
    intro x hx
    have hh := ht x hx
    rw [dist_eq_norm, norm_sub_rev] at hh
    have hn := norm_sub_norm_le (f t x) (g x)
    have hb := hC x hx
    change dist (f t x) 0 ≤ R
    rw [dist_zero_right]
    dsimp [R]
    have hCmax := le_max_left C 0
    linarith
  exact ((isCompact_closedBall (0 : A) R).uniformContinuousOn_of_continuous
    hG.continuousOn).comp_tendstoUniformlyOn_eventually hfK hgK hf

end AngularScaling
end GaussBonnetChern
