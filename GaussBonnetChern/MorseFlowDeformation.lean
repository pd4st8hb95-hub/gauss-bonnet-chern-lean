import GaussBonnetChern.MorseGradient
import GaussBonnetChern.FlowDependence
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Homotopy.Equiv

/-! # Descent on a compact band without critical points

The vector field is constructed from the actual metric gradient, using a smooth
cutoff near its zero set. Its action on the given function is bounded between
`-1` and `0`, and is exactly `-1` on the specified regular band.
-/

noncomputable section

open Function Set Filter Bundle
open scoped Topology Manifold ContDiff

namespace GaussBonnetChern.Morse

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

def gradientEnergy (f : M → ℝ) (x : M) : ℝ :=
  inner ℝ (gradient n M f x) (gradient n M f x)

theorem contMDiff_gradientEnergy {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f) :
    ContMDiff (model n) 𝓘(ℝ) ∞ (gradientEnergy n M f) :=
  (contMDiff_gradient n M hf).inner_bundle (contMDiff_gradient n M hf)

theorem gradientEnergy_nonneg (f : M → ℝ) (x : M) : 0 ≤ gradientEnergy n M f x :=
  real_inner_self_nonneg

theorem gradientEnergy_eq_zero_iff (f : M → ℝ) (x : M) :
    gradientEnergy n M f x = 0 ↔ mvfderiv (model n) f x = 0 := by
  rw [gradientEnergy, inner_self_eq_zero, gradient_eq_zero_iff]

theorem mvfderiv_gradient (f : M → ℝ) (x : M) :
    mvfderiv (model n) f x (gradient n M f x) = gradientEnergy n M f x :=
  (inner_gradient n M f x (gradient n M f x)).symm

/-- The normalized descent field is globally smooth. Both the cutoff and its
support separation from critical points are constructed inside the proof. -/
theorem exists_normalizedGradientCutoff [T2Space M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f) {a b : ℝ}
    (hreg : ∀ x, f x ∈ Icc a b → mvfderiv (model n) f x ≠ 0) :
    ∃ v : (x : M) → TangentSpace (model n) x,
      ContMDiff (model n) (model n).tangent ∞ (T% v) ∧
      (∀ x, mvfderiv (model n) f x (v x) ∈ Icc (-1) 0) ∧
      ∀ x, f x ∈ Icc a b → mvfderiv (model n) f x (v x) = -1 := by
  let e := gradientEnergy n M f
  have he : ContMDiff (model n) 𝓘(ℝ) ∞ e := contMDiff_gradientEnergy n M hf
  let U : Set M := {x | e x ≠ 0}
  have hU : IsOpen U := (isClosed_eq he.continuous continuous_const).isOpen_compl
  have hband : IsClosed (f ⁻¹' Icc a b) := isClosed_Icc.preimage hf.continuous
  have hsub : f ⁻¹' Icc a b ⊆ U := by
    intro x hx
    exact fun he0 => hreg x hx ((gradientEnergy_eq_zero_iff n M f x).mp he0)
  obtain ⟨ρ, hρ0, hρ1, hρbound⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (model n) hU.isClosed_compl hband
      (disjoint_compl_left_iff_subset.mpr hsub) (n := ⊤)
  let c : M → ℝ := fun x => -(ρ x) / e x
  have hc : ContMDiff (model n) 𝓘(ℝ) ∞ c := by
    intro x
    by_cases hx : x ∈ U
    · exact (ρ.contMDiff x).neg.div₀ (he x) hx
    · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hρ0.filter_mono (nhds_le_nhdsSet hx)] with y hy
      simp [c, hy]
  let v : (x : M) → TangentSpace (model n) x := fun x => c x • gradient n M f x
  have hv : ContMDiff (model n) (model n).tangent ∞ (T% v) :=
    hc.smul_section (contMDiff_gradient n M hf)
  have hspeed (x : M) : mvfderiv (model n) f x (v x) = c x * e x := by
    simp [v, mvfderiv_gradient, e]
  refine ⟨v, hv, ?_, ?_⟩
  · intro x
    rw [hspeed]
    by_cases h : e x = 0
    · simp [h]
    · change (-(ρ x) / e x) * e x ∈ Icc (-1) 0
      rw [div_mul_cancel₀ _ h]
      have hb := hρbound x
      constructor <;> linarith [hb.1, hb.2]
  · intro x hx
    rw [hspeed]
    change (-(ρ x) / e x) * e x = -1
    rw [div_mul_cancel₀ _ (hsub hx)]
    rw [hρ1.self_of_nhdsSet x hx]


set_option backward.isDefEq.respectTransparency false in
/-- Chain rule along an actual manifold integral curve, with the derivative
expressed by the actual manifold differential of the scalar function. -/
theorem hasDerivAt_function_along_integralCurve {f : M → ℝ}
    (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    {v : (x : M) → TangentSpace (model n) x} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    HasDerivAt (f ∘ γ) (mvfderiv (model n) f (γ t) (v (γ t))) t := by
  have h := ((hf (γ t)).mdifferentiableAt (by simp)).hasMFDerivAt.comp t (hγ t)
  have h' : HasFDerivAt (f ∘ γ)
      ((mfderiv (model n) 𝓘(ℝ) f (γ t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))) t := h.hasFDerivAt
  change HasDerivAt (f ∘ γ) ((mfderiv (model n) 𝓘(ℝ) f (γ t)) (v (γ t))) t
  have hd : HasDerivAt (f ∘ γ)
      ((mfderiv (model n) 𝓘(ℝ) f (γ t))
        (((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t))) (1 : ℝ))) t := h'.hasDerivAt
  simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using hd

/-- Speed bounds imply uniform descent bounds along every positive-time
trajectory. This estimate controls the eventual stopping time continuously. -/
theorem integralCurve_descent_bounds {f : M → ℝ}
    (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    {v : (x : M) → TangentSpace (model n) x}
    (hspeed : ∀ x, mvfderiv (model n) f x (v x) ∈ Icc (-1) 0)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) {t : ℝ} (ht : 0 ≤ t) :
    f (γ 0) - t ≤ f (γ t) ∧ f (γ t) ≤ f (γ 0) := by
  have hd := hasDerivAt_function_along_integralCurve n M hf hγ
  have hanti := antitone_of_hasDerivAt_nonpos hd (fun s => (hspeed (γ s)).2)
  have hmono := monotone_of_hasDerivAt_nonneg
    (fun s => (hd s).add (hasDerivAt_id s))
    (fun s => by have := (hspeed (γ s)).1; dsimp; linarith)
  have hlow := hmono ht
  exact ⟨by dsimp at hlow; linarith, hanti ht⟩

/-- Before reaching the lower level, the normalized field decreases the
function exactly at unit speed. All strip-invariance estimates are proved. -/
theorem integralCurve_descent_eq {f : M → ℝ}
    (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f) {a b : ℝ}
    {v : (x : M) → TangentSpace (model n) x}
    (hspeed : ∀ x, mvfderiv (model n) f x (v x) ∈ Icc (-1) 0)
    (hunit : ∀ x, f x ∈ Icc a b → mvfderiv (model n) f x (v x) = -1)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (hstart : f (γ 0) ≤ b)
    {t : ℝ} (ht : t ∈ Icc 0 (f (γ 0) - a)) : f (γ t) = f (γ 0) - t := by
  rcases ht.1.eq_or_lt with rfl | htpos
  · simp
  have hd : ∀ s ∈ Ioo 0 t, HasDerivAt (f ∘ γ) (-1) s := by
    intro s hs
    have hb := integralCurve_descent_bounds n M hf hspeed hγ hs.1.le
    have hmem : f (γ s) ∈ Icc a b := ⟨by linarith [ht.2, hs.2, hb.1], hb.2.trans hstart⟩
    simpa [hunit (γ s) hmem] using hasDerivAt_function_along_integralCurve n M hf hγ s
  obtain ⟨s, hs, hslope⟩ := exists_hasDerivAt_eq_slope (f ∘ γ) (fun _ => -1)
    htpos (hf.continuous.comp hγ.continuous).continuousOn hd
  simp only [sub_zero, Function.comp_apply] at hslope
  have := (eq_div_iff (ne_of_gt htpos)).mp hslope
  linarith

/-- A closed band containing no critical points admits continuous descent
from its upper sublevel set to its lower sublevel set. When `a ≤ b`, the
identities below give a strong deformation retraction. The ambient formula
is explicit and fixes every lower-sublevel point for all times. -/
theorem exists_sublevel_deformation [T2Space M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f) {a b : ℝ}
    (hreg : ∀ x, f x ∈ Icc a b → mvfderiv (model n) f x ≠ 0) :
    ∃ H : M × ℝ → M, Continuous H ∧
      (∀ x, H (x, 0) = x) ∧
      (∀ x, f x ≤ b → ∀ s ∈ Icc (0 : ℝ) 1, f (H (x, s)) ≤ b) ∧
      (∀ x, f x ≤ b → f (H (x, 1)) ≤ a) ∧
      ∀ x, f x ≤ a → ∀ s, H (x, s) = x := by
  obtain ⟨v, hv, hspeed, hunit⟩ := exists_normalizedGradientCutoff n M hf hreg
  obtain ⟨Φ, hΦ, hzero, hsol, hadd⟩ := exists_continuous_globalMFlow (hv.of_le (by simp))
  let H : M × ℝ → M := fun z => Φ (z.1, z.2 * max (f z.1 - a) 0)
  have htime : Continuous (fun z : M × ℝ => z.2 * max (f z.1 - a) 0) :=
    continuous_snd.mul (((hf.continuous.comp continuous_fst).sub continuous_const).max continuous_const)
  refine ⟨H, hΦ.comp (continuous_fst.prodMk htime), ?_, ?_, ?_, ?_⟩
  · intro x
    simp [H, hzero]
  · intro x hx s hs
    have ht : 0 ≤ s * max (f x - a) 0 := mul_nonneg hs.1 (le_max_right _ _)
    have hb := integralCurve_descent_bounds n M hf hspeed (hsol x) ht
    simpa only [hzero] using hb.2.trans (by simpa only [hzero] using hx)
  · intro x hx
    by_cases hxa : f x ≤ a
    · simp only [H, max_eq_right (sub_nonpos.mpr hxa), mul_zero, hzero]
      exact hxa
    · have hax : a < f x := lt_of_not_ge hxa
      have heq := integralCurve_descent_eq n M hf hspeed hunit (hsol x)
        (by simpa only [hzero] using hx)
        (t := f x - a) (by simp only [hzero]; exact ⟨sub_nonneg.mpr hax.le, le_rfl⟩)
      simp only [H, one_mul, max_eq_left (sub_nonneg.mpr hax.le)]
      rw [heq, hzero]
      linarith
  · intro x hx s
    simp only [H, max_eq_right (sub_nonpos.mpr hx), mul_zero, hzero]

/-- The actual sublevel inclusion is a homotopy equivalence whenever the
closed interval between its levels contains no critical point. -/
theorem exists_sublevel_homotopyEquiv [T2Space M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hreg : ∀ x, f x ∈ Icc a b → mvfderiv (model n) f x ≠ 0) :
    ∃ e : ContinuousMap.HomotopyEquiv {x : M // f x ≤ a} {x : M // f x ≤ b},
      ∀ x, (e x : M) = x := by
  obtain ⟨H, hH, hzero, hstay, hend, hfix⟩ := exists_sublevel_deformation n M hf hreg
  let i : C({x : M // f x ≤ a}, {x : M // f x ≤ b}) :=
    ContinuousMap.inclusion (fun x hx => le_trans hx hab)
  let r : C({x : M // f x ≤ b}, {x : M // f x ≤ a}) := {
    toFun := fun x => ⟨H (x, 1), hend x x.2⟩
    continuous_toFun := (hH.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _ }
  have hri : r.comp i = ContinuousMap.id {x : M // f x ≤ a} := by
    ext x
    exact hfix x x.2 1
  let h : ContinuousMap.Homotopy (ContinuousMap.id {x : M // f x ≤ b}) (i.comp r) := {
    toFun := fun z => ⟨H (z.2, z.1), hstay z.2 z.2.2 z.1 z.1.2⟩
    continuous_toFun := (hH.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst))).subtype_mk _
    map_zero_left := fun x => Subtype.ext (hzero x)
    map_one_left := fun x => rfl }
  refine ⟨{
    toFun := i
    invFun := r
    left_inv := ?_
    right_inv := ⟨h.symm⟩ }, ?_⟩
  · rw [hri]
  · intro x
    rfl

end GaussBonnetChern.Morse
