import GaussBonnetChern.MorseFlowDeformation
import GaussBonnetChern.QuadraticHandleDeformation
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Lowering a Morse critical value

The local modification is `c - ‖u‖² + ‖v‖² - μ(‖u‖² + 2‖v‖²)`.
The derivative calculation proves that a radial cutoff with derivative in
`(-1,0]` introduces no new critical point. No positivity of either block's
dimension is assumed, so the extreme Morse indices remain included.
-/

noncomputable section

open Function Set Filter MeasureTheory Bundle
open scoped Topology ContDiff Manifold

namespace GaussBonnetChern.Morse

section Quadratic

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def handleRadius (z : E × F) : ℝ := ‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2

def handleQuadratic (c : ℝ) (z : E × F) : ℝ := c - ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2

def loweredHandleQuadratic (μ : ℝ → ℝ) (c : ℝ) (z : E × F) : ℝ :=
  handleQuadratic c z - μ (handleRadius z)

def loweredHandleDerivative (d : ℝ) (z : E × F) : (E × F) →L[ℝ] ℝ :=
  ((-(2 * (1 + d))) • innerSL ℝ z.1).comp (ContinuousLinearMap.fst ℝ E F) +
    ((2 * (1 - 2 * d)) • innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ E F)

theorem hasFDerivAt_loweredHandleQuadratic {μ : ℝ → ℝ} {d c : ℝ} (z : E × F)
    (hμ : HasDerivAt μ d (handleRadius z)) :
    HasFDerivAt (loweredHandleQuadratic μ c) (loweredHandleDerivative d z) z := by
  have hu := (hasStrictFDerivAt_norm_sq z.1).hasFDerivAt.comp z
    (ContinuousLinearMap.fst ℝ E F).hasFDerivAt
  have hv := (hasStrictFDerivAt_norm_sq z.2).hasFDerivAt.comp z
    (ContinuousLinearMap.snd ℝ E F).hasFDerivAt
  have h := ((hasFDerivAt_const c z).sub hu).add hv |>.sub
    (hμ.hasFDerivAt.comp z (hu.add (hv.const_mul 2)))
  convert h using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro w
    simp [loweredHandleDerivative, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring

theorem loweredHandleDerivative_eq_zero_iff {d : ℝ} (hd : -1 < d) (hd' : d ≤ 0)
    (z : E × F) : loweredHandleDerivative d z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hu := congrArg (fun L : (E × F) →L[ℝ] ℝ => L (z.1, 0)) h
    have hv := congrArg (fun L : (E × F) →L[ℝ] ℝ => L (0, z.2)) h
    simp [loweredHandleDerivative, innerSL_apply_apply] at hu hv
    have hcu : -(2 * (1 + d)) ≠ 0 := by linarith
    have hcv : 2 * (1 - 2 * d) ≠ 0 := by linarith
    have hx : z.1 = 0 := hu.resolve_left (by linarith)
    have hy : z.2 = 0 := hv.resolve_left (by linarith)
    exact Prod.ext hx hy
  · rintro rfl
    simp [loweredHandleDerivative]

/-- The modification cannot create a new critical point in either block,
including the cases where one block has dimension zero. -/
theorem fderiv_loweredHandleQuadratic_eq_zero_iff {μ : ℝ → ℝ} {d c : ℝ}
    (z : E × F) (hμ : HasDerivAt μ d (handleRadius z)) (hd : -1 < d) (hd' : d ≤ 0) :
    fderiv ℝ (loweredHandleQuadratic μ c) z = 0 ↔ z = 0 := by
  rw [(hasFDerivAt_loweredHandleQuadratic z hμ).fderiv]
  exact loweredHandleDerivative_eq_zero_iff hd hd' z

theorem handleRadius_nonneg (z : E × F) : 0 ≤ handleRadius z := by
  unfold handleRadius
  positivity

/-- The support ellipsoid fits below the upper level used for attachment. -/
theorem handleQuadratic_le_of_radius {c ε : ℝ} {z : E × F}
    (hz : handleRadius z ≤ 2 * ε) : handleQuadratic c z ≤ c + ε := by
  dsimp [handleQuadratic, handleRadius] at *
  nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]

/-- A nonnegative modification supported in the ellipsoid leaves the upper
sublevel set exactly unchanged. -/
theorem loweredHandleQuadratic_upper_sublevel {μ : ℝ → ℝ} {c ε : ℝ}
    (hμ : ∀ r, 0 ≤ r → 0 ≤ μ r) (hsupp : ∀ r, 2 * ε ≤ r → μ r = 0) :
    {z : E × F | loweredHandleQuadratic μ c z ≤ c + ε} =
      {z : E × F | handleQuadratic c z ≤ c + ε} := by
  ext z
  constructor
  · intro hz
    by_cases hr : handleRadius z ≤ 2 * ε
    · exact handleQuadratic_le_of_radius hr
    · simpa [loweredHandleQuadratic, hsupp _ (le_of_not_ge hr)] using hz
  · intro hz
    change handleQuadratic c z ≤ c + ε at hz
    have hpos := hμ (handleRadius z) (handleRadius_nonneg z)
    dsimp [loweredHandleQuadratic]
    linarith

/-- Once the original critical point has been lowered strictly below the
lower level, the entire modified closed band is regular. -/
theorem loweredHandleQuadratic_regular_band {μ : ℝ → ℝ} {c ε : ℝ}
    (hμ : Differentiable ℝ μ) (hd : ∀ r, -1 < deriv μ r ∧ deriv μ r ≤ 0)
    (hheight : ε < μ 0) (z : E × F)
    (hz : loweredHandleQuadratic μ c z ∈ Icc (c - ε) (c + ε)) :
    fderiv ℝ (loweredHandleQuadratic μ c) z ≠ 0 := by
  intro hcrit
  have hz0 := (fderiv_loweredHandleQuadratic_eq_zero_iff z
    (hμ (handleRadius z)).hasDerivAt (hd _).1 (hd _).2).mp hcrit
  subst z
  simp only [loweredHandleQuadratic, handleQuadratic, handleRadius, Prod.fst_zero,
    Prod.snd_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
    sub_zero, add_zero] at hz
  linarith [hz.1]

end Quadratic


section Cutoff

/-- A smooth descent rate between zero and three quarters, equal to three
quarters through `3ε/2` and zero after `2ε`. -/
def handleCutoffRate (ε r : ℝ) : ℝ :=
  (3 / 4 : ℝ) * (1 - Real.smoothTransition ((r - 3 * ε / 2) / (ε / 2)))

theorem contDiff_handleCutoffRate (ε : ℝ) : ContDiff ℝ ∞ (handleCutoffRate ε) := by
  unfold handleCutoffRate
  fun_prop

theorem handleCutoffRate_bounds (ε r : ℝ) : handleCutoffRate ε r ∈ Icc 0 (3 / 4) := by
  have h₀ := Real.smoothTransition.nonneg ((r - 3 * ε / 2) / (ε / 2))
  have h₁ := Real.smoothTransition.le_one ((r - 3 * ε / 2) / (ε / 2))
  dsimp [handleCutoffRate]
  constructor <;> linarith

theorem handleCutoffRate_eq_zero {ε r : ℝ} (hε : 0 < ε) (hr : 2 * ε ≤ r) :
    handleCutoffRate ε r = 0 := by
  have h : 1 ≤ (r - 3 * ε / 2) / (ε / 2) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  simp [handleCutoffRate, Real.smoothTransition.one_of_one_le h]

theorem handleCutoffRate_eq_three_quarters {ε r : ℝ} (hε : 0 < ε) (hr : r ≤ 3 * ε / 2) :
    handleCutoffRate ε r = 3 / 4 := by
  have h : (r - 3 * ε / 2) / (ε / 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  simp [handleCutoffRate, Real.smoothTransition.zero_of_nonpos h]

/-- The actual radial lowering cutoff, defined by a smooth integral. -/
def handleCutoff (ε r : ℝ) : ℝ := ∫ t in r..(2 * ε), handleCutoffRate ε t

theorem hasDerivAt_handleCutoff (ε r : ℝ) :
    HasDerivAt (handleCutoff ε) (-handleCutoffRate ε r) r := by
  exact intervalIntegral.integral_hasDerivAt_left
    ((contDiff_handleCutoffRate ε).continuous.intervalIntegrable _ _)
    (contDiff_handleCutoffRate ε).continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    (contDiff_handleCutoffRate ε).continuous.continuousAt

theorem contDiff_handleCutoff (ε : ℝ) : ContDiff ℝ ∞ (handleCutoff ε) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun r => (hasDerivAt_handleCutoff ε r).differentiableAt, ?_⟩
  have hder : deriv (handleCutoff ε) = fun r => -handleCutoffRate ε r :=
    funext fun r => (hasDerivAt_handleCutoff ε r).deriv
  rw [hder]
  exact (contDiff_handleCutoffRate ε).neg

theorem deriv_handleCutoff_bounds (ε r : ℝ) :
    -1 < deriv (handleCutoff ε) r ∧ deriv (handleCutoff ε) r ≤ 0 := by
  rw [(hasDerivAt_handleCutoff ε r).deriv]
  have h := handleCutoffRate_bounds ε r
  constructor <;> linarith [h.1, h.2]

theorem handleCutoff_eq_zero {ε r : ℝ} (hε : 0 < ε) (hr : 2 * ε ≤ r) :
    handleCutoff ε r = 0 := by
  unfold handleCutoff
  rw [intervalIntegral.integral_symm]
  have h : (∫ t in (2 * ε)..r, handleCutoffRate ε t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro t
    intro ht
    exact handleCutoffRate_eq_zero hε ((uIoc_of_le hr ▸ ht).1.le)
  rw [h, neg_zero]

theorem handleCutoff_nonneg {ε : ℝ} (hε : 0 < ε) (r : ℝ) : 0 ≤ handleCutoff ε r := by
  by_cases hr : r ≤ 2 * ε
  · exact intervalIntegral.integral_nonneg_of_forall hr (fun t => (handleCutoffRate_bounds ε t).1)
  · rw [handleCutoff_eq_zero hε (le_of_not_ge hr)]

theorem handleCutoff_antitone (ε : ℝ) : Antitone (handleCutoff ε) :=
  antitone_of_hasDerivAt_nonpos (hasDerivAt_handleCutoff ε)
    (fun r => neg_nonpos.mpr (handleCutoffRate_bounds ε r).1)

theorem handleCutoff_zero_gt {ε : ℝ} (hε : 0 < ε) : ε < handleCutoff ε 0 := by
  have hshort : (∫ t in (0 : ℝ)..(3 * ε / 2), handleCutoffRate ε t) = 9 * ε / 8 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (3 / 4 : ℝ))]
    · simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      ring
    · intro t ht
      have hpos : (0 : ℝ) ≤ 3 * ε / 2 := by positivity
      rw [uIcc_of_le hpos] at ht
      exact handleCutoffRate_eq_three_quarters hε ht.2
  have hmono := intervalIntegral.integral_mono_interval (μ := volume) (f := handleCutoffRate ε)
    (a := 0) (b := 3 * ε / 2) (c := 0) (d := 2 * ε) le_rfl (by positivity)
    (by linarith) (Filter.Eventually.of_forall fun t => (handleCutoffRate_bounds ε t).1)
    ((contDiff_handleCutoffRate ε).continuous.intervalIntegrable _ _)
  rw [hshort] at hmono
  change ε < ∫ t in (0 : ℝ)..(2 * ε), handleCutoffRate ε t
  linarith

theorem handleCutoff_covers_lower_level {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    ε ≤ r + handleCutoff ε r := by
  have hm := monotone_of_hasDerivAt_nonneg
    (fun t => (hasDerivAt_id t).add (hasDerivAt_handleCutoff ε t))
    (fun t => by have := handleCutoffRate_bounds ε t; dsimp; linarith [this.2])
  have h := hm hr
  simp only [Pi.add_apply, id_eq, zero_add] at h
  exact (handleCutoff_zero_gt hε).le.trans h

end Cutoff

section Ellipsoid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem contDiff_handleRadius : ContDiff ℝ ∞ (handleRadius (E := E) (F := F)) := by
  exact (contDiff_fst.norm_sq ℝ).add (contDiff_const.mul (contDiff_snd.norm_sq ℝ))

theorem contDiff_handleQuadratic (c : ℝ) :
    ContDiff ℝ ∞ (handleQuadratic (E := E) (F := F) c) := by
  exact (contDiff_const.sub (contDiff_fst.norm_sq ℝ)).add (contDiff_snd.norm_sq ℝ)

def handleEllipsoid (ε : ℝ) : Set (E × F) := {z | handleRadius z ≤ 2 * ε}

theorem isCompact_handleEllipsoid [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (ε : ℝ) : IsCompact (handleEllipsoid (E := E) (F := F) ε) := by
  apply (isCompact_closedBall (0 : E × F) (Real.sqrt (2 * ε))).of_isClosed_subset
  · exact isClosed_le contDiff_handleRadius.continuous continuous_const
  · intro z hz
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    dsimp [handleEllipsoid, handleRadius] at hz
    constructor <;> apply Real.le_sqrt_of_sq_le <;>
      nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]

/-- The larger product block leaves a genuine collar around the support. -/
theorem handleEllipsoid_subset_openBlock {ε : ℝ} (hε : 0 < ε) :
    handleEllipsoid (E := E) (F := F) ε ⊆
      Metric.ball (0 : E) (2 * Real.sqrt ε) ×ˢ Metric.ball (0 : F) (2 * Real.sqrt ε) := by
  intro z hz
  have hs := Real.sq_sqrt hε.le
  have hp := Real.sqrt_pos.mpr hε
  dsimp [handleEllipsoid, handleRadius] at hz
  simp only [mem_prod, Metric.mem_ball, dist_zero_right]
  constructor <;> nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖,
    norm_nonneg z.1, norm_nonneg z.2]

end Ellipsoid

section ChartLowering

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Zero extension of the actual radial perturbation in one Morse chart. -/
def chartLowering (e : OpenPartialHomeomorph M (E × F)) (ε : ℝ) (x : M) : ℝ := by
  classical
  exact if x ∈ e.source then handleCutoff ε (handleRadius (e x)) else 0

theorem chartLowering_eq_on (e : OpenPartialHomeomorph M (E × F)) (ε : ℝ)
    {x : M} (hx : x ∈ e.source) :
    chartLowering e ε x = handleCutoff ε (handleRadius (e x)) := by
  simp [chartLowering, hx]

theorem chartLowering_nonneg (e : OpenPartialHomeomorph M (E × F))
    {ε : ℝ} (hε : 0 < ε) (x : M) : 0 ≤ chartLowering e ε x := by
  unfold chartLowering
  split_ifs
  · exact handleCutoff_nonneg hε _
  · exact le_rfl

theorem tsupport_chartLowering_subset [T2Space M]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : OpenPartialHomeomorph M (E × F)) {ε : ℝ} (hε : 0 < ε)
    (hsub : handleEllipsoid (E := E) (F := F) ε ⊆ e.target) :
    tsupport (chartLowering e ε) ⊆ e.symm '' handleEllipsoid ε := by
  apply closure_minimal
  · intro x hx
    have hs : x ∈ e.source := by
      by_contra h
      exact hx (by simp [chartLowering, h])
    refine ⟨e x, ?_, e.left_inv hs⟩
    by_contra hr
    have hr' : 2 * ε ≤ handleRadius (e x) := le_of_not_ge hr
    exact hx (by rw [chartLowering_eq_on e ε hs, handleCutoff_eq_zero hε hr'])
  · exact ((isCompact_handleEllipsoid ε).image_of_continuousOn
      (e.symm.continuousOn.mono hsub)).isClosed

theorem contMDiff_chartLowering [T2Space M]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : OpenPartialHomeomorph M (E × F)) {ε : ℝ} (hε : 0 < ε)
    (hsub : handleEllipsoid (E := E) (F := F) ε ⊆ e.target)
    (he : ContMDiffOn (model n) 𝓘(ℝ, E × F) ∞ e e.source) :
    ContMDiff (model n) 𝓘(ℝ) ∞ (chartLowering e ε) := by
  apply contMDiff_of_tsupport
  intro x hx
  obtain ⟨z, hz, rfl⟩ := tsupport_chartLowering_subset e hε hsub hx
  have hs := e.map_target (hsub hz)
  have hc := ((contDiff_handleCutoff ε).comp (contDiff_handleRadius (E := E) (F := F))).contMDiff
  apply (hc.contMDiffAt.comp _ (he.contMDiffAt (e.open_source.mem_nhds hs))).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hs] with y hy
  exact chartLowering_eq_on e ε hy

end ChartLowering

section FiniteCharts

universe u v
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M] [T2Space M]
variable {ι : Type v} [Fintype ι] {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, FiniteDimensional ℝ (F i)]

def finiteChartLowering (e : ∀ i, OpenPartialHomeomorph M (E i × F i))
    (ε : ℝ) (f : M → ℝ) (x : M) : ℝ := f x - ∑ i, chartLowering (e i) ε x

theorem contMDiff_finiteChartLowering
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) {ε : ℝ} (hε : 0 < ε)
    (hsub : ∀ i, handleEllipsoid ε ⊆ (e i).target)
    (he : ∀ i, ContMDiffOn (model n) 𝓘(ℝ, E i × F i) ∞ (e i) (e i).source)
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f) :
    ContMDiff (model n) 𝓘(ℝ) ∞ (finiteChartLowering e ε f) := by
  exact hf.sub (contMDiff_finsetSum fun i _ => contMDiff_chartLowering (e i) hε (hsub i) (he i))

theorem finiteChartLowering_le (e : ∀ i, OpenPartialHomeomorph M (E i × F i))
    {ε : ℝ} (hε : 0 < ε) (f : M → ℝ) (x : M) : finiteChartLowering e ε f x ≤ f x := by
  exact sub_le_self _ (Finset.sum_nonneg fun i _ => chartLowering_nonneg (e i) hε x)

theorem finiteChartLowering_eq_on
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) (ε : ℝ) (f : M → ℝ)
    (hdisj : Pairwise (Disjoint on fun i => (e i).source))
    {i : ι} {x : M} (hx : x ∈ (e i).source) :
    finiteChartLowering e ε f x = f x - handleCutoff ε (handleRadius (e i x)) := by
  classical
  unfold finiteChartLowering
  congr 1
  rw [Finset.sum_eq_single i]
  · exact chartLowering_eq_on (e i) ε hx
  · intro j _ hji
    have hj : x ∉ (e j).source := fun hj => Set.disjoint_left.mp (hdisj hji) hj hx
    simp [chartLowering, hj]
  · simp

theorem finiteChartLowering_eq_outside
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) (ε : ℝ) (f : M → ℝ)
    {x : M} (hx : ∀ i, x ∉ (e i).source) : finiteChartLowering e ε f x = f x := by
  simp [finiteChartLowering, chartLowering, hx]

theorem finiteChartLowering_eventuallyEq_outside
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) {ε : ℝ} (hε : 0 < ε)
    (hsub : ∀ i, handleEllipsoid ε ⊆ (e i).target) (f : M → ℝ)
    {x : M} (hx : ∀ i, x ∉ (e i).source) : finiteChartLowering e ε f =ᶠ[𝓝 x] f := by
  have hz : ∀ i, chartLowering (e i) ε =ᶠ[𝓝 x] 0 := by
    intro i
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hm
    obtain ⟨z, hz, hzx⟩ := tsupport_chartLowering_subset (e i) hε (hsub i) hm
    exact hx i (hzx ▸ (e i).map_target (hsub i hz))
  filter_upwards [Filter.eventually_all.mpr hz] with y hy
  simp [finiteChartLowering, hy]

theorem finiteChartLowering_upper_sublevel
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) {ε c : ℝ} (hε : 0 < ε)
    (f : M → ℝ) (hdisj : Pairwise (Disjoint on fun i => (e i).source))
    (hform : ∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x)) :
    {x | finiteChartLowering e ε f x ≤ c + ε} = {x | f x ≤ c + ε} := by
  ext x
  by_cases hx : ∃ i, x ∈ (e i).source
  · obtain ⟨i, hi⟩ := hx
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, finiteChartLowering_eq_on e ε f hdisj hi,
      hform i x hi]
    have h := loweredHandleQuadratic_upper_sublevel (E := E i) (F := F i)
      (c := c) (ε := ε) (μ := handleCutoff ε)
      (fun r _ => handleCutoff_nonneg hε r) (fun _ hr => handleCutoff_eq_zero hε hr)
    exact Set.ext_iff.mp h (e i x)
  · have hxi : ∀ i, x ∉ (e i).source := by simpa only [not_exists] using hx
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, finiteChartLowering_eq_outside e ε f hxi]

set_option backward.isDefEq.respectTransparency false in
theorem finiteChartLowering_regular_band
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) {ε c : ℝ} (hε : 0 < ε)
    (hsub : ∀ i, handleEllipsoid ε ⊆ (e i).target)
    (he : ∀ i, ContMDiffOn (model n) 𝓘(ℝ, E i × F i) ∞ (e i) (e i).source)
    (hei : ∀ i, ContMDiffOn 𝓘(ℝ, E i × F i) (model n) ∞ (e i).symm (e i).target)
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hdisj : Pairwise (Disjoint on fun i => (e i).source))
    (hform : ∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x))
    (hreg : ∀ x, f x ∈ Icc (c - ε) (c + ε) → (∀ i, x ∉ (e i).source) →
      mvfderiv (model n) f x ≠ 0) :
    ∀ x, finiteChartLowering e ε f x ∈ Icc (c - ε) (c + ε) →
      mvfderiv (model n) (finiteChartLowering e ε f) x ≠ 0 := by
  let g := finiteChartLowering e ε f
  have hg := contMDiff_finiteChartLowering e hε hsub he hf
  intro x hx hzero
  by_cases hs : ∃ i, x ∈ (e i).source
  · obtain ⟨i, hi⟩ := hs
    have hy := (e i).map_source hi
    have hlocal : (g ∘ (e i).symm) =ᶠ[𝓝 (e i x)] loweredHandleQuadratic (handleCutoff ε) c := by
      filter_upwards [(e i).open_target.mem_nhds hy] with z hz
      have hs := (e i).map_target hz
      simp only [Function.comp_apply, g, finiteChartLowering_eq_on e ε f hdisj hs,
        hform i _ hs, (e i).right_inv hz, loweredHandleQuadratic]
    have hd := mvfderiv_comp (e i x)
      ((hg _).mdifferentiableAt (by simp))
      (((hei i).contMDiffAt ((e i).open_target.mem_nhds hy)).mdifferentiableAt (by simp))
    rw [(e i).left_inv hi, hzero, ContinuousLinearMap.zero_comp,
      mvfderiv_eq_fderiv] at hd
    have hcrit : fderiv ℝ (loweredHandleQuadratic (handleCutoff ε) c) (e i x) = 0 := by
      rw [← hlocal.fderiv_eq]
      exact hd
    apply loweredHandleQuadratic_regular_band
      ((contDiff_handleCutoff ε).differentiable (by simp))
      (deriv_handleCutoff_bounds ε) (handleCutoff_zero_gt hε) (e i x) _ hcrit
    simpa only [g, finiteChartLowering_eq_on e ε f hdisj hi,
      hform i x hi, loweredHandleQuadratic] using hx
  · have hs' : ∀ i, x ∉ (e i).source := by simpa only [not_exists] using hs
    have heq := finiteChartLowering_eventuallyEq_outside e hε hsub f hs'
    apply hreg x (by simpa only [g, heq.self_of_nhds] using hx) hs'
    have hd := heq.mfderiv_eq (I := model n) (I' := 𝓘(ℝ))
    convert! hd.symm.trans hzero using 1 <;> ext v <;> rfl

end FiniteCharts

section ExcisionCollar

variable {X : Type*} [TopologicalSpace X]

/-- Compactly supported lowering inside the retained region supplies the
closure condition for actual relative singular-homology excision. -/
theorem closure_outside_subset_interior_oldLower
    (f δ : X → ℝ) (a : ℝ) (K : Set X) (hsupp : tsupport δ ⊆ interior K) :
    closure {x : {x : X // f x - δ x ≤ a} | x.val ∉ K} ⊆
      interior {x : {x : X // f x - δ x ≤ a} | f x.val ≤ a} := by
  let Y := {x : X // f x - δ x ≤ a}
  have hc : closure {x : Y | x.val ∉ K} ⊆ {x : Y | x.val ∉ interior K} := by
    apply closure_minimal
    · exact fun x hx hi => hx (interior_subset hi)
    · exact (isOpen_interior.preimage continuous_subtype_val).isClosed_compl
  intro x hx
  have hn : x.val ∉ tsupport δ := fun h => hc hx (hsupp h)
  have heq := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    (continuous_subtype_val.continuousAt (x := x)).tendsto
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [heq] with y hy
  have h := y.2
  change δ y.val = 0 at hy
  simpa only [hy, sub_zero] using h

end ExcisionCollar

section ChartBlocks

universe u v
variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def coordinateBlock (ε : ℝ) : Set (E × F) :=
  Metric.closedBall (0 : E) (2 * Real.sqrt ε) ×ˢ
    Metric.closedBall (0 : F) (2 * Real.sqrt ε)

def chartBlock (e : OpenPartialHomeomorph M (E × F)) (ε : ℝ) : Set M :=
  e.symm '' coordinateBlock ε

theorem isCompact_coordinateBlock (ε : ℝ) :
    IsCompact (coordinateBlock (E := E) (F := F) ε) :=
  (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)

theorem handleEllipsoid_subset_coordinateBlock {ε : ℝ} (hε : 0 < ε) :
    handleEllipsoid (E := E) (F := F) ε ⊆ coordinateBlock ε := by
  intro z hz
  have h := handleEllipsoid_subset_openBlock hε hz
  exact ⟨Metric.ball_subset_closedBall h.1, Metric.ball_subset_closedBall h.2⟩

theorem chartBlock_subset_source (e : OpenPartialHomeomorph M (E × F)) (ε : ℝ)
    (hsub : coordinateBlock ε ⊆ e.target) : chartBlock e ε ⊆ e.source := by
  rintro x ⟨z, hz, rfl⟩
  exact e.map_target (hsub hz)

theorem isCompact_chartBlock (e : OpenPartialHomeomorph M (E × F)) (ε : ℝ)
    (hsub : coordinateBlock ε ⊆ e.target) : IsCompact (chartBlock e ε) :=
  (isCompact_coordinateBlock ε).image_of_continuousOn (e.symm.continuousOn.mono hsub)

theorem tsupport_chartLowering_subset_interior
    (e : OpenPartialHomeomorph M (E × F)) {ε : ℝ} (hε : 0 < ε)
    (hsub : coordinateBlock ε ⊆ e.target) :
    tsupport (chartLowering e ε) ⊆ interior (chartBlock e ε) := by
  let B : Set (E × F) := Metric.ball (0 : E) (2 * Real.sqrt ε) ×ˢ
    Metric.ball (0 : F) (2 * Real.sqrt ε)
  have hBK : B ⊆ coordinateBlock ε :=
    fun z hz => ⟨Metric.ball_subset_closedBall hz.1, Metric.ball_subset_closedBall hz.2⟩
  have hopen : IsOpen (e.symm '' B) :=
    e.isOpen_image_symm_of_subset_target (Metric.isOpen_ball.prod Metric.isOpen_ball) (hBK.trans hsub)
  have hEl := handleEllipsoid_subset_coordinateBlock (E := E) (F := F) hε
  exact (tsupport_chartLowering_subset e hε (hEl.trans hsub)).trans
    ((image_mono (handleEllipsoid_subset_openBlock hε)).trans
      (interior_maximal (image_mono hBK) hopen))

end ChartBlocks

section FiniteBlocks

universe u v
variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable {ι : Type v} [Fintype ι] {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, FiniteDimensional ℝ (F i)]

theorem tsupport_sum_chartLowering_subset_interior
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) {ε : ℝ} (hε : 0 < ε)
    (hsub : ∀ i, coordinateBlock ε ⊆ (e i).target) :
    tsupport (fun x => ∑ i, chartLowering (e i) ε x) ⊆
      interior (⋃ i, chartBlock (e i) ε) := by
  intro x hx
  by_contra hnot
  have hn : ∀ i, x ∉ tsupport (chartLowering (e i) ε) := by
    intro i hi
    exact hnot (interior_mono (subset_iUnion (fun j => chartBlock (e j) ε) i)
      (tsupport_chartLowering_subset_interior (e i) hε (hsub i) hi))
  have hz := Filter.eventually_all.mpr (fun i => notMem_tsupport_iff_eventuallyEq.mp (hn i))
  have hzero : x ∉ tsupport (fun x => ∑ i, chartLowering (e i) ε x) := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [hz] with y hy
    simp only [Pi.zero_apply] at hy ⊢
    simp [hy]
  exact hzero hx

theorem finiteChartLowering_excision_closure
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) {ε c : ℝ} (hε : 0 < ε)
    (hsub : ∀ i, coordinateBlock ε ⊆ (e i).target) (f : M → ℝ) :
    closure {x : {x : M // finiteChartLowering e ε f x ≤ c - ε} |
      x.val ∉ ⋃ i, chartBlock (e i) ε} ⊆
    interior {x : {x : M // finiteChartLowering e ε f x ≤ c - ε} | f x.val ≤ c - ε} :=
  closure_outside_subset_interior_oldLower f (fun x => ∑ i, chartLowering (e i) ε x)
    (c - ε) (⋃ i, chartBlock (e i) ε)
    (tsupport_sum_chartLowering_subset_interior e hε hsub)

end FiniteBlocks

section LocalPair

universe u v
variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable {ι : Type v} [Fintype ι] {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, FiniteDimensional ℝ (F i)]

theorem handleQuadratic_eq_model {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ℝ) (z : U × V) : handleQuadratic c z = c + QuadraticHandle.quadratic z := by
  unfold handleQuadratic QuadraticHandle.quadratic
  ring

theorem loweredHandleQuadratic_eq_model {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : ℝ → ℝ) (c : ℝ) (z : U × V) :
    loweredHandleQuadratic μ c z = c + QuadraticHandle.modified μ z := by
  unfold loweredHandleQuadratic handleQuadratic handleRadius
    QuadraticHandle.modified QuadraticHandle.quadratic QuadraticHandle.radiusSquared
  ring

def localLowerPiece (e : ∀ i, OpenPartialHomeomorph M (E i × F i))
    (ε c : ℝ) (f : M → ℝ) (i : ι) : Set {x : M // finiteChartLowering e ε f x ≤ c - ε} :=
  {x | x.val ∈ chartBlock (e i) ε}

theorem isClosed_localLowerPiece
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) (ε c : ℝ) (f : M → ℝ)
    (hsub : ∀ i, coordinateBlock ε ⊆ (e i).target) (i : ι) :
    IsClosed (localLowerPiece e ε c f i) :=
  (isCompact_chartBlock (e i) ε (hsub i)).isClosed.preimage continuous_subtype_val

theorem pairwise_disjoint_localLowerPiece
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) (ε c : ℝ) (f : M → ℝ)
    (hsub : ∀ i, coordinateBlock ε ⊆ (e i).target)
    (hdisj : Pairwise (Disjoint on fun i => (e i).source)) :
    Pairwise (Disjoint on localLowerPiece e ε c f) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact Set.disjoint_left.mp (hdisj hij)
    (chartBlock_subset_source (e i) ε (hsub i) hi)
    (chartBlock_subset_source (e j) ε (hsub j) hj)

theorem mem_chartBlock_iff (e : OpenPartialHomeomorph M (E i × F i)) (ε : ℝ)
    (hsub : coordinateBlock ε ⊆ e.target) (x : M) :
    x ∈ chartBlock e ε ↔ x ∈ e.source ∧ e x ∈ coordinateBlock ε := by
  rw [chartBlock, e.symm_image_eq_source_inter_preimage hsub]
  rfl

theorem chart_mem_localBlock
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) (ε c : ℝ) (f : M → ℝ)
    (hsub : ∀ i, coordinateBlock ε ⊆ (e i).target)
    (hdisj : Pairwise (Disjoint on fun i => (e i).source))
    (hform : ∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x))
    {i : ι} (x : localLowerPiece e ε c f i) :
    e i x.val.val ∈ QuadraticHandle.lowerBlock (handleCutoff ε) ε (2 * Real.sqrt ε) (2 * Real.sqrt ε) := by
  have hx := (mem_chartBlock_iff (e i) ε (hsub i) x.val.val).mp x.2
  have hlev := x.val.2
  rw [finiteChartLowering_eq_on e ε f hdisj hx.1, hform i _ hx.1] at hlev
  change loweredHandleQuadratic (handleCutoff ε) c (e i x.val.val) ≤ c - ε at hlev
  rw [loweredHandleQuadratic_eq_model] at hlev
  have hc := hx.2
  simp only [coordinateBlock, mem_prod, Metric.mem_closedBall, dist_zero_right] at hc
  exact ⟨hc.1, hc.2, by linarith⟩

theorem inverseChart_mem_localPiece
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) (ε c : ℝ) (f : M → ℝ)
    (hsub : ∀ i, coordinateBlock ε ⊆ (e i).target)
    (hdisj : Pairwise (Disjoint on fun i => (e i).source))
    (hform : ∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x))
    {i : ι} (z : QuadraticHandle.lowerBlock (U := E i) (V := F i)
      (handleCutoff ε) ε (2 * Real.sqrt ε) (2 * Real.sqrt ε)) :
    finiteChartLowering e ε f ((e i).symm z) ≤ c - ε ∧
      (e i).symm z ∈ chartBlock (e i) ε := by
  have hc : z.val ∈ coordinateBlock ε := by
    simpa only [coordinateBlock, mem_prod, Metric.mem_closedBall, dist_zero_right] using
      And.intro z.2.1 z.2.2.1
  have ht := hsub i hc
  have hs := (e i).map_target ht
  refine ⟨?_, ⟨z.val, hc, rfl⟩⟩
  rw [finiteChartLowering_eq_on e ε f hdisj hs, hform i _ hs, (e i).right_inv ht]
  change loweredHandleQuadratic (handleCutoff ε) c z.val ≤ c - ε
  rw [loweredHandleQuadratic_eq_model]
  linarith [z.2.2.2]

/-- Each retained piece of the actual global modified sublevel is genuinely
homeomorphic to its explicit quadratic lower block. -/
def localLowerPieceHomeomorph
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) (ε c : ℝ) (f : M → ℝ)
    (hsub : ∀ i, coordinateBlock ε ⊆ (e i).target)
    (hdisj : Pairwise (Disjoint on fun i => (e i).source))
    (hform : ∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x)) (i : ι) :
    localLowerPiece e ε c f i ≃ₜ QuadraticHandle.lowerBlock (U := E i) (V := F i)
      (handleCutoff ε) ε (2 * Real.sqrt ε) (2 * Real.sqrt ε) where
  toFun x := ⟨e i x.val.val, chart_mem_localBlock e ε c f hsub hdisj hform x⟩
  invFun z := ⟨⟨(e i).symm z, (inverseChart_mem_localPiece e ε c f hsub hdisj hform z).1⟩,
    (inverseChart_mem_localPiece e ε c f hsub hdisj hform z).2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (e i).left_inv ((mem_chartBlock_iff (e i) ε (hsub i) _).mp x.2).1
  right_inv z := by
    apply Subtype.ext
    apply (e i).right_inv
    apply hsub i
    simpa only [coordinateBlock, mem_prod, Metric.mem_closedBall, dist_zero_right] using
      And.intro z.2.1 z.2.2.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (e i).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
    intro x
    exact ((mem_chartBlock_iff (e i) ε (hsub i) _).mp x.2).1
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply (e i).symm.continuousOn.comp_continuous continuous_subtype_val
    intro z
    apply hsub i
    simpa only [coordinateBlock, mem_prod, Metric.mem_closedBall, dist_zero_right] using
      And.intro z.2.1 z.2.2.1

theorem localLowerPieceHomeomorph_oldLower
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) (ε c : ℝ) (f : M → ℝ)
    (hsub : ∀ i, coordinateBlock ε ⊆ (e i).target)
    (hdisj : Pairwise (Disjoint on fun i => (e i).source))
    (hform : ∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x))
    (i : ι) (x : localLowerPiece e ε c f i) :
    localLowerPieceHomeomorph e ε c f hsub hdisj hform i x ∈
      QuadraticHandle.lowerAttaching (handleCutoff ε) ε (2 * Real.sqrt ε) (2 * Real.sqrt ε) ↔
    f x.val.val ≤ c - ε := by
  have hs := ((mem_chartBlock_iff (e i) ε (hsub i) _).mp x.2).1
  rw [hform i _ hs, handleQuadratic_eq_model]
  change QuadraticHandle.quadratic (e i x.val.val) ≤ -ε ↔
    c + QuadraticHandle.quadratic (e i x.val.val) ≤ c - ε
  constructor <;> intro h <;> linarith

end LocalPair

section CriticalLevelFlow

universe u v
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]
variable {ι : Type v} [Fintype ι] {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, FiniteDimensional ℝ (F i)]

/-- Actual descent from the original upper sublevel to the modified lower
sublevel, fixing every point of the original lower sublevel for all times. -/
theorem exists_criticalLevel_deformation
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) {ε c : ℝ} (hε : 0 < ε)
    (hsub : ∀ i, handleEllipsoid ε ⊆ (e i).target)
    (he : ∀ i, ContMDiffOn (model n) 𝓘(ℝ, E i × F i) ∞ (e i) (e i).source)
    (hei : ∀ i, ContMDiffOn 𝓘(ℝ, E i × F i) (model n) ∞ (e i).symm (e i).target)
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hdisj : Pairwise (Disjoint on fun i => (e i).source))
    (hform : ∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x))
    (hreg : ∀ x, f x ∈ Icc (c - ε) (c + ε) → (∀ i, x ∉ (e i).source) →
      mvfderiv (model n) f x ≠ 0) :
    ∃ H : M × ℝ → M, Continuous H ∧
      (∀ x, H (x, 0) = x) ∧
      (∀ x, f x ≤ c + ε → ∀ s ∈ Icc (0 : ℝ) 1, f (H (x, s)) ≤ c + ε) ∧
      (∀ x, f x ≤ c + ε → finiteChartLowering e ε f (H (x, 1)) ≤ c - ε) ∧
      ∀ x, f x ≤ c - ε → ∀ s, H (x, s) = x := by
  have hg := contMDiff_finiteChartLowering e hε hsub he hf
  have hr := finiteChartLowering_regular_band e hε hsub he hei hf hdisj hform hreg
  obtain ⟨H, hH, hzero, hstay, hend, hfix⟩ := exists_sublevel_deformation n M hg hr
  have hu := finiteChartLowering_upper_sublevel e hε f hdisj hform
  have hu' (x : M) : finiteChartLowering e ε f x ≤ c + ε ↔ f x ≤ c + ε :=
    Set.ext_iff.mp hu x
  refine ⟨H, hH, hzero, ?_, ?_, ?_⟩
  · intro x hx s hs
    exact (hu' _).mp (hstay x ((hu' x).mpr hx) s hs)
  · intro x hx
    exact hend x ((hu' x).mpr hx)
  · intro x hx s
    exact hfix x ((finiteChartLowering_le e hε f x).trans hx) s

/-- The forward map is exactly the actual inclusion into the original upper
sublevel, so it is compatible with the original lower-sublevel pair. -/
theorem exists_criticalLevel_homotopyEquiv
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) {ε c : ℝ} (hε : 0 < ε)
    (hsub : ∀ i, handleEllipsoid ε ⊆ (e i).target)
    (he : ∀ i, ContMDiffOn (model n) 𝓘(ℝ, E i × F i) ∞ (e i) (e i).source)
    (hei : ∀ i, ContMDiffOn 𝓘(ℝ, E i × F i) (model n) ∞ (e i).symm (e i).target)
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hdisj : Pairwise (Disjoint on fun i => (e i).source))
    (hform : ∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x))
    (hreg : ∀ x, f x ∈ Icc (c - ε) (c + ε) → (∀ i, x ∉ (e i).source) →
      mvfderiv (model n) f x ≠ 0) :
    ∃ h : ContinuousMap.HomotopyEquiv {x : M // finiteChartLowering e ε f x ≤ c - ε}
      {x : M // f x ≤ c + ε}, ∀ x, (h x : M) = x := by
  have hg := contMDiff_finiteChartLowering e hε hsub he hf
  have hr := finiteChartLowering_regular_band e hε hsub he hei hf hdisj hform hreg
  obtain ⟨h, hh⟩ := exists_sublevel_homotopyEquiv n M hg (by linarith : c - ε ≤ c + ε) hr
  let k := Homeomorph.setCongr (finiteChartLowering_upper_sublevel e hε f hdisj hform)
  refine ⟨h.trans k.toHomotopyEquiv, ?_⟩
  intro x
  exact hh x

end CriticalLevelFlow

end GaussBonnetChern.Morse
