import GaussBonnetChern.ManifoldBoundaryStokes
import GaussBonnetChern.ExteriorSmoothLinear

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology BigOperators
namespace GaussBonnetChern.StokesLocalization
open DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

/-- Local smoothness of the actual form in every smooth chart through a point.
This permits totalized forms that are smooth only off a finite zero set. -/
def IsSmoothAtInCharts (α : Form 𝓘(ℝ, E) M k) (x : M) : Prop :=
  ∀ e : OpenPartialHomeomorph M E,
    e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M → x ∈ e.source →
      ContDiffAt ℝ ∞ (chartRepresentation e α) (e x)

theorem isSmoothAtInCharts_of_isSmooth
    (α : Form 𝓘(ℝ, E) M k) (hα : IsSmooth α) (x : M) : IsSmoothAtInCharts α x := by
  intro e he hx
  exact (hα e he).contDiffAt (e.open_target.mem_nhds (e.map_source hx))

theorem isSmooth_of_isSmoothAtInCharts
    (α : Form 𝓘(ℝ, E) M k) (hα : ∀ x, IsSmoothAtInCharts α x) : IsSmooth α := by
  intro e he y hy
  have h := hα (e.symm y) e he (e.map_target hy)
  rw [e.right_inv hy] at h
  exact h.contDiffWithinAt

def weightForm (f : M → ℝ) (α : Form 𝓘(ℝ, E) M k) : Form 𝓘(ℝ, E) M k :=
  fun x ↦ f x • α x

theorem chartRepresentation_weightForm (e : OpenPartialHomeomorph M E)
    (f : M → ℝ) (α : Form 𝓘(ℝ, E) M k) (y : E) :
    chartRepresentation e (weightForm f α) y = f (e.symm y) • chartRepresentation e α y := by
  ext v
  rfl

theorem isSmooth_weightForm (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (α : Form 𝓘(ℝ, E) M k) (hα : IsSmooth α) : IsSmooth (weightForm f α) := by
  intro e he y hy
  have hfc := (hf (e.symm y)).comp y (contMDiffAt_symm_of_mem_maximalAtlas he hy)
  have hac := (hα e he).contDiffAt (e.open_target.mem_nhds hy)
  have heq : chartRepresentation e (weightForm f α) =
      fun y ↦ f (e.symm y) • chartRepresentation e α y := by
    funext y
    exact chartRepresentation_weightForm e f α y
  rw [heq]
  exact (hfc.contDiffAt.smul hac).contDiffWithinAt

/-- A scalar cutoff supported inside the actual smooth locus produces a
globally smooth form. No global smooth extension of the original form is assumed. -/
theorem isSmooth_weightForm_of_smooth_on_tsupport
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (α : Form 𝓘(ℝ, E) M k) (hα : ∀ x ∈ tsupport f, IsSmoothAtInCharts α x) :
    IsSmooth (weightForm f α) := by
  intro e he y hy
  have heq : chartRepresentation e (weightForm f α) =
      fun y ↦ f (e.symm y) • chartRepresentation e α y := by
    funext y
    exact chartRepresentation_weightForm e f α y
  by_cases hx : e.symm y ∈ tsupport f
  · have hfc := (hf (e.symm y)).comp y (contMDiffAt_symm_of_mem_maximalAtlas he hy)
    have hac := hα (e.symm y) hx e he (e.map_target hy)
    rw [e.right_inv hy] at hac
    rw [heq]
    exact (hfc.contDiffAt.smul hac).contDiffWithinAt
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    have hzero : chartRepresentation e (weightForm f α) =ᶠ[𝓝 y]
        (0 : E → ContinuousAlternatingMap ℝ E ℝ (Fin k)) := by
      filter_upwards [(e.continuousAt_symm hy) hz] with z hz
      rw [chartRepresentation_weightForm, hz]
      exact zero_smul ℝ _
    exact (contDiffAt_const.congr_of_eventuallyEq hzero).contDiffWithinAt

theorem sum_weightForm_eq {ι : Type*} [Fintype ι] (ρ : ι → M → ℝ)
    (hρ : ∀ x, ∑ i, ρ i x = 1) (α : Form 𝓘(ℝ, E) M k) :
    (∑ i, weightForm (ρ i) α) = α := by
  classical
  funext x
  simp only [Finset.sum_apply, weightForm, ← Finset.sum_smul, hρ x, one_smul]

theorem sum_exteriorDerivative_weightForm {ι : Type*} [Fintype ι] (ρ : ι → M → ℝ)
    (hρ : ∀ x, ∑ i, ρ i x = 1) (hs : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (ρ i))
    (α : Form 𝓘(ℝ, E) M k) (hα : IsSmooth α) :
    (∑ i, exteriorDerivative (weightForm (ρ i) α)) = exteriorDerivative α := by
  rw [← exteriorDerivative_sum Finset.univ (fun i ↦ weightForm (ρ i) α)
    (fun i _ ↦ isSmooth_weightForm (ρ i) (hs i) α hα), sum_weightForm_eq ρ hρ α]

/-- The genuine globally defined exterior derivative depends only on the
local form germ. Neither form is assumed smooth away from this neighborhood. -/
theorem exteriorDerivative_eq_of_eventually
    (α β : Form 𝓘(ℝ, E) M k) (x : M) (hx : ∀ᶠ y in 𝓝 x, α y = β y) :
    exteriorDerivative α x = exteriorDerivative β x := by
  let e := chartAt E x
  have hxs : x ∈ e.source := mem_chart_source E x
  have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    have h := e.continuousAt_symm (e.map_source hxs)
    change Tendsto e.symm (𝓝 (e x)) (𝓝 (e.symm (e x))) at h
    rwa [e.left_inv hxs] at h
  have hz : chartRepresentation e α =ᶠ[𝓝 (e x)] chartRepresentation e β := by
    filter_upwards [ht hx] with y hy
    rw [chartRepresentation_eq, chartRepresentation_eq, hy]
  change (extDeriv (chartRepresentation e α) (e x)).compContinuousLinearMap (chartTangentMap e x) =
    (extDeriv (chartRepresentation e β) (e x)).compContinuousLinearMap (chartTangentMap e x)
  rw [hz.extDeriv_eq]

theorem exteriorDerivative_eq_zero_of_eventually
    (α : Form 𝓘(ℝ, E) M k) (x : M) (hx : ∀ᶠ y in 𝓝 x, α y = 0) :
    exteriorDerivative α x = 0 := by
  let e := chartAt E x
  have hxs : x ∈ e.source := mem_chart_source E x
  have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    have h := e.continuousAt_symm (e.map_source hxs)
    change Tendsto e.symm (𝓝 (e x)) (𝓝 (e.symm (e x))) at h
    rwa [e.left_inv hxs] at h
  have hz : chartRepresentation e α =ᶠ[𝓝 (e x)]
      (0 : E → ContinuousAlternatingMap ℝ E ℝ (Fin k)) := by
    filter_upwards [ht hx] with y hy
    rw [chartRepresentation_eq, hy]
    rfl
  have hd : extDeriv (chartRepresentation e α) (e x) = 0 := by
    rw [hz.extDeriv_eq]
    ext v
    simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  change (extDeriv (chartRepresentation e α) (e x)).compContinuousLinearMap (chartTangentMap e x) = 0
  rw [hd]
  rfl

theorem exteriorDerivative_weightForm_eq_zero_of_notMem_tsupport
    (f : M → ℝ) (α : Form 𝓘(ℝ, E) M k) (x : M) (hx : x ∉ tsupport f) :
    exteriorDerivative (weightForm f α) x = 0 := by
  apply exteriorDerivative_eq_zero_of_eventually
  have hf := notMem_tsupport_iff_eventuallyEq.mp hx
  filter_upwards [hf] with y hy
  simp [weightForm, hy]

/-- Local smoothness on an open neighborhood of a closed domain is enough
for Stokes: a genuine smooth cutoff constructs a globally smooth form with
the same germ (and hence the same exterior derivative) along that domain. -/
theorem exists_global_smooth_form_eq_near_closed_domain
    [FiniteDimensional ℝ E] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    (Ω U : Set M) (hΩ : IsClosed Ω) (hU : IsOpen U) (hΩU : Ω ⊆ U)
    (α : Form 𝓘(ℝ, E) M k) (hα : ∀ x ∈ U, IsSmoothAtInCharts α x) :
    ∃ β : Form 𝓘(ℝ, E) M k, IsSmooth β ∧
      (∀ x ∈ Ω, ∀ᶠ y in 𝓝 x, β y = α y) ∧
      (∀ x ∈ Ω, exteriorDerivative β x = exteriorDerivative α x) := by
  have hd : Disjoint Uᶜ Ω := Set.disjoint_left.mpr (fun x hx hxΩ ↦ hx (hΩU hxΩ))
  obtain ⟨f, hf0, hf1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, E) hU.isClosed_compl hΩ hd (n := (⊤ : ℕ∞))
  have hfs : tsupport (f : M → ℝ) ⊆ U := by
    intro x hx
    by_contra hxU
    have hz : ∀ᶠ y in 𝓝 x, f y = 0 :=
      (eventually_nhdsSet_iff_forall.mp hf0) x hxU
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx
  have hb : IsSmooth (weightForm f α) :=
    isSmooth_weightForm_of_smooth_on_tsupport f f.contMDiff α (fun x hx ↦ hα x (hfs hx))
  have heq (x : M) (hx : x ∈ Ω) : ∀ᶠ y in 𝓝 x, weightForm f α y = α y := by
    filter_upwards [(eventually_nhdsSet_iff_forall.mp hf1) x hx] with y hy
    simp only [weightForm, hy, one_smul]
  exact ⟨weightForm f α, hb, heq,
    fun x hx ↦ exteriorDerivative_eq_of_eventually _ _ x (heq x hx)⟩

end GaussBonnetChern.StokesLocalization


noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff
namespace GaussBonnetChern.StokesLocalization
open DifferentialForm
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

theorem topFormCoefficient_eq_zero (e : OpenPartialHomeomorph M (Model n))
    (α : Form (model n) M (2*n)) (y : Model n) (h : α (e.symm y) = 0) :
    topFormCoefficient e α y = 0 := by
  rw [topFormCoefficient, chartRepresentation_eq, h]
  rfl

/-- A compact set supporting the actual form is enough for every continuous
weighted coefficient to be integrable in a chart containing that compact set. -/
theorem integrableOn_coefficient_of_compact_support
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (α : Form (model n) M (2*n)) (hα : IsSmooth α)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hαK : ∀ x, x ∉ K → α x = 0) (φ : M → ℝ) (hφ : Continuous φ) :
    IntegrableOn (fun y ↦ φ (e.symm y) * topFormCoefficient e α y) e.target := by
  let T := e '' K
  have hT : IsCompact T := hK.image_of_continuousOn (e.continuousOn.mono hKs)
  have hTt : T ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hKs hx)
  have hc : ContinuousOn (fun y ↦ φ (e.symm y) * topFormCoefficient e α y) e.target :=
    (hφ.comp_continuousOn e.continuousOn_symm).mul
      (contDiffOn_topFormCoefficient e he α hα).continuousOn
  apply ((hc.mono hTt).integrableOn_compact hT).of_forall_sdiff_eq_zero e.open_target.measurableSet
  intro y hy
  have hz : α (e.symm y) = 0 := hαK (e.symm y) (fun hx ↦ hy.2 ⟨e.symm y, hx, e.right_inv hy.1⟩)
  rw [topFormCoefficient_eq_zero e α y hz, mul_zero]

open ManifoldBoundaryStokes

/-- A form supported in a single positively oriented chart has exactly the
corresponding single-chart domain integral. This is the localization step
needed before applying the proved coordinate Stokes formula. -/
theorem integralTopFormOn_eq_single_chart [CompactSpace M]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (hp : ∀ i (x : M), x ∈ (a.chart i).source → x ∈ e.source →
      0 < LinearMap.det (fderiv ℝ (e ∘ (a.chart i).symm) ((a.chart i) x)).toLinearMap)
    (Ω : Set M) (hΩ : IsClosed Ω)
    (α : Form (model n) M (2*n)) (hα : IsSmooth α)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hαK : ∀ x, x ∉ K → α x = 0) :
    integralTopFormOn a ρ Ω α =
      ∫ y in chartDomain e Ω, topFormCoefficient e α y := by
  classical
  have hsum : integralTopFormOn a ρ Ω α =
      ∑ i, ∫ y in chartDomain e Ω, ρ i (e.symm y) * topFormCoefficient e α y := by
    unfold integralTopFormOn
    apply Finset.sum_congr rfl
    intro i _
    let φ : M → ℝ := e.source.indicator (ρ i)
    have hsφ : Function.support φ ⊆ (a.chart i).source := by
      intro x hx
      by_cases hxe : x ∈ e.source
      · apply hρ i
        apply subset_tsupport (ρ i)
        change φ x ≠ 0 at hx
        change ρ i x ≠ 0
        simpa only [φ, indicator_of_mem hxe] using hx
      · exact False.elim (hx (indicator_of_notMem hxe (ρ i)))
    have heφ : Function.support φ ⊆ e.source := by
      intro x hx
      by_contra hxe
      exact hx (indicator_of_notMem hxe (ρ i))
    have hleft : (∫ y in chartDomain (a.chart i) Ω, topFormIntegrand a ρ α i y) =
        ∫ y in chartDomain (a.chart i) Ω,
          φ ((a.chart i).symm y) * topFormCoefficient (a.chart i) α y := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      by_cases hxe : (a.chart i).symm y ∈ e.source
      · simp [topFormIntegrand, φ, hxe]
      · have hz : α ((a.chart i).symm y) = 0 :=
          hαK _ (fun hxK ↦ hxe (hKs hxK))
        rw [topFormIntegrand, topFormCoefficient_eq_zero (a.chart i) α y hz]
        simp [φ, hxe]
    rw [hleft, weighted_chartDomainIntegral_change_chart (a.chart i) e
      (a.smooth i) he Ω hΩ α φ hsφ heφ (hp i)]
    apply setIntegral_congr_fun (measurableSet_chartDomain e Ω hΩ)
    intro y hy
    simp only [φ, indicator_of_mem (e.map_target hy.1)]
  rw [hsum, ← integral_finsetSum]
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    have h1 : ∑ i, ρ i (e.symm y) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ (e.symm y))
    change (∑ i, ρ i (e.symm y) * topFormCoefficient e α y) = topFormCoefficient e α y
    rw [← Finset.sum_mul, h1, one_mul]
  · intro i _
    exact (integrableOn_coefficient_of_compact_support e he α hα K hK hKs hαK
      (ρ i) (ρ i).contMDiff.continuous).mono_set inter_subset_left

end GaussBonnetChern.StokesLocalization
