import GaussBonnetChern.EuclideanStokes
import GaussBonnetChern.AtlasInvariance

/-! # Localization needed for manifold Stokes

The zero extension results below turn genuinely compactly supported local
forms into the globally smooth coordinate forms required by the proved
half-space Stokes theorem. They introduce no Stokes hypothesis.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold BigOperators

namespace GaussBonnetChern.ManifoldBoundaryStokes

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Compact support away from the edge of an open coordinate domain gives a
globally smooth extension by zero. No regularity of the original totalized
function outside the domain is required. -/
theorem contDiff_indicator_of_compact_support
    (s K : Set E) (hs : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f s)
    (hsupp : Function.support f ∩ s ⊆ K) :
    ContDiff ℝ ∞ (s.indicator f) := by
  classical
  have hsupp' : Function.support (s.indicator f) ⊆ K := by
    intro x hx
    by_cases hxs : x ∈ s
    · apply hsupp ⟨?_, hxs⟩
      simpa only [Function.mem_support, indicator_of_mem hxs] using hx
    · exact False.elim (hx (indicator_of_notMem hxs f))
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hxs : x ∈ s
  · apply (hf.contDiffAt (hs.mem_nhds hxs)).congr_of_eventuallyEq
    filter_upwards [hs.mem_nhds hxs] with y hy
    exact indicator_of_mem hy f
  · have hxK : x ∈ Kᶜ := fun h ↦ hxs (hKs h)
    apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact Function.notMem_support.mp (fun h ↦ hy (hsupp' h))

theorem hasCompactSupport_indicator_of_compact_support
    (s K : Set E) (hK : IsCompact K) (f : E → F)
    (hsupp : Function.support f ∩ s ⊆ K) : HasCompactSupport (s.indicator f) := by
  classical
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro x hx
  by_cases hxs : x ∈ s
  · apply hsupp ⟨?_, hxs⟩
    simpa only [Function.mem_support, indicator_of_mem hxs] using hx
  · exact False.elim (hx (indicator_of_notMem hxs f))

/-- On the coordinate domain, the derivative of the zero extension is the
ordinary exterior derivative of the original local form. -/
theorem extDeriv_indicator_on {k : ℕ} (s : Set E) (hs : IsOpen s)
    (α : E → ContinuousAlternatingMap ℝ E ℝ (Fin k)) (x : E) (hx : x ∈ s) :
    extDeriv (s.indicator α) x = extDeriv α x := by
  apply Filter.EventuallyEq.extDeriv_eq
  filter_upwards [hs.mem_nhds hx] with y hy
  exact indicator_of_mem hy α

theorem extDeriv_indicator_eq {k : ℕ}
    (s K : Set E) (hs : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s)
    (α : E → ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (hsupp : Function.support α ∩ s ⊆ K) :
    extDeriv (s.indicator α) = s.indicator (extDeriv α) := by
  classical
  funext x
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs, extDeriv_indicator_on s hs α x hxs]
  · rw [indicator_of_notMem hxs]
    have hxK : x ∈ Kᶜ := fun h ↦ hxs (hKs h)
    have heq : s.indicator α =ᶠ[𝓝 x] (0 : E → ContinuousAlternatingMap ℝ E ℝ (Fin k)) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      by_cases hys : y ∈ s
      · rw [indicator_of_mem hys]
        exact Function.notMem_support.mp (fun h ↦ hy (hsupp ⟨h, hys⟩))
      · exact indicator_of_notMem hys α
    rw [heq.extDeriv_eq]
    ext v
    simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]

open CoordinateStokes

/-- The local differentiated top form is integrable on its coordinate patch.
This establishes the integrability needed in the local Stokes identity. -/
theorem integrableOn_local_extDeriv {n : ℕ}
    (s K : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hs : IsOpen s)
    (hK : IsCompact K) (hKs : K ⊆ s)
    (α : EuclideanSpace ℝ (Fin (n + 1)) →
      ContinuousAlternatingMap ℝ (EuclideanSpace ℝ (Fin (n + 1))) ℝ (Fin n))
    (hα : ContDiffOn ℝ ∞ α s) (hsupp : Function.support α ∩ s ⊆ K) :
    IntegrableOn (fun x ↦ extDeriv α x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)) s := by
  classical
  let β := s.indicator α
  have hb : ContDiff ℝ ∞ β := contDiff_indicator_of_compact_support s K hs hK hKs α hα hsupp
  have hbc : HasCompactSupport β := hasCompactSupport_indicator_of_compact_support s K hK α hsupp
  have hcont : Continuous (fun x ↦ extDeriv β x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)) :=
    (ContinuousAlternatingMap.apply ℝ _ ℝ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)).continuous.comp
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ).continuous.comp
        (hb.continuous_fderiv (by simp)))
  have hc : HasCompactSupport
      (fun x ↦ extDeriv β x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)) := by
    apply hbc.mono'
    intro x hx
    by_contra hn
    exact hx (by simp [extDeriv, fderiv_of_notMem_tsupport ℝ hn,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply])
  refine (hcont.integrable_of_hasCompactSupport hc).integrableOn.congr_fun ?_ hs.measurableSet
  intro x hx
  dsimp only [β]
  rw [extDeriv_indicator_on s hs α x hx]

/-- The exact local half-space formula on an open coordinate patch. The
coefficient form needs to be smooth only on that patch, with compact support
there. All integrals are of the original form and its actual derivative. -/
theorem stokes_local_halfspace {n : ℕ}
    (s K : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hs : IsOpen s)
    (hK : IsCompact K) (hKs : K ⊆ s)
    (α : EuclideanSpace ℝ (Fin (n + 1)) →
      ContinuousAlternatingMap ℝ (EuclideanSpace ℝ (Fin (n + 1))) ℝ (Fin n))
    (hα : ContDiffOn ℝ ∞ α s) (hsupp : Function.support α ∩ s ⊆ K)
    (i : Fin (n + 1)) :
    (∫ x in {x : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ x i} ∩ s,
      extDeriv α x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)) =
      -(∫ y in {y : CoordinateSpace n | toEuclidean (n + 1) (i.insertNth 0 y) ∈ s},
        (-1 : ℝ)^i.val * α (toEuclidean (n + 1) (i.insertNth 0 y))
          (fun j ↦ EuclideanSpace.basisFun (Fin (n + 1)) ℝ (i.succAbove j))) := by
  classical
  have h := stokes_euclidean_halfspace (s.indicator α)
    (contDiff_indicator_of_compact_support s K hs hK hKs α hα hsupp)
    (hasCompactSupport_indicator_of_compact_support s K hK α hsupp) i
  rw [extDeriv_indicator_eq s K hs hK hKs α hsupp] at h
  have heval (x : EuclideanSpace ℝ (Fin (n + 1))) :
      (s.indicator (extDeriv α) x) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ) =
        s.indicator (fun x ↦ extDeriv α x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)) x := by
    by_cases hx : x ∈ s <;> simp [hx]
  simp_rw [heval] at h
  rw [setIntegral_indicator hs.measurableSet] at h
  rw [h]
  congr 1
  have hinc : Continuous (fun y : CoordinateSpace n ↦
      toEuclidean (n + 1) (i.insertNth 0 y)) :=
    (toEuclidean (n + 1)).continuous.comp (contDiff_faceInclusion i 0).continuous
  have hm : MeasurableSet {y : CoordinateSpace n |
      toEuclidean (n + 1) (i.insertNth 0 y) ∈ s} := (hs.preimage hinc).measurableSet
  rw [← integral_indicator hm]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  by_cases hy : toEuclidean (n + 1) (i.insertNth 0 y) ∈ s <;> simp [hy]

section DomainIntegration

open DifferentialForm
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

/-- The actual portion of a chart target corresponding to the integration domain. -/
def chartDomain (e : OpenPartialHomeomorph M (Model n)) (Ω : Set M) : Set (Model n) :=
  e.target ∩ e.symm ⁻¹' Ω

theorem measurableSet_chartDomain (e : OpenPartialHomeomorph M (Model n))
    (Ω : Set M) (hΩ : IsClosed Ω) : MeasurableSet (chartDomain e Ω) := by
  have heq : chartDomain e Ω = e.target \ (e.target ∩ e.symm ⁻¹' Ωᶜ) := by
    ext y
    simp [chartDomain]
  rw [heq]
  exact e.open_target.measurableSet.diff
    (e.symm.isOpen_inter_preimage hΩ.isOpen_compl).measurableSet

/-- Integrate over an actual subset of the ambient manifold by restricting
the atlas integrals. -/
def integralTopFormOn (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (Ω : Set M) (α : Form (model n) M (2 * n)) : ℝ :=
  ∑ i, ∫ y in chartDomain (a.chart i) Ω, topFormIntegrand a ρ α i y

theorem integrableOn_topFormIntegrand_chartDomain [CompactSpace M]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (Ω : Set M) (α : Form (model n) M (2 * n)) (hα : IsSmooth α) (i : Fin a.card) :
    IntegrableOn (topFormIntegrand a ρ α i) (chartDomain (a.chart i) Ω) :=
  (integrableOn_topFormIntegrand a ρ hρ α hα i).mono_set inter_subset_left

@[simp] theorem integralTopFormOn_univ
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (α : Form (model n) M (2 * n)) :
    integralTopFormOn a ρ univ α = integralTopForm a ρ α := by
  simp [integralTopFormOn, integralTopForm, chartDomain]

/-- Finite subordinate partition refinement of the actual domain integral.
All summands are proved integrable before exchanging the finite sum/integral. -/
theorem integralTopFormOn_partition_refinement [CompactSpace M]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    {ι : Type*} [Fintype ι] (τ : SmoothPartitionOfUnity ι (model n) M univ)
    (Ω : Set M) (α : Form (model n) M (2 * n)) (hα : IsSmooth α) :
    integralTopFormOn a ρ Ω α = ∑ i, ∑ j,
      ∫ y in chartDomain (a.chart i) Ω,
        (ρ i ((a.chart i).symm y) * τ j ((a.chart i).symm y)) *
          topFormCoefficient (a.chart i) α y := by
  classical
  unfold integralTopFormOn
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with y
    have hs : ∑ j, τ j ((a.chart i).symm y) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using τ.sum_eq_one (mem_univ ((a.chart i).symm y))
    simp only [topFormIntegrand, ← Finset.sum_mul, ← Finset.mul_sum, hs, mul_one]
  · intro j _
    apply IntegrableOn.mono_set (t := (a.chart i).target) _ inter_subset_left
    apply integrableOn_weighted_topFormCoefficient (a.chart i) (a.smooth i) α hα
      (fun x ↦ ρ i x * τ j x)
      ((ρ i).contMDiff.continuous.mul (τ j).contMDiff.continuous)
      (isClosed_tsupport _).isCompact
    exact (tsupport_mul_subset_left (f := fun x ↦ ρ i x)
      (g := fun x ↦ τ j x)).trans (hρ i)

theorem weighted_chartDomain_integral_eq_indicator
    (e : OpenPartialHomeomorph M (Model n)) (Ω : Set M) (hΩ : IsClosed Ω)
    (α : Form (model n) M (2 * n)) (φ : M → ℝ) :
    (∫ y in chartDomain e Ω, φ (e.symm y) * topFormCoefficient e α y) =
      ∫ y in e.target, Ω.indicator φ (e.symm y) * topFormCoefficient e α y := by
  classical
  have heq : (∫ y in e.target, Ω.indicator φ (e.symm y) * topFormCoefficient e α y) =
      ∫ y in e.target, (chartDomain e Ω).indicator
        (fun y ↦ φ (e.symm y) * topFormCoefficient e α y) y := by
    apply setIntegral_congr_fun e.open_target.measurableSet
    intro y hy
    by_cases hmem : e.symm y ∈ Ω <;> simp [chartDomain, hy, hmem]
  rw [heq, setIntegral_indicator (measurableSet_chartDomain e Ω hΩ),
    inter_eq_right.mpr (show chartDomain e Ω ⊆ e.target from inter_subset_left)]

/-- The actual integral over a closed domain changes by the positive chart
Jacobian, with the domain represented by its actual preimage in each chart. -/
theorem weighted_chartDomainIntegral_change_chart
    (e e' : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (Ω : Set M) (hΩ : IsClosed Ω) (α : Form (model n) M (2 * n)) (φ : M → ℝ)
    (hs : Function.support φ ⊆ e.source) (hs' : Function.support φ ⊆ e'.source)
    (hp : ∀ x ∈ e.source, x ∈ e'.source →
      0 < LinearMap.det (fderiv ℝ (e' ∘ e.symm) (e x)).toLinearMap) :
    (∫ y in chartDomain e Ω, φ (e.symm y) * topFormCoefficient e α y) =
      ∫ y in chartDomain e' Ω, φ (e'.symm y) * topFormCoefficient e' α y := by
  classical
  rw [weighted_chartDomain_integral_eq_indicator e Ω hΩ,
    weighted_chartDomain_integral_eq_indicator e' Ω hΩ]
  have hsub : Function.support (Ω.indicator φ) ⊆ Function.support φ := by
    intro x hx hφ
    exact hx (by simp [hφ])
  exact weighted_topFormIntegral_change_chart e e' he he' α (Ω.indicator φ)
    (hsub.trans hs) (hsub.trans hs') hp

theorem integralTopFormOn_independent [CompactSpace M]
    (a b : FiniteOrientedAtlas n M) (hab : a.Compatible b)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (τ : SmoothPartitionOfUnity (Fin b.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (hτ : τ.IsSubordinate (fun j ↦ (b.chart j).source))
    (Ω : Set M) (hΩ : IsClosed Ω) (α : Form (model n) M (2 * n)) (hα : IsSmooth α) :
    integralTopFormOn a ρ Ω α = integralTopFormOn b τ Ω α := by
  classical
  rw [integralTopFormOn_partition_refinement a ρ hρ τ Ω α hα,
    integralTopFormOn_partition_refinement b τ hτ ρ Ω α hα, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have h := weighted_chartDomainIntegral_change_chart (a.chart i) (b.chart j)
    (a.smooth i) (b.smooth j) Ω hΩ α (fun x ↦ ρ i x * τ j x)
    ((Function.support_mul_subset_left _ _).trans ((subset_tsupport _).trans (hρ i)))
    ((Function.support_mul_subset_right _ _).trans ((subset_tsupport _).trans (hτ j)))
    (hab i j)
  simpa only [mul_comm (ρ i _) (τ j _)] using h

end DomainIntegration

end GaussBonnetChern.ManifoldBoundaryStokes
