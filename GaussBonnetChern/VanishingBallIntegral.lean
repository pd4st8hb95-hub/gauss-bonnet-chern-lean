import GaussBonnetChern.EulerIntegral
import GaussBonnetChern.ManifoldBoundaryStokes
import GaussBonnetChern.PuncturedManifold
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Vanishing integrals over shrinking coordinate balls

The convergence statements use the actual chart integrands and actual removed
domains. Integrability is supplied by the geometric construction, and the
exceptional centers are removed using singleton-nullity of positive-dimensional
Lebesgue measure.
-/

noncomputable section
open Bundle MeasureTheory Set Filter Metric
open scoped Topology Manifold ContDiff BigOperators

namespace GaussBonnetChern

theorem tendsto_integral_ball_zero
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [NullSingletonClass μ]
    {f : E → ℝ} (hf : Integrable f μ) (c : E) :
    Tendsto (fun r : ℝ ↦ ∫ y in ball c r, f y ∂μ) (𝓝 0) (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝 (0 : ℝ)) (F := fun r ↦ (ball c r).indicator f)
    (f := fun _ ↦ (0 : ℝ)) (fun y ↦ ‖f y‖)
    (Eventually.of_forall fun r ↦ hf.aestronglyMeasurable.indicator measurableSet_ball)
    (Eventually.of_forall fun r ↦ Eventually.of_forall fun y ↦ by
      by_cases hy : y ∈ ball c r <;> simp [hy]) hf.norm ?_
  · simpa only [integral_indicator measurableSet_ball, integral_zero] using h
  · filter_upwards [μ.ae_ne c] with y hy
    apply tendsto_const_nhds.congr'
    filter_upwards [gt_mem_nhds (dist_pos.mpr hy)] with r hr
    exact (indicator_of_notMem (show y ∉ ball c r from not_lt.mpr hr.le) f).symm

theorem tendsto_integral_inter_ball_zero
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [NullSingletonClass μ]
    {f : E → ℝ} {s : Set E} (hf : IntegrableOn f s μ) (c : E) :
    Tendsto (fun r : ℝ ↦ ∫ y in s ∩ ball c r, f y ∂μ) (𝓝 0) (𝓝 0) := by
  simpa only [Measure.restrict_restrict measurableSet_ball, inter_comm] using
    tendsto_integral_ball_zero (μ := μ.restrict s) hf c

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

open DifferentialForm

theorem tendsto_topFormIntegrand_ball_zero [CompactSpace M]
    (hn : 0 < n) (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (α : Form (model n) M (2 * n)) (hα : IsSmooth α) (i : Fin a.card)
    (c : Model n) :
    Tendsto (fun r : ℝ ↦ ∫ y in (a.chart i).target ∩ ball c r,
      topFormIntegrand a ρ α i y) (𝓝 0) (𝓝 0) := by
  letI : Nonempty (Fin (2 * n)) := Fin.pos_iff_nonempty.mp (by omega)
  exact tendsto_integral_inter_ball_zero (integrableOn_topFormIntegrand a ρ hρ α hα i) c


open ManifoldBoundaryStokes PuncturedManifold

theorem eventually_not_mem_coordinateBall
    (g e : OpenPartialHomeomorph M (Model n)) (c y : Model n)
    (hy : y ∈ g.target) (hne : y ≠ g (e.symm c)) :
    ∀ᶠ r : ℝ in 𝓝 0, g.symm y ∉ coordinateBall e c r := by
  by_cases hx : g.symm y ∈ e.source
  · have hd : 0 < dist (e (g.symm y)) c := by
      apply dist_pos.mpr
      intro heq
      apply hne
      have hpoint : g.symm y = e.symm c := by
        rw [← heq, e.left_inv hx]
      calc
        y = g (g.symm y) := (g.right_inv hy).symm
        _ = g (e.symm c) := congrArg g hpoint
    filter_upwards [gt_mem_nhds hd] with r hr
    intro hmem
    exact (not_lt_of_ge hr.le) hmem.2
  · exact Eventually.of_forall (fun r hmem ↦ hx hmem.1)

theorem measurableSet_chartDomain_removedBalls {ι : Type*}
    (g : OpenPartialHomeomorph M (Model n))
    (e : ι → OpenPartialHomeomorph M (Model n)) (c : ι → Model n) (r : ι → ℝ) :
    MeasurableSet (chartDomain g (⋃ i, coordinateBall (e i) (c i) (r i))) :=
  (g.symm.isOpen_inter_preimage (isOpen_iUnion fun i ↦ isOpen_coordinateBall (e i) (c i) (r i))).measurableSet

/-- Almost every coordinate point eventually avoids a finite family of
shrinking coordinate balls, including when the ball charts and integration
chart differ. The only exceptions are an explicitly finite set of centers. -/
theorem ae_eventually_not_mem_removedBalls
    (hn : 0 < n) {ι T : Type*} [Fintype ι] {l : Filter T}
    (g : OpenPartialHomeomorph M (Model n))
    (e : ι → OpenPartialHomeomorph M (Model n)) (c : ι → Model n)
    (r : ι → T → ℝ) (hr : ∀ i, Tendsto (r i) l (𝓝 0)) :
    ∀ᵐ y ∂(volume.restrict g.target), ∀ᶠ t in l,
      y ∉ chartDomain g (⋃ i, coordinateBall (e i) (c i) (r i t)) := by
  letI : Nonempty (Fin (2 * n)) := Fin.pos_iff_nonempty.mp (by omega)
  have hex : ∀ᵐ y ∂(volume.restrict g.target),
      y ∉ Set.range (fun i ↦ g ((e i).symm (c i))) :=
    (Set.finite_range (fun i ↦ g ((e i).symm (c i)))).countable.ae_notMem _
  filter_upwards [hex, ae_restrict_mem g.open_target.measurableSet] with y hy hyt
  have hav (i : ι) : ∀ᶠ t in l,
      g.symm y ∉ coordinateBall (e i) (c i) (r i t) := by
    have hi := eventually_not_mem_coordinateBall g (e i) (c i) y hyt
      (fun h ↦ hy ⟨i, h.symm⟩)
    exact (hr i).eventually hi
  filter_upwards [eventually_all.mpr hav] with t ht
  intro hmem
  obtain ⟨i, hi⟩ := mem_iUnion.mp hmem.2
  exact ht i hi

theorem tendsto_chartDomain_removedBalls_integral_zero
    (hn : 0 < n) {ι T : Type*} [Fintype ι] {l : Filter T} [l.IsCountablyGenerated]
    (g : OpenPartialHomeomorph M (Model n))
    (e : ι → OpenPartialHomeomorph M (Model n)) (c : ι → Model n)
    (r : ι → T → ℝ) (hr : ∀ i, Tendsto (r i) l (𝓝 0))
    (f : Model n → ℝ) (hf : IntegrableOn f g.target) :
    Tendsto (fun t ↦ ∫ y in chartDomain g (⋃ i, coordinateBall (e i) (c i) (r i t)),
      f y) l (𝓝 0) := by
  let S := fun t ↦ chartDomain g (⋃ i, coordinateBall (e i) (c i) (r i t))
  have hS (t : T) : MeasurableSet (S t) := measurableSet_chartDomain_removedBalls g e c (fun i ↦ r i t)
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict g.target) (l := l) (F := fun t ↦ (S t).indicator f)
    (f := fun _ ↦ (0 : ℝ)) (fun y ↦ ‖f y‖)
    (Eventually.of_forall fun t ↦ hf.aestronglyMeasurable.indicator (hS t))
    (Eventually.of_forall fun t ↦ Eventually.of_forall fun y ↦ by
      by_cases hy : y ∈ S t <;> simp [hy]) hf.norm ?_
  · have hsub (t : T) : S t ∩ g.target = S t := inter_eq_left.mpr inter_subset_left
    simpa only [integral_indicator (hS _), Measure.restrict_restrict (hS _), hsub,
      integral_zero] using h
  · filter_upwards [ae_eventually_not_mem_removedBalls hn g e c r hr] with y hy
    apply tendsto_const_nhds.congr'
    filter_upwards [hy] with t ht
    exact (indicator_of_notMem ht f).symm

theorem tendsto_integralTopFormOn_removedBalls_zero [CompactSpace M]
    (hn : 0 < n) {ι T : Type*} [Fintype ι] {l : Filter T} [l.IsCountablyGenerated]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (α : Form (model n) M (2 * n)) (hα : IsSmooth α)
    (e : ι → OpenPartialHomeomorph M (Model n)) (c : ι → Model n)
    (r : ι → T → ℝ) (hr : ∀ i, Tendsto (r i) l (𝓝 0)) :
    Tendsto (fun t ↦ integralTopFormOn a ρ
      (⋃ i, coordinateBall (e i) (c i) (r i t)) α) l (𝓝 0) := by
  have h (j : Fin a.card) := tendsto_chartDomain_removedBalls_integral_zero hn (a.chart j)
    e c r hr (topFormIntegrand a ρ α j) (integrableOn_topFormIntegrand a ρ hρ α hα j)
  simpa only [integralTopFormOn, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ ↦ h j)

theorem integralTopFormOn_puncturedDomain_eq_sub [CompactSpace M]
    {ι : Type*} [Fintype ι]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (α : Form (model n) M (2 * n)) (hα : IsSmooth α)
    (e : ι → OpenPartialHomeomorph M (Model n)) (c : ι → Model n) (r : ι → ℝ) :
    integralTopFormOn a ρ (puncturedDomain e c r) α =
      integralTopForm a ρ α - integralTopFormOn a ρ (⋃ i, coordinateBall (e i) (c i) (r i)) α := by
  unfold integralTopFormOn integralTopForm
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have heq : chartDomain (a.chart j) (puncturedDomain e c r) =
      (a.chart j).target \ chartDomain (a.chart j) (⋃ i, coordinateBall (e i) (c i) (r i)) := by
    ext y
    simp [chartDomain, puncturedDomain]
  rw [heq]
  exact setIntegral_sdiff (measurableSet_chartDomain_removedBalls (a.chart j) e c r)
    (integrableOn_topFormIntegrand a ρ hρ α hα j) inter_subset_left

theorem tendsto_integralTopFormOn_puncturedDomain [CompactSpace M]
    (hn : 0 < n) {ι T : Type*} [Fintype ι] {l : Filter T} [l.IsCountablyGenerated]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (α : Form (model n) M (2 * n)) (hα : IsSmooth α)
    (e : ι → OpenPartialHomeomorph M (Model n)) (c : ι → Model n)
    (r : ι → T → ℝ) (hr : ∀ i, Tendsto (r i) l (𝓝 0)) :
    Tendsto (fun t ↦ integralTopFormOn a ρ (puncturedDomain e c (fun i ↦ r i t)) α)
      l (𝓝 (integralTopForm a ρ α)) := by
  have h : Tendsto (fun t ↦ integralTopForm a ρ α - integralTopFormOn a ρ
      (⋃ i, coordinateBall (e i) (c i) (r i t)) α) l (𝓝 (integralTopForm a ρ α - 0)) :=
    tendsto_const_nhds.sub (tendsto_integralTopFormOn_removedBalls_zero hn a ρ hρ α hα e c r hr)
  simpa only [integralTopFormOn_puncturedDomain_eq_sub a ρ hρ α hα e c, sub_zero] using h


variable [Bundle.RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

theorem tendsto_chartIntegrand_ball_zero [CompactSpace M]
    (hn : 0 < n) (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (i : Fin a.card) (c : Model n) :
    Tendsto (fun r : ℝ ↦ ∫ y in (a.chart i).target ∩ ball c r,
      chartIntegrand n M a ρ i y) (𝓝 0) (𝓝 0) := by
  letI : Nonempty (Fin (2 * n)) := Fin.pos_iff_nonempty.mp (by omega)
  exact tendsto_integral_inter_ball_zero (integrableOn_chartIntegrand n M a ρ hρ i) c

/-- The actual Euler integral on the punctured manifold tends to the exact
curvature integral appearing in the frozen main statement. -/
theorem tendsto_integralTopFormOn_puncturedEuler [CompactSpace M]
    (hn : 0 < n) {ι T : Type*} [Fintype ι] {l : Filter T} [l.IsCountablyGenerated]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (e : ι → OpenPartialHomeomorph M (Model n)) (c : ι → Model n)
    (r : ι → T → ℝ) (hr : ∀ i, Tendsto (r i) l (𝓝 0)) :
    Tendsto (fun t ↦ integralTopFormOn a ρ (puncturedDomain e c (fun i ↦ r i t))
      (atlasEulerForm n M a hn)) l (𝓝 (curvatureIntegral n M a ρ)) := by
  simpa only [integralTopForm_atlasEulerForm] using
    tendsto_integralTopFormOn_puncturedDomain hn a ρ hρ (atlasEulerForm n M a hn)
      (isSmooth_atlasEulerForm n M a hn) e c r hr

end GaussBonnetChern
