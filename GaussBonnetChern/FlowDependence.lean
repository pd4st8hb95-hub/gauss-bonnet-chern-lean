import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-! # Continuous dependence of actual integral curves

The local solution families below are obtained from Picard--Lindelöf with
joint continuity in initial point and time. Continuity is a proved property
of the constructed solutions; it is not inferred from pointwise existence.
-/

noncomputable section

open Function Set Filter Metric
open scoped Topology Manifold ContDiff

namespace GaussBonnetChern.Morse

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuously differentiable vector field has a jointly continuous local
flow on one common time interval for all nearby initial conditions. -/
theorem exists_continuous_localFlow {v : E → E} {x₀ : E}
    (hv : ContDiffAt ℝ 1 v x₀) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : E × ℝ → E,
      ContinuousOn Φ (ball x₀ r ×ˢ Ioo (-ε) ε) ∧
      (∀ x ∈ ball x₀ r, Φ (x, 0) = x) ∧
      ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => Φ (x, s)) (v (Φ (x, t))) t := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hv
  obtain ⟨Φ, hΦ, hc⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  simp only [zero_sub, zero_add] at hΦ hc
  refine ⟨r, hr, ε, hε, Φ, hc.mono ?_, ?_, ?_⟩
  · exact fun z hz => ⟨ball_subset_closedBall hz.1, Ioo_subset_Icc_self hz.2⟩
  · intro x hx
    exact (hΦ x (ball_subset_closedBall hx)).1
  · intro x hx t ht
    exact ((hΦ x (ball_subset_closedBall hx)).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)

/-- The same local flow can be restricted so that all its trajectories remain
in a prescribed open neighborhood of the starting point. -/
theorem exists_continuous_localFlow_in {v : E → E} {x₀ : E} {U : Set E}
    (hv : ContDiffAt ℝ 1 v x₀) (hU : IsOpen U) (hxU : x₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : E × ℝ → E,
      ContinuousOn Φ (ball x₀ r ×ˢ Ioo (-ε) ε) ∧
      (∀ x ∈ ball x₀ r, Φ (x, 0) = x) ∧
      (∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => Φ (x, s)) (v (Φ (x, t))) t) ∧
      MapsTo Φ (ball x₀ r ×ˢ Ioo (-ε) ε) U := by
  obtain ⟨r, hr, ε, hε, Φ, hc, hzero, hder⟩ := exists_continuous_localFlow hv
  have hbase : (x₀, (0 : ℝ)) ∈ ball x₀ r ×ˢ Ioo (-ε) ε :=
    ⟨mem_ball_self hr, by constructor <;> linarith⟩
  have hca : ContinuousAt Φ (x₀, 0) :=
    (hc _ hbase).continuousAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds hbase)
  have hpre : Φ ⁻¹' U ∈ 𝓝 (x₀, (0 : ℝ)) :=
    hca.preimage_mem_nhds (hU.mem_nhds (by simpa [hzero _ (mem_ball_self hr)] using hxU))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  let r' := min r δ
  let ε' := min ε δ
  have hsub : ball x₀ r' ×ˢ Ioo (-ε') ε' ⊆ ball x₀ r ×ˢ Ioo (-ε) ε := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨ball_subset_ball (min_le_left _ _) hx,
      ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ht.1,
        lt_of_lt_of_le ht.2 (min_le_left _ _)⟩⟩
  refine ⟨r', lt_min hr hδ, ε', lt_min hε hδ, Φ, hc.mono hsub, ?_, ?_, ?_⟩
  · intro x hx
    exact hzero x (ball_subset_ball (min_le_left _ _) hx)
  · intro x hx t ht
    exact hder x (hsub (a := (x, t)) ⟨hx, ht⟩).1 t
      (hsub (a := (x, t)) ⟨hx, ht⟩).2
  · rintro ⟨x, t⟩ ⟨hx, ht⟩
    apply hδsub
    rw [← ball_prod_same]
    refine ⟨ball_subset_ball (min_le_right _ _) hx, ?_⟩
    rw [Real.ball_eq_Ioo]
    simp only [zero_sub, zero_add]
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right _ _)⟩

end Normed


section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [I.Boundaryless]

/-- The given vector field in the coordinates centered at `x₀`. -/
def coordinateVectorField (x₀ : M) (v : (x : M) → TangentSpace I x) : E → E :=
  fun y => tangentCoordChange I ((extChartAt I x₀).symm y) x₀
    ((extChartAt I x₀).symm y) (v ((extChartAt I x₀).symm y))

set_option backward.isDefEq.respectTransparency false in
theorem contDiffAt_coordinateVectorField {x₀ : M} {v : (x : M) → TangentSpace I x}
    (hv : ContMDiffAt I I.tangent 1 (T% v) x₀) :
    ContDiffAt ℝ 1 (coordinateVectorField (I := I) x₀ v) (extChartAt I x₀ x₀) := by
  rw [contMDiffAt_iff] at hv
  exact (hv.2.contDiffAt (range_mem_nhds_isInteriorPoint
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))).snd

set_option backward.isDefEq.respectTransparency false in
/-- Transport a coordinate solution through the actual inverse chart. -/
theorem hasMFDerivAt_inverseChart_of_hasDerivAt {x₀ : M}
    {v : (x : M) → TangentSpace I x} {γ : ℝ → E} {t : ℝ}
    (hγ : HasDerivAt γ (coordinateVectorField (I := I) x₀ v (γ t)) t)
    (ht : γ t ∈ (extChartAt I x₀).target) :
    HasMFDerivAt 𝓘(ℝ) I ((extChartAt I x₀).symm ∘ γ) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((extChartAt I x₀).symm (γ t)))) := by
  let xₜ : M := (extChartAt I x₀).symm (γ t)
  have hsrc := (extChartAt I x₀).map_target ht
  have hself := mem_extChartAt_source (I := I) xₜ
  refine ⟨(continuousAt_extChartAt_symm'' ht).comp hγ.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ γ) (v xₜ) t
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hself,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hself, hsrc⟩, hself⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ hγ
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _
    (mem_of_superset ((isOpen_extChartAt_target x₀).mem_nhds ht)
      (extChartAt_target_subset_range ..))
  rw [← (extChartAt I x₀).right_inv ht]
  exact hasFDerivWithinAt_tangentCoordChange ⟨hsrc, hself⟩

/-- A `C¹` vector field has a jointly continuous local flow on a manifold,
uniformly for every initial point in one open neighborhood. -/
theorem exists_continuous_localMFlow {x₀ : M} {v : (x : M) → TangentSpace I x}
    (hv : ContMDiffAt I I.tangent 1 (T% v) x₀) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ ε > (0 : ℝ), ∃ Φ : M × ℝ → M,
        ContinuousOn Φ (U ×ˢ Ioo (-ε) ε) ∧
        (∀ x ∈ U, Φ (x, 0) = x) ∧
        ∀ x ∈ U, IsMIntegralCurveOn (fun t => Φ (x, t)) v (Ioo (-ε) ε) := by
  let φ := extChartAt I x₀
  obtain ⟨r, hr, ε, hε, α, hcont, hzero, hder, hrange⟩ :=
    exists_continuous_localFlow_in (contDiffAt_coordinateVectorField hv)
      (isOpen_extChartAt_target x₀) (mem_extChartAt_target x₀)
  let U : Set M := φ.source ∩ φ ⁻¹' ball (φ x₀) r
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact inter_mem (extChartAt_source_mem_nhds' hx.1)
      ((continuousAt_extChartAt' hx.1).preimage_mem_nhds (isOpen_ball.mem_nhds hx.2))
  have hxU : x₀ ∈ U := ⟨mem_extChartAt_source x₀, mem_ball_self hr⟩
  let Φ : M × ℝ → M := fun z => φ.symm (α (φ z.1, z.2))
  have hmap : MapsTo (fun z : M × ℝ => (φ z.1, z.2))
      (U ×ˢ Ioo (-ε) ε) (ball (φ x₀) r ×ˢ Ioo (-ε) ε) := fun z hz => ⟨hz.1.2, hz.2⟩
  have hcp : ContinuousOn (fun z : M × ℝ => (φ z.1, z.2)) (U ×ˢ Ioo (-ε) ε) :=
    ((continuousOn_extChartAt x₀).comp continuousOn_fst (fun z hz => hz.1.1)).prodMk
      continuousOn_snd
  refine ⟨U, hU, hxU, ε, hε, Φ, ?_, ?_, ?_⟩
  · exact (continuousOn_extChartAt_symm x₀).comp (hcont.comp hcp hmap)
      (fun z hz => hrange (hmap hz))
  · intro x hx
    change φ.symm (α (φ x, 0)) = x
    rw [hzero (φ x) hx.2, φ.left_inv hx.1]
  · intro x hx t ht
    exact (hasMFDerivAt_inverseChart_of_hasDerivAt (hder (φ x) hx.2 t ht)
      (hrange ⟨hx.2, ht⟩)).hasMFDerivWithinAt


/-- Compactness gives a common positive time for jointly continuous local
flows, even though different spatial neighborhoods may use different charts. -/
theorem exists_uniform_continuous_localMFlow [CompactSpace M]
    {v : (x : M) → TangentSpace I x} (hv : ContMDiff I I.tangent 1 (T% v)) :
    ∃ ε > (0 : ℝ), ∀ x₀ : M, ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ Φ : M × ℝ → M, ContinuousOn Φ (U ×ˢ Ioo (-ε) ε) ∧
        (∀ x ∈ U, Φ (x, 0) = x) ∧
        ∀ x ∈ U, IsMIntegralCurveOn (fun t => Φ (x, t)) v (Ioo (-ε) ε) := by
  classical
  choose U hU hxU ε hε Φ hc hzero hsol using fun x => exists_continuous_localMFlow (hv x)
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  have hbound : ∃ δ > (0 : ℝ), ∀ i ∈ S, δ ≤ ε i := by
    clear hS
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a S ha ih =>
      obtain ⟨δ, hδ, hδS⟩ := ih
      refine ⟨min (ε a) δ, lt_min (hε a) hδ, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hδS i hi)
  obtain ⟨δ, hδ, hδS⟩ := hbound
  refine ⟨δ, hδ, ?_⟩
  intro x
  obtain ⟨i, hiS, hxi⟩ := mem_iUnion₂.mp (hS (mem_univ x))
  have ht : Ioo (-δ) δ ⊆ Ioo (-(ε i)) (ε i) :=
    Ioo_subset_Ioo (neg_le_neg (hδS i hiS)) (hδS i hiS)
  exact ⟨U i, hU i, hxi, Φ i, (hc i).mono (prod_subset_prod_right ht),
    hzero i, fun y hy => (hsol i y hy).mono ht⟩

/-- Every `C¹` vector field on a compact boundaryless Hausdorff manifold has
global integral curves; uniform local time is obtained internally. -/
theorem exists_globalMIntegralCurve_of_compact [CompactSpace M] [T2Space M]
    {v : (x : M) → TangentSpace I x} (hv : ContMDiff I I.tangent 1 (T% v)) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε, hε, hloc⟩ := exists_uniform_continuous_localMFlow hv
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε _ x
  intro y
  obtain ⟨U, hU, hyU, Φ, hc, hzero, hsol⟩ := hloc y
  exact ⟨fun t => Φ (y, t), hzero y hyU, hsol y hyU⟩

/-- A chosen global solution family has the flow law by actual uniqueness. -/
theorem globalMFlow_add [T2Space M]
    {v : (x : M) → TangentSpace I x} (hv : ContMDiff I I.tangent 1 (T% v))
    {Φ : M × ℝ → M} (hzero : ∀ x, Φ (x, 0) = x)
    (hsol : ∀ x, IsMIntegralCurve (fun t => Φ (x, t)) v) (x : M) (s t : ℝ) :
    Φ (x, s + t) = Φ (Φ (x, s), t) := by
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv
    ((hsol x).comp_add s) (hsol (Φ (x, s))) (by simp [hzero])
  simpa [add_comm] using congrFun heq t

/-- Any global solution family agrees with an actual continuous local flow
on its full local domain, not just separately at each initial condition. -/
theorem globalMFlow_eq_local [T2Space M]
    {v : (x : M) → TangentSpace I x} (hv : ContMDiff I I.tangent 1 (T% v))
    {Φ : M × ℝ → M} (hzero : ∀ x, Φ (x, 0) = x)
    (hsol : ∀ x, IsMIntegralCurve (fun t => Φ (x, t)) v)
    {U : Set M} {ε : ℝ} (hε : 0 < ε) {α : M × ℝ → M}
    (ha0 : ∀ x ∈ U, α (x, 0) = x)
    (ha : ∀ x ∈ U, IsMIntegralCurveOn (fun t => α (x, t)) v (Ioo (-ε) ε)) :
    EqOn Φ α (U ×ˢ Ioo (-ε) ε) := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) (by constructor <;> linarith) hv
    ((hsol x).isMIntegralCurveOn _) (ha x hx) (by rw [hzero, ha0 x hx]) ht


/-- On a compact manifold, the actual global solution family depends jointly
continuously on its initial point and time. The proof uses the flow law and
finitely many locally continuous solution families. -/
theorem continuous_globalMFlow_of_compact [CompactSpace M] [T2Space M]
    {v : (x : M) → TangentSpace I x} (hv : ContMDiff I I.tangent 1 (T% v))
    {Φ : M × ℝ → M} (hzero : ∀ x, Φ (x, 0) = x)
    (hsol : ∀ x, IsMIntegralCurve (fun t => Φ (x, t)) v) : Continuous Φ := by
  obtain ⟨ε, hε, hloc⟩ := exists_uniform_continuous_localMFlow hv
  have hsmall : ∀ t ∈ Ioo (-ε) ε, Continuous (fun x => Φ (x, t)) := by
    intro t ht
    apply continuous_iff_continuousAt.mpr
    intro x
    obtain ⟨U, hU, hxU, α, hc, ha0, ha⟩ := hloc x
    have heq := globalMFlow_eq_local hv hzero hsol hε ha0 ha
    have hcΦ := hc.congr heq
    have hc0 : ContinuousAt Φ (x, t) := (hcΦ (x, t) ⟨hxU, ht⟩).continuousAt
      ((hU.prod isOpen_Ioo).mem_nhds ⟨hxU, ht⟩)
    exact hc0.comp (f := fun y : M => (y, t))
      (continuousAt_id.prodMk continuousAt_const)
  have hiter (s : ℝ) (k : ℕ) (x : M) :
      Φ (x, (k : ℝ) * s) = (fun y => Φ (y, s))^[k] x := by
    induction k with
    | zero => simpa using hzero x
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, globalMFlow_add hv hzero hsol, ih,
        Function.iterate_succ_apply']
  have htime : ∀ t : ℝ, Continuous (fun x => Φ (x, t)) := by
    intro t
    obtain ⟨k, hk⟩ := exists_nat_gt (|t| / ε)
    have hkpos : (0 : ℝ) < k := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hε.le) hk
    have hknz : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    have hstep : t / k ∈ Ioo (-ε) ε := by
      rw [mem_Ioo, ← abs_lt, abs_div, abs_of_pos hkpos, div_lt_iff₀ hkpos]
      have := (div_lt_iff₀ hε).mp hk
      linarith
    have hc := (hsmall (t / k) hstep).iterate k
    convert hc using 1
    funext x
    rw [← hiter]
    congr 1
    field_simp
  apply continuous_iff_continuousAt.mpr
  rintro ⟨x, t⟩
  obtain ⟨U, hU, hxU, α, hc, ha0, ha⟩ := hloc (Φ (x, t))
  have heq := globalMFlow_eq_local hv hzero hsol hε ha0 ha
  let F : M × ℝ → M × ℝ := fun z => (Φ (z.1, t), z.2 - t)
  have hF : Continuous F := (htime t |>.comp continuous_fst).prodMk
    (continuous_snd.sub continuous_const)
  have hFmem : F (x, t) ∈ U ×ˢ Ioo (-ε) ε :=
    ⟨hxU, by simp only [F, sub_self]; constructor <;> linarith⟩
  have hα : ContinuousAt α (F (x, t)) :=
    (hc _ hFmem).continuousAt ((hU.prod isOpen_Ioo).mem_nhds hFmem)
  apply (hα.comp hF.continuousAt).congr_of_eventuallyEq
  filter_upwards [hF.continuousAt.preimage_mem_nhds
    ((hU.prod isOpen_Ioo).mem_nhds hFmem)] with z hz
  calc
    Φ z = Φ (Φ (z.1, t), z.2 - t) := by
      rw [← globalMFlow_add hv hzero hsol]
      congr 1
      simp
    _ = α (F z) := heq hz

/-- Complete `C¹` dynamics on the compact manifold, including proved joint
continuity, initial conditions, the actual differential equation and flow law. -/
theorem exists_continuous_globalMFlow [CompactSpace M] [T2Space M]
    {v : (x : M) → TangentSpace I x} (hv : ContMDiff I I.tangent 1 (T% v)) :
    ∃ Φ : M × ℝ → M, Continuous Φ ∧ (∀ x, Φ (x, 0) = x) ∧
      (∀ x, IsMIntegralCurve (fun t => Φ (x, t)) v) ∧
      ∀ x s t, Φ (x, s + t) = Φ (Φ (x, s), t) := by
  choose γ hzero hsol using exists_globalMIntegralCurve_of_compact hv
  let Φ : M × ℝ → M := fun z => γ z.1 z.2
  exact ⟨Φ, continuous_globalMFlow_of_compact hv hzero hsol, hzero, hsol,
    globalMFlow_add hv hzero hsol⟩

end Manifold

end GaussBonnetChern.Morse
