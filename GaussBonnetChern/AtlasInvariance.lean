import GaussBonnetChern.FormIntegration
import GaussBonnetChern.ExteriorDerivative
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Determinant

/-! # Integrability and changes of positive coordinates for top forms

All coefficients are those of the actual alternating form. Compact support is
transported through the chart only inside its source, so no regularity of the
totalized inverse chart outside its target is used.
-/

noncomputable section

open MeasureTheory Module
open scoped Manifold ContDiff BigOperators

namespace GaussBonnetChern

open DifferentialForm

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

/-- A continuous scalar weight with compact support contained in one chart gives
an integrable chart coefficient for every smooth top form. -/
theorem integrableOn_weighted_topFormCoefficient
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (α : Form (model n) M (2 * n)) (hα : IsSmooth α)
    (φ : M → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ e.source) :
    IntegrableOn (fun y ↦ φ (e.symm y) * topFormCoefficient e α y) e.target volume := by
  let K := e '' tsupport φ
  have hK : IsCompact K := hc.image_of_continuousOn (e.continuousOn.mono hs)
  have hKt : K ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  have hcont : ContinuousOn (fun y ↦ φ (e.symm y) * topFormCoefficient e α y)
      e.target :=
    (hφ.comp_continuousOn e.continuousOn_symm).mul
      (contDiffOn_topFormCoefficient e he α hα).continuousOn
  apply ((hcont.mono hKt).integrableOn_compact hK).of_forall_sdiff_eq_zero
    e.open_target.measurableSet
  intro y hy
  have hz : φ (e.symm y) = 0 := by
    by_contra hz
    exact hy.2 ⟨e.symm y, subset_tsupport φ hz, e.right_inv hy.1⟩
  simp [hz]

/-- The subordinate partitions appearing in the frozen theorem do satisfy the
integrability obligation for actual smooth top forms. -/
theorem integrableOn_topFormIntegrand [CompactSpace M]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (α : Form (model n) M (2 * n)) (hα : IsSmooth α) (i : Fin a.card) :
    IntegrableOn (topFormIntegrand a ρ α i) (a.chart i).target volume :=
  integrableOn_weighted_topFormCoefficient (a.chart i) (a.smooth i) α hα
    (ρ i) (ρ i).contMDiff.continuous (isClosed_tsupport _).isCompact (hρ i)

theorem integralTopForm_add_smooth [CompactSpace M]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (α β : Form (model n) M (2 * n)) (hα : IsSmooth α) (hβ : IsSmooth β) :
    integralTopForm a ρ (α + β) = integralTopForm a ρ α + integralTopForm a ρ β :=
  integralTopForm_add a ρ α β
    (integrableOn_topFormIntegrand a ρ hρ α hα)
    (integrableOn_topFormIntegrand a ρ hρ β hβ)

/-- The top-degree coefficient changes by the determinant of the actual chart
transition. This holds for arbitrary top forms, before any smoothness choice. -/
theorem topFormCoefficient_transition
    (e e' : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (α : Form (model n) M (2 * n)) (y : Model n)
    (hy : y ∈ e.target) (hy' : e.symm y ∈ e'.source) :
    topFormCoefficient e α y =
      LinearMap.det (fderiv ℝ (e' ∘ e.symm) y).toLinearMap *
        topFormCoefficient e' α ((e' ∘ e.symm) y) := by
  unfold topFormCoefficient
  rw [transition_pullback e e' he he' α y hy hy']
  let A := (chartRepresentation e' α ((e' ∘ e.symm) y)).toAlternatingMap
  let b := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
  let T := (fderiv ℝ (e' ∘ e.symm) y).toLinearMap
  have h := congrArg (fun f : Model n [⋀^Fin (2 * n)]→ₗ[ℝ] ℝ ↦
      f (fun i ↦ T (b i))) (A.eq_smul_basis_det b)
  have hb : b.det (fun i ↦ T (b i)) = LinearMap.det T := by
    change b.det (T ∘ b) = LinearMap.det T
    rw [Basis.det_comp, Basis.det_self, mul_one]
  change A (fun i ↦ T (b i)) = A b * b.det (fun i ↦ T (b i)) at h
  rw [hb] at h
  change A (fun i ↦ T (b i)) = LinearMap.det T * A b
  exact h.trans (mul_comm _ _)


/-- A weight supported in both charts has equal top-form integrals when the
transition preserves orientation. Integrability is not assumed or encoded. -/
theorem weighted_topFormIntegral_change_chart
    (e e' : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (α : Form (model n) M (2 * n)) (φ : M → ℝ)
    (hs : Function.support φ ⊆ e.source) (hs' : Function.support φ ⊆ e'.source)
    (hp : ∀ x ∈ e.source, x ∈ e'.source →
      0 < LinearMap.det (fderiv ℝ (e' ∘ e.symm) (e x)).toLinearMap) :
    (∫ y in e.target, φ (e.symm y) * topFormCoefficient e α y ∂volume) =
      ∫ y in e'.target, φ (e'.symm y) * topFormCoefficient e' α y ∂volume := by
  let t := e.symm.trans e'
  have hl : (∫ y in e.target, φ (e.symm y) * topFormCoefficient e α y ∂volume) =
      ∫ y in t.source, φ (e.symm y) * topFormCoefficient e α y ∂volume := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e.open_target.measurableSet
      Set.inter_subset_left
    intro y hy
    have hz : φ (e.symm y) = 0 := by
      by_contra hz
      exact hy.2 ⟨hy.1, hs' hz⟩
    simp [hz]
  have hr : (∫ y in e'.target, φ (e'.symm y) * topFormCoefficient e' α y ∂volume) =
      ∫ y in t.target, φ (e'.symm y) * topFormCoefficient e' α y ∂volume := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e'.open_target.measurableSet
      Set.inter_subset_left
    intro y hy
    have hz : φ (e'.symm y) = 0 := by
      by_contra hz
      exact hy.2 ⟨hy.1, hs hz⟩
    simp [hz]
  rw [hl, hr]
  have hd : ∀ y ∈ t.source, HasFDerivAt t (fderiv ℝ (e' ∘ e.symm) y) y := by
    intro y hy
    have ht : ContDiffAt ℝ ∞ (e' ∘ e.symm) y :=
      ((contMDiffAt_of_mem_maximalAtlas he' hy.2).comp y
        (contMDiffAt_symm_of_mem_maximalAtlas he hy.1)).contDiffAt
    exact (ht.differentiableAt (by simp)).hasFDerivAt
  rw [integral_target_eq_integral_abs_det_fderiv_smul volume hd]
  apply setIntegral_congr_fun t.open_source.measurableSet
  intro y hy
  have hy0 : y ∈ e.target := hy.1
  have hy1 : e.symm y ∈ e'.source := hy.2
  change φ (e.symm y) * topFormCoefficient e α y =
    |LinearMap.det (fderiv ℝ (e' ∘ e.symm) y).toLinearMap| •
      (φ (e'.symm (e' (e.symm y))) * topFormCoefficient e' α (e' (e.symm y)))
  rw [e'.left_inv hy1, topFormCoefficient_transition e e' he he' α y hy0 hy1]
  have hpos : 0 < LinearMap.det (fderiv ℝ (e' ∘ e.symm) y).toLinearMap := by
    simpa only [e.right_inv hy0] using hp (e.symm y) (e.map_target hy0) hy1
  rw [abs_of_pos hpos, smul_eq_mul]
  simp only [Function.comp_apply]
  ring

/-- Two finite atlases represent the same chosen orientation exactly when
their cross-chart transitions preserve orientation. -/
def FiniteOrientedAtlas.Compatible (a b : FiniteOrientedAtlas n M) : Prop :=
  ∀ i j (x : M), x ∈ (a.chart i).source → x ∈ (b.chart j).source →
    0 < LinearMap.det (fderiv ℝ ((b.chart j) ∘ (a.chart i).symm)
      ((a.chart i) x)).toLinearMap

theorem FiniteOrientedAtlas.compatible_self (a : FiniteOrientedAtlas n M) :
    a.Compatible a := a.positive_transition


theorem integralTopForm_partition_refinement [CompactSpace M]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    {ι : Type*} [Fintype ι]
    (τ : SmoothPartitionOfUnity ι (model n) M Set.univ)
    (α : Form (model n) M (2 * n)) (hα : IsSmooth α) :
    integralTopForm a ρ α = ∑ i, ∑ j,
      ∫ y in (a.chart i).target,
        (ρ i ((a.chart i).symm y) * τ j ((a.chart i).symm y)) *
          topFormCoefficient (a.chart i) α y ∂volume := by
  classical
  unfold integralTopForm
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with y
    have hs : ∑ j, τ j ((a.chart i).symm y) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using
        τ.sum_eq_one (Set.mem_univ ((a.chart i).symm y))
    simp only [topFormIntegrand, ← Finset.sum_mul, ← Finset.mul_sum, hs, mul_one]
  · intro j _
    apply integrableOn_weighted_topFormCoefficient (a.chart i) (a.smooth i) α hα
      (fun x ↦ ρ i x * τ j x)
      ((ρ i).contMDiff.continuous.mul (τ j).contMDiff.continuous)
      (isClosed_tsupport _).isCompact
    exact (tsupport_mul_subset_left (f := fun x ↦ ρ i x)
      (g := fun x ↦ τ j x)).trans (hρ i)

/-- Actual top-form integration is independent of the subordinate partition
and finite atlas representing the same orientation. -/
theorem integralTopForm_independent [CompactSpace M]
    (a b : FiniteOrientedAtlas n M) (hab : a.Compatible b)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (τ : SmoothPartitionOfUnity (Fin b.card) (model n) M Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (hτ : τ.IsSubordinate (fun j ↦ (b.chart j).source))
    (α : Form (model n) M (2 * n)) (hα : IsSmooth α) :
    integralTopForm a ρ α = integralTopForm b τ α := by
  classical
  rw [integralTopForm_partition_refinement a ρ hρ τ α hα,
    integralTopForm_partition_refinement b τ hτ ρ α hα, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have h := weighted_topFormIntegral_change_chart (a.chart i) (b.chart j)
    (a.smooth i) (b.smooth j) α (fun x ↦ ρ i x * τ j x)
    ((Function.support_mul_subset_left _ _).trans ((subset_tsupport _).trans (hρ i)))
    ((Function.support_mul_subset_right _ _).trans ((subset_tsupport _).trans (hτ j)))
    (hab i j)
  simpa only [mul_comm (ρ i _) (τ j _)] using h

theorem integralTopForm_partition_independent [CompactSpace M]
    (a : FiniteOrientedAtlas n M)
    (ρ τ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (hτ : τ.IsSubordinate (fun j ↦ (a.chart j).source))
    (α : Form (model n) M (2 * n)) (hα : IsSmooth α) :
    integralTopForm a ρ α = integralTopForm a τ α :=
  integralTopForm_independent a a a.compatible_self ρ τ hρ hτ α hα

end GaussBonnetChern
