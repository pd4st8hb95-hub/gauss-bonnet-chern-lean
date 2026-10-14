import GaussBonnetChern.DifferentialForms
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-! # Exterior differentiation in genuine chart coordinates

The coordinate maps below are built from the derivatives of the chart and its
inverse. No abstract coordinate-change or exterior-derivative axiom is introduced.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Filter

namespace GaussBonnetChern.DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

/-- The differential of the chart, with its target tangent space identified
canonically with the Euclidean model space. -/
def chartTangentMap (e : OpenPartialHomeomorph M E) (x : M) :
    TangentSpace 𝓘(ℝ, E) x →L[ℝ] E :=
  (NormedSpace.fromTangentSpace (e x)).toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x)

/-- The differential of the inverse chart, using the canonical model-space
tangent identification on its domain. -/
def inverseChartTangentMap (e : OpenPartialHomeomorph M E) (y : E) :
    E →L[ℝ] TangentSpace 𝓘(ℝ, E) (e.symm y) :=
  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y).comp
    (NormedSpace.fromTangentSpace y).symm.toContinuousLinearMap

@[simp] theorem chartRepresentation_eq (e : OpenPartialHomeomorph M E)
    (α : Form 𝓘(ℝ, E) M k) (y : E) :
    chartRepresentation e α y =
      (α (e.symm y)).compContinuousLinearMap (inverseChartTangentMap e y) := by
  ext v
  rfl

private theorem chart_mdifferentiable (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
  ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩

/-- A coordinate representation recovers the original form after pulling back
through the chart differential. -/
theorem chartRepresentation_recover (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (α : Form 𝓘(ℝ, E) M k) (x : M) (hx : x ∈ e.source) :
    (chartRepresentation e α (e x)).compContinuousLinearMap (chartTangentMap e x) = α x := by
  have hderiv := (chart_mdifferentiable e he).symm_comp_deriv hx
  ext v
  change (α (e.symm (e x))) (fun j ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (v j))) = α x v
  have hvec : (fun j ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (v j))) = v := by
    funext j
    exact congrArg (fun L ↦ L (v j)) hderiv
  rw [hvec, e.left_inv hx]

/-- Exterior derivative computed through one actual chart. -/
def chartDerivative (e : OpenPartialHomeomorph M E)
    (α : Form 𝓘(ℝ, E) M k) (x : M) :
    ContinuousAlternatingMap ℝ (TangentSpace 𝓘(ℝ, E) x) ℝ (Fin (k + 1)) :=
  (extDeriv (chartRepresentation e α) (e x)).compContinuousLinearMap (chartTangentMap e x)

/-- Global exterior differentiation uses the chart centered at the point.
Chart independence for smooth forms is a theorem, rather than a structure field. -/
def exteriorDerivative (α : Form 𝓘(ℝ, E) M k) : Form 𝓘(ℝ, E) M (k + 1) :=
  fun x ↦ chartDerivative (chartAt E x) α x

/-- The transition differential is the composite of the two actual chart
coordinate maps. All hypotheses restrict this formula to the overlap. -/
theorem transition_fderiv (e e' : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (y : E) (hy : y ∈ e.target) (hy' : e.symm y ∈ e'.source) :
    fderiv ℝ (e' ∘ e.symm) y =
      (chartTangentMap e' (e.symm y)).comp (inverseChartTangentMap e y) := by
  have hcomp := mfderiv_comp y
    ((contMDiffAt_of_mem_maximalAtlas he' hy').mdifferentiableAt (by simp))
    ((contMDiffAt_symm_of_mem_maximalAtlas he hy).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hcomp
  ext v
  exact congrArg (fun L ↦ L v) hcomp

/-- On an overlap, the two coordinate forms are related by the genuine
Fréchet-derivative pullback of the chart transition. -/
theorem transition_pullback (e e' : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (α : Form 𝓘(ℝ, E) M k) (y : E)
    (hy : y ∈ e.target) (hy' : e.symm y ∈ e'.source) :
    chartRepresentation e α y =
      (chartRepresentation e' α ((e' ∘ e.symm) y)).compContinuousLinearMap
        (fderiv ℝ (e' ∘ e.symm) y) := by
  rw [transition_fderiv e e' he he' y hy hy']
  calc
    chartRepresentation e α y =
        (α (e.symm y)).compContinuousLinearMap (inverseChartTangentMap e y) :=
      chartRepresentation_eq e α y
    _ = ((chartRepresentation e' α (e' (e.symm y))).compContinuousLinearMap
          (chartTangentMap e' (e.symm y))).compContinuousLinearMap
            (inverseChartTangentMap e y) := by
      rw [chartRepresentation_recover e' he' α (e.symm y) hy']
    _ = _ := by ext v; rfl

/-- The two coordinate tangent maps cancel on the source of a smooth chart. -/
theorem inverseChartTangentMap_chartTangentMap (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (x : M) (hx : x ∈ e.source) (v : TangentSpace 𝓘(ℝ, E) x) :
    inverseChartTangentMap e (e x) (chartTangentMap e x v) = v :=
  congrArg (fun L ↦ L v) ((chart_mdifferentiable e he).symm_comp_deriv hx)

/-- The two coordinate tangent maps cancel on the target of a smooth chart. -/
theorem chartTangentMap_inverseChartTangentMap (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (y : E) (hy : y ∈ e.target) (v : E) :
    chartTangentMap e (e.symm y) (inverseChartTangentMap e y v) = v :=
  congrArg (fun L ↦ L v) ((chart_mdifferentiable e he).comp_symm_deriv hy)

/-- Exterior derivatives of coordinate forms satisfy the transition pullback
rule on overlaps. This is a consequence of the genuine Euclidean chain rule. -/
theorem transition_extDeriv (e e' : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (α : Form 𝓘(ℝ, E) M k) (hα : IsSmooth α) (y : E)
    (hy : y ∈ e.target) (hy' : e.symm y ∈ e'.source) :
    extDeriv (chartRepresentation e α) y =
      (extDeriv (chartRepresentation e' α) ((e' ∘ e.symm) y)).compContinuousLinearMap
        (fderiv ℝ (e' ∘ e.symm) y) := by
  have hsource : e'.source ∈ 𝓝 (e.symm y) := e'.open_source.mem_nhds hy'
  have hpre : e.symm ⁻¹' e'.source ∈ 𝓝 y :=
    (e.continuousAt_symm hy).preimage_mem_nhds hsource
  have heq : chartRepresentation e α =ᶠ[𝓝 y]
      (fun z ↦ (chartRepresentation e' α ((e' ∘ e.symm) z)).compContinuousLinearMap
        (fderiv ℝ (e' ∘ e.symm) z)) := by
    filter_upwards [e.open_target.mem_nhds hy, hpre] with z hz hz'
    exact transition_pullback e e' he he' α z hz hz'
  rw [heq.extDeriv_eq]
  have hform : ContDiffAt ℝ ∞ (chartRepresentation e' α) (e' (e.symm y)) :=
    (hα e' he').contDiffAt (e'.open_target.mem_nhds (e'.map_source hy'))
  have htransition : ContDiffAt ℝ ∞ (e' ∘ e.symm) y :=
    ((contMDiffAt_of_mem_maximalAtlas he' hy').comp y
      (contMDiffAt_symm_of_mem_maximalAtlas he hy)).contDiffAt
  exact extDeriv_pullback (hform.differentiableAt (by simp)) htransition (by simp)

/-- The chart-computed exterior derivative is independent of every smooth
chart containing the point. No chart-independence hypothesis is assumed. -/
theorem chartDerivative_independent (e e' : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (α : Form 𝓘(ℝ, E) M k) (hα : IsSmooth α)
    (x : M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    chartDerivative e α x = chartDerivative e' α x := by
  have hxinv : e.symm (e x) ∈ e'.source := by simpa only [e.left_inv hx] using hx'
  have h := transition_extDeriv e e' he he' α hα (e x) (e.map_source hx) hxinv
  unfold chartDerivative
  rw [h, transition_fderiv e e' he he' (e x) (e.map_source hx) hxinv]
  ext v
  change (extDeriv (chartRepresentation e' α) (e' (e.symm (e x))))
      (fun j ↦ chartTangentMap e' (e.symm (e x))
        (inverseChartTangentMap e (e x) (chartTangentMap e x (v j)))) =
    (extDeriv (chartRepresentation e' α) (e' x)) (fun j ↦ chartTangentMap e' x (v j))
  simp only [inverseChartTangentMap_chartTangentMap e he x hx]
  simp only [e.left_inv hx]
  congr 1
  funext j
  exact congrArg
    (fun z : M ↦ (show E from chartTangentMap e' z (show TangentSpace 𝓘(ℝ, E) z from v j)))
    (e.left_inv hx)

/-- The global exterior derivative agrees with every smooth chart computation. -/
theorem exteriorDerivative_eq_chartDerivative (α : Form 𝓘(ℝ, E) M k)
    (hα : IsSmooth α) (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (x : M) (hx : x ∈ e.source) :
    exteriorDerivative α x = chartDerivative e α x :=
  chartDerivative_independent (chartAt E x) e (IsManifold.chart_mem_maximalAtlas x) he
    α hα x (mem_chart_source E x) hx

/-- In every smooth chart, the global derivative has precisely the ordinary
Euclidean exterior derivative as its coordinate representation. -/
theorem chartRepresentation_exteriorDerivative (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (α : Form 𝓘(ℝ, E) M k) (hα : IsSmooth α) (y : E) (hy : y ∈ e.target) :
    chartRepresentation e (exteriorDerivative α) y = extDeriv (chartRepresentation e α) y := by
  rw [chartRepresentation_eq,
    exteriorDerivative_eq_chartDerivative α hα e he (e.symm y) (e.map_target hy)]
  ext v
  change (extDeriv (chartRepresentation e α) (e (e.symm y)))
    (fun j ↦ chartTangentMap e (e.symm y) (inverseChartTangentMap e y (v j))) =
      extDeriv (chartRepresentation e α) y v
  simp only [chartTangentMap_inverseChartTangentMap e he y hy, e.right_inv hy]

/-- Exterior differentiation preserves actual chartwise smoothness. -/
theorem IsSmooth.exteriorDerivative {α : Form 𝓘(ℝ, E) M k} (hα : IsSmooth α) :
    IsSmooth (exteriorDerivative α) := by
  intro e he
  have hlocal : ContDiffOn ℝ ∞ (extDeriv (chartRepresentation e α)) e.target := by
    intro y hy
    have hform := (hα e he).contDiffAt (e.open_target.mem_nhds hy)
    have hd : ContDiffAt ℝ ∞ (fderiv ℝ (chartRepresentation e α)) y :=
      hform.fderiv_right (by simp)
    exact ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).contDiff.contDiffAt.comp y hd).contDiffWithinAt
  exact hlocal.congr (fun y hy ↦ chartRepresentation_exteriorDerivative e he α hα y hy)

/-- The global second exterior derivative of a smooth differential form is zero. -/
theorem exteriorDerivative_exteriorDerivative (α : Form 𝓘(ℝ, E) M k) (hα : IsSmooth α) :
    exteriorDerivative (exteriorDerivative α) = 0 := by
  funext x
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  have hy : e x ∈ e.target := e.map_source hx
  have heq : chartRepresentation e (exteriorDerivative α) =ᶠ[𝓝 (e x)]
      extDeriv (chartRepresentation e α) := by
    filter_upwards [e.open_target.mem_nhds hy] with y hy
    exact chartRepresentation_exteriorDerivative e he α hα y hy
  rw [exteriorDerivative_eq_chartDerivative (exteriorDerivative α) hα.exteriorDerivative e he x hx]
  unfold chartDerivative
  rw [heq.extDeriv_eq,
    extDeriv_extDeriv_apply ((hα e he).contDiffAt (e.open_target.mem_nhds hy)) (by simp)]
  ext v
  rfl

end GaussBonnetChern.DifferentialForm






