import GaussBonnetChern.ExteriorDerivativeNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff Topology
namespace GaussBonnetChern.DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  {k : ℕ}

/-- A smooth pullback is a smooth form whenever the original form is
smooth in actual centered coordinates at each point of the image. No
unrelated global extension of a local frame is required to be smooth. -/
theorem isSmooth_pullback_of_chartSmoothAt (f : M → N)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (α : Form 𝓘(ℝ,F) N k)
    (hα : ∀ x : M, ContDiffAt ℝ ∞ (chartRepresentation (chartAt F (f x)) α)
      ((chartAt F (f x)) (f x))) :
    IsSmooth (pullback (I := 𝓘(ℝ,E)) f α) := by
  intro e he y hy
  let e' := chartAt F (f (e.symm y))
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ,F) ∞ N :=
    IsManifold.chart_mem_maximalAtlas (f (e.symm y))
  have hy' : f (e.symm y) ∈ e'.source := mem_chart_source F _
  have hc := coordinateMap_contDiffAt e e' he he' f hf y hy hy'
  have ha : ContDiffAt ℝ ∞ (chartRepresentation e' α) (coordinateMap e e' f y) :=
    hα (e.symm y)
  have hpoly := contDiffAt_compContinuousLinearMap (ha.comp y hc)
    (hc.fderiv_right (m := ∞) (by simp))
  exact (hpoly.congr_of_eventuallyEq
    (chartRepresentation_pullback_eventuallyEq e e' he he' f hf α y hy hy')).contDiffWithinAt

/-- Pointwise naturality of the actual exterior derivative only needs
smoothness of the original form at the image point in centered coordinates. -/
theorem pullback_exteriorDerivative_at (f : M → N)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (α : Form 𝓘(ℝ,F) N k) (x : M)
    (hα : ContDiffAt ℝ ∞ (chartRepresentation (chartAt F (f x)) α)
      ((chartAt F (f x)) (f x))) :
    pullback (I := 𝓘(ℝ,E)) f (exteriorDerivative α) x =
      exteriorDerivative (pullback (I := 𝓘(ℝ,E)) f α) x := by
  let e := chartAt E x
  let e' := chartAt F (f x)
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ,F) ∞ N := IsManifold.chart_mem_maximalAtlas (f x)
  have hx : x ∈ e.source := mem_chart_source E x
  have hx' : f x ∈ e'.source := mem_chart_source F (f x)
  have hsource : f (e.symm (e x)) ∈ e'.source := by simpa only [e.left_inv hx] using hx'
  have hpoint : coordinateMap e e' f (e x) = e' (f x) := by
    simp only [coordinateMap, Function.comp_apply, e.left_inv hx]
  have hderiv : extDeriv (chartRepresentation e (pullback (I := 𝓘(ℝ,E)) f α)) (e x) =
      (extDeriv (chartRepresentation e' α) (coordinateMap e e' f (e x))).compContinuousLinearMap
        (fderiv ℝ (coordinateMap e e' f) (e x)) := by
    rw [(chartRepresentation_pullback_eventuallyEq e e' he he' f hf α (e x)
      (e.map_source hx) hsource).extDeriv_eq]
    have ha : ContDiffAt ℝ ∞ (chartRepresentation e' α) (coordinateMap e e' f (e x)) :=
      hpoint.symm ▸ hα
    exact extDeriv_pullback (ha.differentiableAt (by simp))
      (coordinateMap_contDiffAt e e' he he' f hf (e x) (e.map_source hx) hsource) (by simp)
  change (chartDerivative e' α (f x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x) = chartDerivative e (pullback (I := 𝓘(ℝ,E)) f α) x
  unfold chartDerivative
  rw [hderiv, hpoint]
  ext v
  change (extDeriv (chartRepresentation e' α) (e' (f x)))
      (fun j ↦ chartTangentMap e' (f x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x (v j))) =
    (extDeriv (chartRepresentation e' α) (e' (f x)))
      (fun j ↦ fderiv ℝ (coordinateMap e e' f) (e x) (chartTangentMap e x (v j)))
  congr 1
  funext j
  exact (coordinateMap_fderiv_chartTangentMap e e' he he' f hf x hx hx' (v j)).symm

/-- Centered-chart smoothness at every point gives the all-maximal-chart
regularity required by `IsSmooth`, by the actual coordinate-change formula. -/
theorem isSmooth_of_centeredChartSmoothAt (α : Form 𝓘(ℝ,F) N k)
    (hα : ∀ x : N, ContDiffAt ℝ ∞ (chartRepresentation (chartAt F x) α) ((chartAt F x) x)) :
    IsSmooth α := by
  simpa only [pullback_id] using isSmooth_pullback_of_chartSmoothAt
    (E := F) (M := N) id contMDiff_id α hα

/-- Restricting a genuinely local smooth form to its actual open domain
makes a globally smooth form on that open submanifold. -/
theorem isSmooth_restrict_of_chartSmoothAt (U : TopologicalSpace.Opens N)
    (α : Form 𝓘(ℝ,F) N k)
    (hα : ∀ x ∈ U, ContDiffAt ℝ ∞ (chartRepresentation (chartAt F x) α) ((chartAt F x) x)) :
    IsSmooth (pullback (I := 𝓘(ℝ,F)) ((↑) : U → N) α) :=
  isSmooth_pullback_of_chartSmoothAt _ contMDiff_subtype_val α (fun x ↦ hα x.1 x.2)

theorem restrict_exteriorDerivative_of_chartSmoothAt (U : TopologicalSpace.Opens N)
    (α : Form 𝓘(ℝ,F) N k)
    (hα : ∀ x ∈ U, ContDiffAt ℝ ∞ (chartRepresentation (chartAt F x) α) ((chartAt F x) x)) :
    pullback (I := 𝓘(ℝ,F)) ((↑) : U → N) (exteriorDerivative α) =
      exteriorDerivative (pullback (I := 𝓘(ℝ,F)) ((↑) : U → N) α) := by
  funext x
  exact pullback_exteriorDerivative_at _ contMDiff_subtype_val α x (hα x.1 x.2)

end GaussBonnetChern.DifferentialForm
