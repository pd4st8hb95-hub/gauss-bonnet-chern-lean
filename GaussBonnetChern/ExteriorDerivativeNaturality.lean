import GaussBonnetChern.ExteriorDerivative
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-! # Naturality of actual manifold exterior differentiation

Coordinate maps use the genuine map and chart derivatives. Smooth pullback is
proved using the polynomial pullback operation on continuous alternating maps.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Filter

namespace GaussBonnetChern.DifferentialForm

set_option backward.isDefEq.respectTransparency false

section AlternatingProjection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)

/-- Alternatization as a real linear map. -/
def alternatizationLinear :
    ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ →ₗ[ℝ]
      ContinuousAlternatingMap ℝ E ℝ (Fin k) where
  toFun := ContinuousMultilinearMap.alternatization
  map_add' f g := map_add _ f g
  map_smul' c f := by
    ext v
    simp only [ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    exact smul_comm (Equiv.Perm.sign σ) c (f (v ∘ σ))

/-- The finite permutation formula gives an operator-norm bound. -/
theorem norm_alternatizationLinear_le (f : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ) :
    ‖alternatizationLinear k f‖ ≤ (Fintype.card (Equiv.Perm (Fin k)) : ℝ) * ‖f‖ := by
  change ‖∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • f.domDomCongr σ‖ ≤ _
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin k), ‖Equiv.Perm.sign σ • f.domDomCongr σ‖ := norm_sum_le _ _
    _ = _ := by simp [ContinuousMultilinearMap.norm_domDomCongr]

/-- Bounded alternatization, with a proved finite norm bound. -/
def alternatizationCLM :
    ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ →L[ℝ]
      ContinuousAlternatingMap ℝ E ℝ (Fin k) :=
  (alternatizationLinear (E := E) k).mkContinuous (Fintype.card (Equiv.Perm (Fin k)) : ℝ)
    (fun f ↦ norm_alternatizationLinear_le (E := E) k f)

/-- Normalized alternatization projects onto the alternating maps. -/
def alternatingProjection :
    ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ →L[ℝ]
      ContinuousAlternatingMap ℝ E ℝ (Fin k) :=
  (k.factorial : ℝ)⁻¹ • alternatizationCLM k

@[simp] theorem alternatingProjection_toContinuousMultilinearMap
    (α : ContinuousAlternatingMap ℝ E ℝ (Fin k)) :
    alternatingProjection k α.toContinuousMultilinearMap = α := by
  have h : ContinuousMultilinearMap.alternatization α.toContinuousMultilinearMap =
      k.factorial • α := by
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    rw [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap,
      ContinuousAlternatingMap.toAlternatingMap_smul]
    simpa using AlternatingMap.coe_alternatization α.toAlternatingMap
  change (k.factorial : ℝ)⁻¹ • ContinuousMultilinearMap.alternatization
    α.toContinuousMultilinearMap = α
  rw [h, ← Nat.cast_smul_eq_nsmul (R := ℝ)]
  simp [smul_smul, Nat.factorial_ne_zero]

end AlternatingProjection

section PolynomialPullback
variable {V E F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {a : V → ContinuousAlternatingMap ℝ F ℝ (Fin k)}
  {L : V → E →L[ℝ] F} {x : V}

/-- Pullback of an alternating map is smooth jointly in its coefficients and
in the linear map. The proof uses a genuine finite polynomial operation. -/
theorem contDiffAt_compContinuousLinearMap
    (ha : ContDiffAt ℝ ∞ a x) (hL : ContDiffAt ℝ ∞ L x) :
    ContDiffAt ℝ ∞ (fun z ↦ (a z).compContinuousLinearMap (L z)) x := by
  let op : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E →L[ℝ] F)
      (ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ F) ℝ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin k ↦ E) (fun _ : Fin k ↦ F) ℝ
  have hop : ContDiffAt ℝ ∞ op (fun _ ↦ L x) :=
    ContinuousMultilinearMap.contDiffAt (𝕜 := ℝ) (ι := Fin k)
      (E := fun _ : Fin k ↦ E →L[ℝ] F)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ F) ℝ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ)
      (n := ∞) (x := fun _ ↦ L x) op
  have hpi : ContDiffAt ℝ ∞ (fun z : V ↦ (fun _ : Fin k ↦ L z)) x :=
    contDiffAt_pi.mpr (fun _ ↦ hL)
  have hO : ContDiffAt ℝ ∞ (fun z ↦ op (fun _ ↦ L z)) x := hop.comp x hpi
  have hinc : ContDiffAt ℝ ∞
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ :
        ContinuousAlternatingMap ℝ F ℝ (Fin k) →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ F) ℝ) (a x) :=
    ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM
      (𝕜 := ℝ) (E := F) (F := ℝ) (ι := Fin k) ℝ).contDiff (n := ∞)).contDiffAt (x := a x)
  have hA : ContDiffAt ℝ ∞ (fun z ↦ (a z).toContinuousMultilinearMap) x := hinc.comp x ha
  have h := (alternatingProjection (E := E) k).contDiff.contDiffAt.comp x (hO.clm_apply hA)
  change ContDiffAt ℝ ∞
    (fun z ↦ alternatingProjection k ((a z).compContinuousLinearMap (L z)).toContinuousMultilinearMap) x at h
  simpa only [alternatingProjection_toContinuousMultilinearMap] using h

end PolynomialPullback

section ManifoldCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, F) ∞ N] {k : ℕ}

/-- A smooth manifold map expressed through actual source and target charts. -/
def coordinateMap (e : OpenPartialHomeomorph M E) (e' : OpenPartialHomeomorph N F)
    (f : M → N) : E → F := e' ∘ (f ∘ e.symm)

/-- Local smoothness of the coordinate map on its genuine chart domain. -/
theorem coordinateMap_contDiffAt (e : OpenPartialHomeomorph M E)
    (e' : OpenPartialHomeomorph N F)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (y : E) (hy : y ∈ e.target) (hy' : f (e.symm y) ∈ e'.source) :
    ContDiffAt ℝ ∞ (coordinateMap e e' f) y :=
  ((contMDiffAt_of_mem_maximalAtlas he' hy').comp y
    ((hf (e.symm y)).comp y (contMDiffAt_symm_of_mem_maximalAtlas he hy))).contDiffAt

/-- Actual chart-coordinate derivative of a manifold map. -/
theorem coordinateMap_fderiv (e : OpenPartialHomeomorph M E)
    (e' : OpenPartialHomeomorph N F)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (y : E) (hy : y ∈ e.target) (hy' : f (e.symm y) ∈ e'.source) :
    fderiv ℝ (coordinateMap e e' f) y =
      (chartTangentMap e' (f (e.symm y))).comp
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (e.symm y)).comp (inverseChartTangentMap e y)) := by
  have hdInv := (contMDiffAt_symm_of_mem_maximalAtlas he hy).mdifferentiableAt (by simp)
  have hdF := (hf (e.symm y)).mdifferentiableAt (by simp)
  have hinner := mfderiv_comp y hdF hdInv
  have houter := mfderiv_comp y
    ((contMDiffAt_of_mem_maximalAtlas he' hy').mdifferentiableAt (by simp))
    (hdF.comp y hdInv)
  rw [mfderiv_eq_fderiv, hinner] at houter
  ext v
  exact congrArg (fun L ↦ L v) houter

/-- A genuine manifold pullback is the ordinary derivative pullback in every
compatible pair of charts, on their actual domain. -/
theorem chartRepresentation_pullback (e : OpenPartialHomeomorph M E)
    (e' : OpenPartialHomeomorph N F)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (α : Form 𝓘(ℝ, F) N k) (y : E)
    (hy : y ∈ e.target) (hy' : f (e.symm y) ∈ e'.source) :
    chartRepresentation e (pullback (I := 𝓘(ℝ, E)) f α) y =
      (chartRepresentation e' α (coordinateMap e e' f y)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap e e' f) y) := by
  rw [coordinateMap_fderiv e e' he he' f hf y hy hy']
  calc
    chartRepresentation e (pullback (I := 𝓘(ℝ, E)) f α) y =
        (α (f (e.symm y))).compContinuousLinearMap
          ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (e.symm y)).comp (inverseChartTangentMap e y)) := by
      ext v; rfl
    _ = ((chartRepresentation e' α (e' (f (e.symm y)))).compContinuousLinearMap
        (chartTangentMap e' (f (e.symm y)))).compContinuousLinearMap
          ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (e.symm y)).comp (inverseChartTangentMap e y)) := by
      rw [chartRepresentation_recover e' he' α (f (e.symm y)) hy']
    _ = _ := by ext v; rfl

/-- The chartwise pullback identity holds on a whole neighborhood, with chart
domains justified by continuity of the actual map and the inverse chart. -/
theorem chartRepresentation_pullback_eventuallyEq (e : OpenPartialHomeomorph M E)
    (e' : OpenPartialHomeomorph N F)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (α : Form 𝓘(ℝ, F) N k) (y : E)
    (hy : y ∈ e.target) (hy' : f (e.symm y) ∈ e'.source) :
    chartRepresentation e (pullback (I := 𝓘(ℝ, E)) f α) =ᶠ[𝓝 y]
      (fun z ↦ (chartRepresentation e' α (coordinateMap e e' f z)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap e e' f) z)) := by
  have hpre : (f ∘ e.symm) ⁻¹' e'.source ∈ 𝓝 y :=
    (hf.continuous.continuousAt.comp (e.continuousAt_symm hy)).preimage_mem_nhds
      (e'.open_source.mem_nhds hy')
  filter_upwards [e.open_target.mem_nhds hy, hpre] with z hz hz'
  exact chartRepresentation_pullback e e' he he' f hf α z hz hz'

/-- Pullback by any smooth map of manifolds preserves actual smoothness of
forms, even when the domain and codomain have different model dimensions. -/
theorem IsSmooth.pullback {α : Form 𝓘(ℝ, F) N k} (hα : IsSmooth α)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    IsSmooth (pullback (I := 𝓘(ℝ, E)) f α) := by
  intro e he y hy
  let e' := chartAt F (f (e.symm y))
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N :=
    IsManifold.chart_mem_maximalAtlas (f (e.symm y))
  have hy' : f (e.symm y) ∈ e'.source := mem_chart_source F (f (e.symm y))
  have hc := coordinateMap_contDiffAt e e' he he' f hf y hy hy'
  have ha : ContDiffAt ℝ ∞ (chartRepresentation e' α) (coordinateMap e e' f y) :=
    (hα e' he').contDiffAt (e'.open_target.mem_nhds (e'.map_source hy'))
  have hpoly := contDiffAt_compContinuousLinearMap (ha.comp y hc)
    (hc.fderiv_right (m := ∞) (by simp))
  exact (hpoly.congr_of_eventuallyEq
    (chartRepresentation_pullback_eventuallyEq e e' he he' f hf α y hy hy')).contDiffWithinAt

/-- In coordinates, differentiating a manifold pullback is the Euclidean
exterior derivative pullback rule, proved on a genuine open neighborhood. -/
theorem extDeriv_chartRepresentation_pullback (e : OpenPartialHomeomorph M E)
    (e' : OpenPartialHomeomorph N F)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (α : Form 𝓘(ℝ, F) N k) (hα : IsSmooth α) (y : E)
    (hy : y ∈ e.target) (hy' : f (e.symm y) ∈ e'.source) :
    extDeriv (chartRepresentation e (pullback (I := 𝓘(ℝ, E)) f α)) y =
      (extDeriv (chartRepresentation e' α) (coordinateMap e e' f y)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap e e' f) y) := by
  rw [(chartRepresentation_pullback_eventuallyEq e e' he he' f hf α y hy hy').extDeriv_eq]
  have ha : ContDiffAt ℝ ∞ (chartRepresentation e' α) (coordinateMap e e' f y) :=
    (hα e' he').contDiffAt (e'.open_target.mem_nhds (e'.map_source hy'))
  exact extDeriv_pullback (ha.differentiableAt (by simp))
    (coordinateMap_contDiffAt e e' he he' f hf y hy hy') (by simp)

/-- The source coordinate tangent map cancels the inverse-chart derivative in
the coordinate expression for the derivative of a manifold map. -/
theorem coordinateMap_fderiv_chartTangentMap (e : OpenPartialHomeomorph M E)
    (e' : OpenPartialHomeomorph N F)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (x : M) (hx : x ∈ e.source) (hx' : f x ∈ e'.source)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    fderiv ℝ (coordinateMap e e' f) (e x) (chartTangentMap e x v) =
      chartTangentMap e' (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x v) := by
  have hsource : f (e.symm (e x)) ∈ e'.source := by simpa only [e.left_inv hx] using hx'
  rw [coordinateMap_fderiv e e' he he' f hf (e x) (e.map_source hx) hsource]
  change chartTangentMap e' (f (e.symm (e x)))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (e.symm (e x))
        (inverseChartTangentMap e (e x) (chartTangentMap e x v))) = _
  rw [inverseChartTangentMap_chartTangentMap e he x hx]
  exact congrArg (fun z : M ↦ (show F from chartTangentMap e' (f z)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z (show TangentSpace 𝓘(ℝ, E) z from v)))) (e.left_inv hx)

/-- Exterior differentiation commutes with pullback by any smooth manifold map.
Every object is the actual form, derivative, and map; no naturality premise is assumed. -/
theorem pullback_exteriorDerivative (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (α : Form 𝓘(ℝ, F) N k) (hα : IsSmooth α) :
    pullback (I := 𝓘(ℝ, E)) f (exteriorDerivative α) =
      exteriorDerivative (pullback (I := 𝓘(ℝ, E)) f α) := by
  funext x
  let e := chartAt E x
  let e' := chartAt F (f x)
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N := IsManifold.chart_mem_maximalAtlas (f x)
  have hx : x ∈ e.source := mem_chart_source E x
  have hx' : f x ∈ e'.source := mem_chart_source F (f x)
  have hsource : f (e.symm (e x)) ∈ e'.source := by simpa only [e.left_inv hx] using hx'
  change (exteriorDerivative α (f x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) =
    exteriorDerivative (pullback (I := 𝓘(ℝ, E)) f α) x
  rw [exteriorDerivative_eq_chartDerivative α hα e' he' (f x) hx',
    exteriorDerivative_eq_chartDerivative (pullback (I := 𝓘(ℝ, E)) f α)
      (hα.pullback f hf) e he x hx]
  unfold chartDerivative
  rw [extDeriv_chartRepresentation_pullback e e' he he' f hf α hα (e x) (e.map_source hx) hsource]
  have hpoint : coordinateMap e e' f (e x) = e' (f x) := by
    simp only [coordinateMap, Function.comp_apply, e.left_inv hx]
  rw [hpoint]
  ext v
  change (extDeriv (chartRepresentation e' α) (e' (f x)))
      (fun j ↦ chartTangentMap e' (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x (v j))) =
    (extDeriv (chartRepresentation e' α) (e' (f x)))
      (fun j ↦ fderiv ℝ (coordinateMap e e' f) (e x) (chartTangentMap e x (v j)))
  congr 1
  funext j
  exact (coordinateMap_fderiv_chartTangentMap e e' he he' f hf x hx hx' (v j)).symm

end ManifoldCoordinates
end GaussBonnetChern.DifferentialForm






