import GaussBonnetChern.ExteriorSmoothLinear

/-! # Exterior differentiation with local coordinate hypotheses

These are pointwise identities for the genuine chart derivative and the actual
globally defined exterior derivative. No smoothness away from the relevant
coordinate germ is required, so the statements apply to local frame forms.
-/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {k l : ℕ}

/-- Local Leibniz in an arbitrary smooth chart. Only the two coordinate forms
must be differentiable at the point; no global smooth extension is assumed. -/
theorem chartDerivative_wedge_apply
    (e : OpenPartialHomeomorph M E) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (α : Form 𝓘(ℝ, E) M k) (β : Form 𝓘(ℝ, E) M l)
    (x : M) (hx : x ∈ e.source)
    (hA : DifferentiableAt ℝ (chartRepresentation e α) (e x))
    (hB : DifferentiableAt ℝ (chartRepresentation e β) (e x))
    (v : Fin (k+l+1) → TangentSpace 𝓘(ℝ, E) x) :
    chartDerivative e (wedge α β) x v =
      wedgeFiber (chartDerivative e α x) (β x)
        (v ∘ finCongr (show k+1+l = k+l+1 by omega)) +
      (-1 : ℝ)^k * wedgeFiber (α x) (chartDerivative e β x)
        (v ∘ finCongr (show k+(l+1) = k+l+1 by omega)) := by
  let L := chartTangentMap e x
  have hchart : chartRepresentation e (wedge α β) =
      (fun y ↦ wedgeFiber (chartRepresentation e α y) (chartRepresentation e β y)) := by
    funext y
    exact chartRepresentation_wedge e α β y
  change extDeriv (chartRepresentation e (wedge α β)) (e x) (L ∘ v) = _
  rw [hchart, extDeriv_wedgeFiber hA hB]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    degreeCastCLM_apply, smul_eq_mul]
  rw [← chartRepresentation_recover e he α x hx, ← chartRepresentation_recover e he β x hx]
  change _ = wedgeFiber
      ((extDeriv (chartRepresentation e α) (e x)).compContinuousLinearMap L)
      ((chartRepresentation e β (e x)).compContinuousLinearMap L)
      (v ∘ finCongr (show k+1+l = k+l+1 by omega)) +
    (-1 : ℝ)^k * wedgeFiber
      ((chartRepresentation e α (e x)).compContinuousLinearMap L)
      ((extDeriv (chartRepresentation e β) (e x)).compContinuousLinearMap L)
      (v ∘ finCongr (show k+(l+1) = k+l+1 by omega))
  rw [← wedgeFiber_compContinuousLinearMap, ← wedgeFiber_compContinuousLinearMap]
  rfl

theorem chartDerivative_wedge
    (e : OpenPartialHomeomorph M E) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (α : Form 𝓘(ℝ, E) M k) (β : Form 𝓘(ℝ, E) M l)
    (x : M) (hx : x ∈ e.source)
    (hA : DifferentiableAt ℝ (chartRepresentation e α) (e x))
    (hB : DifferentiableAt ℝ (chartRepresentation e β) (e x)) :
    chartDerivative e (wedge α β) x =
      degreeCastForm (show k+1+l = k+l+1 by omega)
        (wedge (fun y ↦ chartDerivative e α y) β) x +
      (-1 : ℝ)^k • degreeCastForm (show k+(l+1) = k+l+1 by omega)
        (wedge α (fun y ↦ chartDerivative e β y)) x := by
  ext v
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    degreeCastForm_apply_intrinsic, smul_eq_mul]
  exact chartDerivative_wedge_apply e he α β x hx hA hB v

/-- The actual global definition satisfies Leibniz pointwise under local
differentiability in its centered chart, without a global smoothness hypothesis. -/
theorem exteriorDerivative_wedge_at
    (α : Form 𝓘(ℝ, E) M k) (β : Form 𝓘(ℝ, E) M l) (x : M)
    (hA : DifferentiableAt ℝ (chartRepresentation (chartAt E x) α) (chartAt E x x))
    (hB : DifferentiableAt ℝ (chartRepresentation (chartAt E x) β) (chartAt E x x)) :
    exteriorDerivative (wedge α β) x =
      degreeCastForm (show k+1+l = k+l+1 by omega)
        (wedge (exteriorDerivative α) β) x +
      (-1 : ℝ)^k • degreeCastForm (show k+(l+1) = k+l+1 by omega)
        (wedge α (exteriorDerivative β)) x := by
  ext v
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    degreeCastForm_apply_intrinsic, smul_eq_mul]
  exact chartDerivative_wedge_apply (chartAt E x) (IsManifold.chart_mem_maximalAtlas x)
    α β x (mem_chart_source E x) hA hB v

theorem chartRepresentation_degreeCast {r s : ℕ} (h : r = s)
    (e : OpenPartialHomeomorph M E) (α : Form 𝓘(ℝ, E) M r) :
    chartRepresentation e (degreeCastForm h α) =
      fun y ↦ degreeCastCLM h (chartRepresentation e α y) := by
  subst s
  rfl

theorem chartDerivative_degreeCast {r s : ℕ} (h : r = s)
    (e : OpenPartialHomeomorph M E) (α : Form 𝓘(ℝ, E) M r) (x : M) :
    chartDerivative e (degreeCastForm h α) x =
      degreeCastForm (congrArg (fun j ↦ j+1) h) (fun y ↦ chartDerivative e α y) x := by
  subst s
  rfl

end GaussBonnetChern.DifferentialForm
