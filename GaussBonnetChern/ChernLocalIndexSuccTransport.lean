import GaussBonnetChern.ChernLocalIndexLimit
import GaussBonnetChern.NormalizedFieldAngularBoundary

/-! Exact successor-arity and standard-basis bridge from the actual local
index limit to the actual ambient form used by punctured Stokes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Bundle
open Module Metric Set Filter

namespace GaussBonnetChern.ChernLocalIndexSuccTransport
open DifferentialForm ChernLocalIndex AngularVertical
universe u
variable (k : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model (k+1)) M]
  [IsManifold (model (k+1)) ∞ M]
  [RiemannianBundle (TangentSpace (model (k+1)) : M → Type _)]
  [IsContMDiffRiemannianBundle (model (k+1)) ∞ (Model (k+1))
    (TangentSpace (model (k+1)) : M → Type _)]

local instance successorPositive : Fact (0 < k+1) := ⟨by omega⟩
local instance successorSphereDimension : Fact (finrank ℝ (Model (k+1)) = (2*k+1)+1) :=
  ⟨by simp only [Model, finrank_euclideanSpace, Fintype.card_fin]; omega⟩

theorem successor_angular_arity : 2*(k+1)-1 = 2*k+1 := by omega

/-- For a successor even dimension the sphere arity and the original model
arity are definitionally equal. The equality cast fixes each actual basis
vector; it carries no permutation or orientation sign. -/
theorem standardBasis_reindex_evenSuccEquiv_successor :
    (EuclideanSpace.basisFun (Fin (2*(k+1))) ℝ).reindex
        (evenSuccEquiv (k+1) (by omega)).symm =
      EuclideanSpace.basisFun (Fin (2*(k+1))) ℝ := by
  apply DFunLike.coe_injective
  funext i
  change EuclideanSpace.basisFun (Fin (2*(k+1))) ℝ
      (evenSuccEquiv (k+1) (by omega) i) =
    EuclideanSpace.basisFun (Fin (2*(k+1))) ℝ i
  apply congrArg (EuclideanSpace.basisFun (Fin (2*(k+1))) ℝ)
  apply Fin.ext
  rfl

theorem degreeCast_successor_angular_arity
    (α : Form (model (k+1)) M (2*(k+1)-1)) :
    degreeCastForm (successor_angular_arity k) α = α := by
  rfl

/-- Exact integral identification, retaining the actual normalized section,
the original Euclidean basis and the ambient form used by Stokes. -/
theorem successor_boundary_integral_eq_ambient
    (a : FiniteOrientedAtlas (k+1) M) (i : Fin a.card)
    (X : (x : M) → TangentSpace (model (k+1)) x)
    (hX : ContMDiff (model (k+1)) (model (k+1)).tangent ∞ (T% X))
    (p : M) (r : ℝ) (hr : 0 < r)
    (hcover : closedBall ((a.chart i) p) r ⊆ (a.chart i).target)
    (hnz : ∀ u : sphere (0:Model (k+1)) 1,
      X (centeredInverseChart (k+1) M (a.chart i) p (r • (u:Model (k+1)))) ≠ 0) :
    sphereFormIntegral
      ((EuclideanSpace.basisFun (Fin (2*(k+1))) ℝ).reindex (evenSuccEquiv (k+1) (by omega)).symm)
      (positiveChartAngularBoundary (k+1) M a i X p r) =
    sphereFormIntegral (EuclideanSpace.basisFun (Fin (2*(k+1))) ℝ)
      (pullback (I := 𝓡 (2*k+1))
        (BoundarySphereTrace.sphereEmbedding (a.chart i) ((a.chart i) p) r)
        (degreeCastForm (successor_angular_arity k)
          (normalizedFieldAngularForm (k+1) M a X hX))) := by
  rw [standardBasis_reindex_evenSuccEquiv_successor,
    positiveChartAngularBoundary_eq_ambient_pullback (k+1) M a i X hX p r hr hcover hnz,
    degreeCast_successor_angular_arity]

/-- The local-index limit directly for the same actual ambient angular form
and the same original standard sphere basis used by punctured Stokes. Every
small-sphere validity condition is derived internally from the actual zero.
-/
theorem exists_successor_ambient_boundary_integral_limit
    (a : FiniteOrientedAtlas (k+1) M) {p : M}
    {X : (x : M) → TangentSpace (model (k+1)) x}
    (hX : ContMDiff (model (k+1)) (model (k+1)).tangent ∞ (T% X))
    (hzero : X p = 0) (hi : Function.Injective (fieldLinearization (k+1) M p X)) :
    ∃ i : Fin a.card, p ∈ (a.chart i).source ∧
      Tendsto (fun r => sphereFormIntegral (EuclideanSpace.basisFun (Fin (2*(k+1))) ℝ)
        (pullback (I := 𝓡 (2*k+1))
          (BoundarySphereTrace.sphereEmbedding (a.chart i) ((a.chart i) p) r)
          (degreeCastForm (successor_angular_arity k)
            (normalizedFieldAngularForm (k+1) M a X hX))))
        (𝓝[>] (0:ℝ)) (𝓝 (Real.sign (fieldLinearization (k+1) M p X).det)) := by
  obtain ⟨i, hp, hnz, hlimit⟩ :=
    exists_positiveChartAngularBoundaryIntegral_limit (k+1) M a hX hzero hi
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (a.chart i).open_target _ ((a.chart i).map_source hp)
  have hcover : ∀ᶠ r in 𝓝[>] (0:ℝ),
      closedBall ((a.chart i) p) r ⊆ (a.chart i).target := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    intro y hy
    exact hball (lt_of_le_of_lt hy hr.2)
  refine ⟨i, hp, ?_⟩
  apply hlimit.congr'
  filter_upwards [hnz, hcover, self_mem_nhdsWithin] with r hr hrc hrpos
  exact successor_boundary_integral_eq_ambient k M a i X hX p r hrpos hrc hr

end GaussBonnetChern.ChernLocalIndexSuccTransport
