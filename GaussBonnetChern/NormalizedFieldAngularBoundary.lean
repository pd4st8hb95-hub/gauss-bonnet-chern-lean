import GaussBonnetChern.NormalizedFieldTransgression
import GaussBonnetChern.ChernLocalIndexLimit
import GaussBonnetChern.BoundarySphereTrace

/-! # The actual sphere trace of the normalized-field transgression

This module identifies the original local-index boundary form with the sphere
pullback of the same ambient angular form used in punctured Stokes.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern
open DifferentialForm StokesLocalization
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] [Fact (0<n)]

/-- The local-index boundary form is the actual sphere trace of the same
ambient form used in punctured Stokes. -/
theorem positiveChartAngularBoundary_eq_ambient_pullback
    (a : FiniteOrientedAtlas n M) (i : Fin a.card)
    (X : (x : M) → TangentSpace (model n) x)
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X)) (p : M) (r : ℝ)
    (hr : 0 < r)
    (hcover : closedBall ((a.chart i) p) r ⊆ (a.chart i).target)
    (hnz : ∀ u : sphere (0 : Model n) 1,
      X (centeredInverseChart n M (a.chart i) p (r • (u : Model n))) ≠ 0) :
    ChernLocalIndex.positiveChartAngularBoundary n M a i X p r =
      pullback (I := 𝓡 (2*n-1))
        (BoundarySphereTrace.sphereEmbedding (a.chart i) ((a.chart i) p) r)
        (normalizedFieldAngularForm n M a X hX) := by
  classical
  let F := BoundarySphereTrace.sphereEmbedding (a.chart i) ((a.chart i) p) r
  have hF : ContMDiff (𝓡 (2*n-1)) (model n) ∞ F := by
    intro u
    have ht : (a.chart i) p + r • (u : Model n) ∈ (a.chart i).target :=
      hcover (BoundarySphereTrace.centered_sphere_mem_closedBall _ r hr u)
    have hcoord : ContMDiffAt (𝓡 (2*n-1)) (model n) ∞
        (fun v : sphere (0 : Model n) 1 ↦ (a.chart i) p + r • (v : Model n)) u := by
      have ha : ContDiffAt ℝ ∞
          (fun z : Model n ↦ (a.chart i) p + r • z) (u : Model n) :=
        contDiffAt_const.add (contDiffAt_id.const_smul r)
      have hm : ContMDiffAt (model n) (model n) ∞
          (fun z : Model n ↦ (a.chart i) p + r • z) (u : Model n) := ha.contMDiffAt
      exact hm.comp u (contMDiff_coe_sphere (n := 2*n-1) (m := ∞) u)
    exact (contMDiffAt_symm_of_mem_maximalAtlas (a.smooth i) ht).comp u hcoord
  rw [ChernLocalIndex.positiveChartAngularBoundary, dif_pos hnz]
  exact (pullback_normalizedFieldAngularForm n M a X hX F hF hnz).symm

end GaussBonnetChern
