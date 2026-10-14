import GaussBonnetChern.PuncturedBoundarySmoothness
import GaussBonnetChern.RadialChartOrientation
import GaussBonnetChern.Geometry

/-! Positive orientation of the actual smooth punctured boundary charts. -/

noncomputable section
open Set Metric TopologicalSpace
open scoped Manifold ContDiff Topology
namespace GaussBonnetChern.RadialBoundaryCharts

section EvenDimension
variable {n : ℕ} {N : Type*} [TopologicalSpace N] [T2Space N]
  [ChartedSpace (Model (n+1)) N] [IsManifold (model (n+1)) ∞ N]

local instance evenBoundaryDimension :
    Fact (Module.finrank ℝ (Model (n+1)) = (2*n+1)+1) :=
  ⟨by simp [Model, Nat.mul_add, Nat.add_assoc]⟩

local instance evenEuclideanBoundaryDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2*n+1+1))) = 2*n+1+1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Positive outward sphere charts induce positive ambient radial charts,
also relative to every chart of the originally chosen orientation. -/
theorem puncturedBoundaryChart_positive_cross {ι : Type*} [Fintype ι]
    (a : FiniteOrientedAtlas (n+1) N) (chartIndex : ι → Fin a.card)
    (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (chartIndex i)).target)
    (i : ι) (u : sphere (0 : Model (n+1)) 1)
    (c : OpenPartialHomeomorph (sphere (0 : Model (n+1)) 1)
      (EuclideanSpace ℝ (Fin (2*n+1))))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 (2*n+1)) ∞ (sphere (0 : Model (n+1)) 1))
    (hp : ∀ y ∈ c.target,
      0 < sphereChartDensity (EuclideanSpace.basisFun (Fin (2*n+1+1)) ℝ) c y)
    (k : Fin a.card) (x : N) (hxk : x ∈ (a.chart k).source)
    (hxp : x ∈ (puncturedBoundaryChart (fun j ↦ a.chart (chartIndex j))
      center r hr hcover i u c).source) :
    0 < LinearMap.det (fderiv ℝ
      (puncturedBoundaryChart (fun j ↦ a.chart (chartIndex j)) center r hr hcover i u c ∘
        (a.chart k).symm) (a.chart k x)).toLinearMap := by
  let q := a.chart (chartIndex i)
  let p := a.chart k
  let R := radialEuclideanChart (r i) (hr i) u c
  let F : Model (n+1) → Model (n+1) := fun y ↦ q (p.symm y)
  let y := p x
  have hxq : x ∈ q.source := hxp.1.1
  have hxR : q x - center i ∈ R.source := hxp.1.2.2
  have hq : ContMDiffAt (model (n+1)) (model (n+1)) ∞ q (p.symm y) := by
    simpa only [y, p.left_inv hxk] using contMDiffAt_of_mem_maximalAtlas (a.smooth (chartIndex i)) hxq
  have hF : ContDiffAt ℝ ∞ F y :=
    (hq.comp y (contMDiffAt_symm_of_mem_maximalAtlas (a.smooth k) (p.map_source hxk))).contDiffAt
  have hFR : F y - center i ∈ R.source := by simpa only [F, y, p.left_inv hxk] using hxR
  have hR : HasFDerivAt R (fderiv ℝ R (F y - center i)) (F y - center i) :=
    (((contDiffOn_radialEuclideanChart (r i) (hr i) u c hc).contDiffAt
      (R.open_source.mem_nhds hFR)).differentiableAt (by simp)).hasFDerivAt
  have hfd : fderiv ℝ
      (puncturedBoundaryChart (fun j ↦ a.chart (chartIndex j)) center r hr hcover i u c ∘ p.symm) y =
        (fderiv ℝ R (F y - center i)).comp (fderiv ℝ F y) :=
    (hR.comp y ((hF.differentiableAt (by simp)).hasFDerivAt.sub_const (center i))).fderiv
  have hRpos : 0 < (fderiv ℝ R (F y - center i)).det :=
    radialEuclideanChart_forward_det_pos (r i) (hr i) u c hc hp (F y - center i) hFR
  have hFpos : 0 < (fderiv ℝ F y).det :=
    a.positive_transition k (chartIndex i) x hxk hxq
  change 0 < (fderiv ℝ
    (puncturedBoundaryChart (fun j ↦ a.chart (chartIndex j)) center r hr hcover i u c ∘ p.symm) y).det
  rw [hfd]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
  exact mul_pos hRpos hFpos

end EvenDimension

end GaussBonnetChern.RadialBoundaryCharts
