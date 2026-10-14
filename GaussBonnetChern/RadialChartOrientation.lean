import GaussBonnetChern.RadialBoundaryJacobian

noncomputable section
open Set Metric Module Filter
open scoped ContDiff Manifold Topology
namespace GaussBonnetChern.RadialBoundaryCharts
variable {d : ℕ}
local instance euclideanFact : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d+1))) = d+1) :=
  ⟨finrank_euclideanSpace_fin⟩
variable (r : ℝ) (hr : 0 < r)
  (u : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
  (c : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
    (EuclideanSpace ℝ (Fin d)))
  (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1))

theorem radialEuclideanChart_symm_eq_collarMap
    (z : EuclideanSpace ℝ (Fin (d+1))) (hz : -r < z 0) :
    (radialEuclideanChart r hr u c).symm z = collarCoordinateMap r c z := by
  change (radialProductChart r hr u c).symm ((heightFirstEquiv d).symm z) = _
  have h := radialProductChart_symm r hr u c ((heightFirstEquiv d).symm z).1
    ((heightFirstEquiv d).symm z).2 hz
  exact h

include hc

theorem hasFDerivAt_radialEuclideanChart_symm
    (z : EuclideanSpace ℝ (Fin (d+1)))
    (hz : z ∈ (radialEuclideanChart r hr u c).target) :
    HasFDerivAt (radialEuclideanChart r hr u c).symm (collarCoordinateDerivative r c z) z := by
  have ht : (heightFirstEquiv d).symm z ∈ (radialProductChart r hr u c).target := hz.2
  rw [radialProductChart_target] at ht
  have hy : sphereCoordinateLinear d z ∈ c.target := ht.1
  have hh : -r < z 0 := ht.2
  have heq : (radialEuclideanChart r hr u c).symm =ᶠ[𝓝 z] collarCoordinateMap r c := by
    have h0 : Continuous (fun w : EuclideanSpace ℝ (Fin (d+1)) ↦ w 0) :=
      PiLp.continuous_apply 2 (fun _ : Fin (d+1) ↦ ℝ) 0
    filter_upwards [(isOpen_Ioi.preimage h0).mem_nhds hh] with w hw
    exact radialEuclideanChart_symm_eq_collarMap r hr u c w hw
  exact (hasFDerivAt_collarCoordinateMap r c hc z hy).congr_of_eventuallyEq heq

theorem radialEuclideanChart_inverse_det_pos
    (hp : ∀ y ∈ c.target,
      0 < sphereChartDensity (EuclideanSpace.basisFun (Fin (d+1)) ℝ) c y)
    (z : EuclideanSpace ℝ (Fin (d+1)))
    (hz : z ∈ (radialEuclideanChart r hr u c).target) :
    0 < (fderiv ℝ (radialEuclideanChart r hr u c).symm z).det := by
  rw [(hasFDerivAt_radialEuclideanChart_symm r hr u c hc z hz).fderiv]
  have ht : (heightFirstEquiv d).symm z ∈ (radialProductChart r hr u c).target := hz.2
  rw [radialProductChart_target] at ht
  have hy : sphereCoordinateLinear d z ∈ c.target := ht.1
  apply det_collarCoordinateDerivative_pos r c hc z hy
  · have hh : -r < z 0 := ht.2
    linarith
  · exact hp _ hy

theorem radialEuclideanChart_forward_det_pos
    (hp : ∀ y ∈ c.target,
      0 < sphereChartDensity (EuclideanSpace.basisFun (Fin (d+1)) ℝ) c y)
    (x : EuclideanSpace ℝ (Fin (d+1)))
    (hx : x ∈ (radialEuclideanChart r hr u c).source) :
    0 < (fderiv ℝ (radialEuclideanChart r hr u c) x).det := by
  let e := radialEuclideanChart r hr u c
  change 0 < (fderiv ℝ e x).det
  have hforward : DifferentiableAt ℝ e x :=
    ((contDiffOn_radialEuclideanChart r hr u c hc).contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hinverse : DifferentiableAt ℝ e.symm (e x) :=
    (hasFDerivAt_radialEuclideanChart_symm r hr u c hc (e x) (e.map_source hx)).differentiableAt
  have hcomp := hinverse.hasFDerivAt.comp x hforward.hasFDerivAt
  have heq : (e.symm ∘ e) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hid : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ _ := by
    rw [← hcomp.fderiv, heq.fderiv_eq]
    exact fderiv_id
  have hdet : (fderiv ℝ e.symm (e x)).det * (fderiv ℝ e x).det = 1 := by
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin (d+1)) →L[ℝ] EuclideanSpace ℝ (Fin (d+1)) ↦ L.det) hid
    simpa [ContinuousLinearMap.det, LinearMap.det_comp] using h
  have hpos := radialEuclideanChart_inverse_det_pos r hr u c hc hp (e x) (e.map_source hx)
  by_contra hn
  have hnon := mul_nonpos_of_nonneg_of_nonpos hpos.le (le_of_not_gt hn)
  rw [hdet] at hnon
  norm_num at hnon

end GaussBonnetChern.RadialBoundaryCharts
