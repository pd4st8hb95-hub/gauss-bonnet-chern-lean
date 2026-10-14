import GaussBonnetChern.PuncturedBoundaryCharts
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Smoothness of the actual punctured boundary charts

The charts are the concrete ambient chart, translation, radial chart, and
restriction constructed previously. Smoothness is proved on both domains,
rather than stored as an assumed property of a boundary structure.
-/

noncomputable section
open Set Metric TopologicalSpace
open scoped Manifold ContDiff Topology
namespace GaussBonnetChern.RadialBoundaryCharts

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (d+1))) M] [IsManifold (𝓡 (d+1)) ∞ M]

local instance euclideanBoundaryFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d+1))) = d+1) := ⟨finrank_euclideanSpace_fin⟩

theorem contMDiffOn_centeredRadialChart
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 (d+1)) ∞ M)
    (center : EuclideanSpace ℝ (Fin (d+1))) (r : ℝ) (hr : 0 < r)
    (u : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
    (c : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
      (EuclideanSpace ℝ (Fin d)))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)) :
    ContMDiffOn (𝓡 (d+1)) (𝓡 (d+1)) ∞ (centeredRadialChart e center r hr u c)
      (centeredRadialChart e center r hr u c).source := by
  intro x hx
  have hxE : x ∈ e.source := hx.1
  have hxR : e x - center ∈ (radialEuclideanChart r hr u c).source := hx.2.2
  have hE := contMDiffAt_of_mem_maximalAtlas he hxE
  have hT : ContMDiffAt (𝓡 (d+1)) (𝓡 (d+1)) ∞
      (fun z : EuclideanSpace ℝ (Fin (d+1)) ↦ z - center) (e x) :=
    (contDiffAt_id.sub contDiffAt_const).contMDiffAt
  have hR := ((contDiffOn_radialEuclideanChart r hr u c hc).contDiffAt
    ((radialEuclideanChart r hr u c).open_source.mem_nhds hxR)).contMDiffAt
  exact (hR.comp x (hT.comp x hE)).contMDiffWithinAt

theorem contMDiffOn_centeredRadialChart_symm
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 (d+1)) ∞ M)
    (center : EuclideanSpace ℝ (Fin (d+1))) (r : ℝ) (hr : 0 < r)
    (u : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
    (c : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
      (EuclideanSpace ℝ (Fin d)))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)) :
    ContMDiffOn (𝓡 (d+1)) (𝓡 (d+1)) ∞ (centeredRadialChart e center r hr u c).symm
      (centeredRadialChart e center r hr u c).target := by
  intro y hy
  have hy' : y ∈ (radialEuclideanChart r hr u c).target ∧
      (radialEuclideanChart r hr u c).symm y + center ∈ e.target := by
    exact ⟨hy.1.1, hy.2⟩
  have hR := ((contDiffOn_radialEuclideanChart_symm r hr u c hc).contDiffAt
    ((radialEuclideanChart r hr u c).open_target.mem_nhds hy'.1)).contMDiffAt
  have hT : ContMDiffAt (𝓡 (d+1)) (𝓡 (d+1)) ∞
      (fun z : EuclideanSpace ℝ (Fin (d+1)) ↦ z + center)
      ((radialEuclideanChart r hr u c).symm y) :=
    (contDiffAt_id.add contDiffAt_const).contMDiffAt
  have hE := contMDiffAt_symm_of_mem_maximalAtlas he hy'.2
  exact (hE.comp y (hT.comp y hR)).contMDiffWithinAt

theorem centeredRadialChart_mem_maximalAtlas
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 (d+1)) ∞ M)
    (center : EuclideanSpace ℝ (Fin (d+1))) (r : ℝ) (hr : 0 < r)
    (u : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
    (c : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
      (EuclideanSpace ℝ (Fin d)))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)) :
    centeredRadialChart e center r hr u c ∈ IsManifold.maximalAtlas (𝓡 (d+1)) ∞ M :=
  (centeredRadialChart e center r hr u c).mem_maximalAtlas_of_contMDiffOn
    (contMDiffOn_centeredRadialChart e he center r hr u c hc)
    (contMDiffOn_centeredRadialChart_symm e he center r hr u c hc)

/-- Restriction is proved for an abstract chart before it is specialized to
the large concrete collar composition. This keeps the kernel conversion small. -/
theorem radial_restrOpen_mem_maximalAtlas
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 (d+1)) ∞ M)
    (U : Set M) (hU : IsOpen U) :
    e.restrOpen U hU ∈ IsManifold.maximalAtlas (𝓡 (d+1)) ∞ M := by
  apply (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).mpr
  constructor
  · change ContMDiffOn (𝓡 (d+1)) (𝓡 (d+1)) ∞ e (e.source ∩ U)
    exact (contMDiffOn_of_mem_maximalAtlas he).mono inter_subset_left
  · change ContMDiffOn (𝓡 (d+1)) (𝓡 (d+1)) ∞ e.symm (e.target ∩ e.symm ⁻¹' U)
    exact (contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left

theorem puncturedBoundaryChart_mem_maximalAtlas [T2Space M] {ι : Type*} [Fintype ι]
    (e : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))))
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas (𝓡 (d+1)) ∞ M)
    (center : ι → EuclideanSpace ℝ (Fin (d+1))) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (e i).target)
    (i : ι) (u : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
    (c : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
      (EuclideanSpace ℝ (Fin d)))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)) :
    puncturedBoundaryChart e center r hr hcover i u c ∈ IsManifold.maximalAtlas (𝓡 (d+1)) ∞ M := by
  have hg := centeredRadialChart_mem_maximalAtlas (e i) (he i) (center i) (r i) (hr i) u c hc
  exact radial_restrOpen_mem_maximalAtlas
    (centeredRadialChart (e i) (center i) (r i) (hr i) u c) hg
    (PuncturedManifold.otherBallExterior e center r i)
    (PuncturedManifold.isOpen_otherBallExterior e center r hcover i)

end GaussBonnetChern.RadialBoundaryCharts
