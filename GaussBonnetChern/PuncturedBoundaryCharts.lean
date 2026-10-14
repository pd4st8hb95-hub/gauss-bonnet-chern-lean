import GaussBonnetChern.RadialBoundaryCharts
import Mathlib.Topology.Algebra.Group.ContinuousDiv
noncomputable section
open Set Metric TopologicalSpace
open scoped ContDiff Manifold
namespace GaussBonnetChern.RadialBoundaryCharts
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
-- Candidate centered and localized charts. These represent actual deleted balls.
-- Insert into RadialBoundaryCharts namespace after radialEuclideanChart.

variable {M : Type*} [TopologicalSpace M]

def centeredRadialChart {d : ℕ} (e : OpenPartialHomeomorph M E) (center : E)
    (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d))) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))) :=
  e.trans ((Homeomorph.subRight center).toOpenPartialHomeomorph.trans
    (radialEuclideanChart r hr u c))

theorem centeredRadialChart_height {d : ℕ} (e : OpenPartialHomeomorph M E) (center : E)
    (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ (centeredRadialChart e center r hr u c).source) :
    centeredRadialChart e center r hr u c x 0 = ‖e x - center‖ - r := by
  have hx' : e x - center ∈ (radialEuclideanChart r hr u c).source := hx.2.2
  exact radialEuclideanChart_height r hr u c (e x - center) hx'

theorem centeredRadialChart_domain {d : ℕ} (e : OpenPartialHomeomorph M E) (center : E)
    (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ (centeredRadialChart e center r hr u c).source) :
    x ∉ PuncturedManifold.coordinateBall e center r ↔
      0 ≤ centeredRadialChart e center r hr u c x 0 := by
  rw [centeredRadialChart_height e center r hr u c x hx]
  have hxs : x ∈ e.source := hx.1
  simp [PuncturedManifold.coordinateBall, hxs, mem_ball, dist_eq_norm, sub_nonneg]

variable [ProperSpace E] [T2Space M] {ι : Type*} [Fintype ι]

def puncturedBoundaryChart {d : ℕ}
    (e : ι → OpenPartialHomeomorph M E) (center : ι → E) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hcover : ∀ i, closedBall (center i) (r i) ⊆ (e i).target)
    (i : ι) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d))) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))) :=
  (centeredRadialChart (e i) (center i) (r i) (hr i) u c).restrOpen
    (PuncturedManifold.otherBallExterior e center r i)
    (PuncturedManifold.isOpen_otherBallExterior e center r hcover i)

theorem puncturedBoundaryChart_domain {d : ℕ}
    (e : ι → OpenPartialHomeomorph M E) (center : ι → E) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hcover : ∀ i, closedBall (center i) (r i) ⊆ (e i).target)
    (i : ι) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ (puncturedBoundaryChart e center r hr hcover i u c).source) :
    x ∈ PuncturedManifold.puncturedDomain e center r ↔
      0 ≤ puncturedBoundaryChart e center r hr hcover i u c x 0 := by
  rw [PuncturedManifold.puncturedDomain_local_iff e center r i x hx.2]
  exact centeredRadialChart_domain (e i) (center i) (r i) (hr i) u c x hx.1

end GaussBonnetChern.RadialBoundaryCharts