import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import GaussBonnetChern.Pfaffian

/-! # Concrete geometric data and the curvature integral

The model is the whole Euclidean space of dimension `2*n`, so manifolds here
have no boundary. A finite atlas with positive transition Jacobians records a
chosen orientation. The integrand is the scalar form of the Euler curvature
density; chartwise integration uses the positive metric volume density.

All operations below are explicit definitions. Tensoriality of curvature,
independence of the chosen frame, and identification with the global oriented
Pfaffian form are subsequent proof obligations, not hidden structure fields.
-/

noncomputable section

universe u

open Bundle MeasureTheory
open scoped Manifold Topology BigOperators ContDiff

namespace GaussBonnetChern

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n))

abbrev model (n : ℕ) := 𝓘(ℝ, Model n)

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

/-- A chosen orientation represented by a finite smooth, positively compatible
atlas. The empty manifold is allowed, with an atlas of cardinality zero.
The charts belong to the maximal smooth atlas, not just arbitrary homeomorphisms. -/
structure FiniteOrientedAtlas where
  card : ℕ
  chart : Fin card → OpenPartialHomeomorph M (Model n)
  smooth : ∀ i, chart i ∈ IsManifold.maximalAtlas (model n) ∞ M
  covers : ∀ x : M, ∃ i, x ∈ (chart i).source
  positive_transition : ∀ i j (x : M), x ∈ (chart i).source → x ∈ (chart j).source →
    0 < LinearMap.det
      (fderiv ℝ ((chart j) ∘ (chart i).symm) ((chart i) x)).toLinearMap

abbrev SmoothMetric :=
  Bundle.ContMDiffRiemannianMetric (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)

section Metric

variable [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

/-- The actual Mathlib Levi-Civita connection for the registered smooth metric. -/
def connection : CovariantDerivative (model n) (Model n) (TangentSpace (model n) : M → Type _) := by
  letI : IsContMDiffRiemannianBundle (model n) 1 (Model n)
      (TangentSpace (model n) : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  exact CovariantDerivative.leviCivitaConnection (model n) M

/-- Curvature evaluated using the library's local smooth extensions of tangent
vectors. Convention: `R(u,v)w = ∇_u ∇_v w - ∇_v ∇_u w - ∇_[u,v] w`.
No arbitrary curvature tensor is supplied as a parameter. -/
def curvature (x : M) (u v w : TangentSpace (model n) x) : TangentSpace (model n) x :=
  let U := FiberBundle.extend (Model n) (x := x) u
  let V := FiberBundle.extend (Model n) (x := x) v
  let W := FiberBundle.extend (Model n) (x := x) w
  let cov := connection n M
  cov (fun y ↦ cov W y (V y)) x u - cov (fun y ↦ cov W y (U y)) x v -
    cov W x (VectorField.mlieBracket (model n) U V x)

/-- A pointwise orthonormal frame. No global frame or parallelizability is
assumed: this is a separate basis at each point. -/
def orthonormalFrame (x : M) :
    OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x) :=
  (stdOrthonormalBasis ℝ (TangentSpace (model n) x)).reindex
    (finCongr (by change Module.finrank ℝ (Model n) = 2 * n; simp [Model]))

/-- `B a b i j = ⟪R(e_i,e_j)e_b, e_a⟫`; on a unit round sphere the
`B 0 1 0 1` component is positive with this curvature convention. -/
def curvatureComponents (x : M) (a b i j : Fin (2 * n)) : ℝ :=
  inner ℝ
    (curvature n M x (orthonormalFrame n M x i) (orthonormalFrame n M x j)
      (orthonormalFrame n M x b))
    (orthonormalFrame n M x a)

def eulerDensity (x : M) : ℝ := eulerScalar n (curvatureComponents n M x)

/-- Coordinate tangent vectors obtained by differentiating the inverse chart.
Only values inside the chart target are used by the integral. -/
def coordinateVector (e : OpenPartialHomeomorph M (Model n)) (y : Model n)
    (i : Fin (2 * n)) : TangentSpace (model n) (e.symm y) :=
  mfderiv (model n) (model n) e.symm y (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)

/-- The pullback metric matrix in the standard Euclidean coordinate basis. -/
def chartMetric (e : OpenPartialHomeomorph M (Model n)) (y : Model n) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun i j ↦ inner ℝ (coordinateVector n M e y i) (coordinateVector n M e y j)

/-- Positive Riemannian volume density in a chart. -/
def chartVolumeDensity (e : OpenPartialHomeomorph M (Model n)) (y : Model n) : ℝ :=
  Real.sqrt (Matrix.det (chartMetric n M e y))

/-- The weighted chart integrand. -/
def chartIntegrand (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (i : Fin a.card) (y : Model n) : ℝ :=
  ρ i ((a.chart i).symm y) * eulerDensity n M ((a.chart i).symm y) *
    chartVolumeDensity n M (a.chart i) y

/-- A finite chartwise Bochner integral. Restriction to each chart target is
explicit; chart inverses outside their domains do not contribute. -/
def curvatureIntegral (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ) : ℝ :=
  ∑ i, ∫ y in (a.chart i).target, chartIntegrand n M a ρ i y ∂volume

end Metric

end GaussBonnetChern
