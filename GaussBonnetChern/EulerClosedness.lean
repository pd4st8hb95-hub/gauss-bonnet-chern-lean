import GaussBonnetChern.ExteriorDerivative
import GaussBonnetChern.EulerIntegral
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Top-degree forms are closed because their exterior derivatives have
more alternating arguments than the dimension of the actual chart model.
No compactness, connectedness, or closedness premise is needed. -/

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace GaussBonnetChern.DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An alternating map above the dimension vanishes on every tuple, since
that tuple is linearly dependent. -/
theorem continuousAlternatingMap_eq_zero_of_finrank_lt {k : ℕ}
    (hk : Module.finrank ℝ E < k) (A : ContinuousAlternatingMap ℝ E ℝ (Fin k)) :
    A = 0 := by
  ext v
  apply A.toAlternatingMap.map_linearDependent v
  intro h
  have hcard := h.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

variable {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  [IsManifold 𝓘(ℝ,E) ∞ P]

/-- Exterior differentiation of any top-degree form is zero. This applies
to the project's actual chart-coordinate derivative, even without a
smoothness premise on the form. -/
theorem exteriorDerivative_eq_zero_of_topDegree {k : ℕ}
    (hk : Module.finrank ℝ E = k) (α : Form 𝓘(ℝ,E) P k) :
    exteriorDerivative α = 0 := by
  funext x
  have hzero : extDeriv (chartRepresentation (chartAt E x) α) ((chartAt E x) x) = 0 :=
    continuousAlternatingMap_eq_zero_of_finrank_lt (by omega) _
  change (extDeriv (chartRepresentation (chartAt E x) α) ((chartAt E x) x)).compContinuousLinearMap
    (chartTangentMap (chartAt E x) x) = 0
  ext v
  exact congrArg (fun A : ContinuousAlternatingMap ℝ E ℝ (Fin (k+1)) ↦
    A (fun j ↦ chartTangentMap (chartAt E x) x (v j))) hzero

end GaussBonnetChern.DifferentialForm

namespace GaussBonnetChern
open DifferentialForm
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

/-- Every actual top form on a real `2*n`-dimensional manifold is closed,
including the zero-dimensional case and the empty manifold. -/
theorem exteriorDerivative_topForm (α : Form (model n) M (2*n)) :
    exteriorDerivative α = 0 :=
  exteriorDerivative_eq_zero_of_topDegree (by simp [Model]) α

variable [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

/-- The actual atlas Euler curvature form is closed by its top degree. -/
theorem exteriorDerivative_atlasEulerForm (a : FiniteOrientedAtlas n M) (hn : 0<n) :
    exteriorDerivative (atlasEulerForm n M a hn) = 0 :=
  exteriorDerivative_topForm n M (atlasEulerForm n M a hn)

end GaussBonnetChern
