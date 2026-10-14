import GaussBonnetChern.GenericFormIntegration
import GaussBonnetChern.FormIntegration

/-! # Agreement with the frozen even-dimensional coordinate integral

Both equalities are definitional. This adapter keeps the Levi-Civita and
even-dimensional geometric imports out of the sphere integral infrastructure.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GaussBonnetChern.GenericFormIntegration

variable {n : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (Model n) N]
  [IsManifold (model n) ∞ N]

theorem coefficient_even (e : OpenPartialHomeomorph N (Model n))
    (α : DifferentialForm.Form (model n) N (2*n)) :
    coefficient e α = topFormCoefficient e α := rfl

theorem integral_even (a : FiniteOrientedAtlas n N)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) N Set.univ)
    (α : DifferentialForm.Form (model n) N (2*n)) :
    integral a.chart (fun i ↦ ρ i) α = integralTopForm a ρ α := rfl

end GaussBonnetChern.GenericFormIntegration
