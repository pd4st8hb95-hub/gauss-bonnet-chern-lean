import GaussBonnetChern.DifferentialForms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Coordinate integrals of top forms in arbitrary dimension

The definition is the literal weighted finite sum of chart integrals. Smoothness,
subordination and orientation are hypotheses of comparison theorems; they are
not silently included in a scalar chosen to be the integral.
-/

noncomputable section
open MeasureTheory
open scoped Manifold BigOperators ContDiff

namespace GaussBonnetChern.GenericFormIntegration

abbrev CoordinateSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (CoordinateSpace d) M]

def coefficient (e : OpenPartialHomeomorph M (CoordinateSpace d))
    (α : DifferentialForm.Form 𝓘(ℝ, CoordinateSpace d) M d) (y : CoordinateSpace d) : ℝ :=
  DifferentialForm.chartRepresentation e α y (EuclideanSpace.basisFun (Fin d) ℝ)

def integral (e : Fin q → OpenPartialHomeomorph M (CoordinateSpace d))
    (ρ : Fin q → M → ℝ) (α : DifferentialForm.Form 𝓘(ℝ, CoordinateSpace d) M d) : ℝ :=
  ∑ i, ∫ y in (e i).target, ρ i ((e i).symm y) * coefficient (e i) α y ∂volume

@[simp] theorem coefficient_zero (e : OpenPartialHomeomorph M (CoordinateSpace d)) :
    coefficient e (0 : DifferentialForm.Form 𝓘(ℝ, CoordinateSpace d) M d) = 0 := rfl

@[simp] theorem coefficient_add (e : OpenPartialHomeomorph M (CoordinateSpace d))
    (α β : DifferentialForm.Form 𝓘(ℝ, CoordinateSpace d) M d) :
    coefficient e (α + β) = coefficient e α + coefficient e β := rfl

@[simp] theorem coefficient_smul (e : OpenPartialHomeomorph M (CoordinateSpace d))
    (c : ℝ) (α : DifferentialForm.Form 𝓘(ℝ, CoordinateSpace d) M d) :
    coefficient e (c • α) = c • coefficient e α := rfl

@[simp] theorem integral_zero (e : Fin q → OpenPartialHomeomorph M (CoordinateSpace d))
    (ρ : Fin q → M → ℝ) : integral e ρ (0 : DifferentialForm.Form 𝓘(ℝ, CoordinateSpace d) M d) = 0 := by
  simp [integral]

end GaussBonnetChern.GenericFormIntegration
