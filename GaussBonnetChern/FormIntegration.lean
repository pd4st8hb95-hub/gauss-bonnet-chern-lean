import GaussBonnetChern.AtlasIntegration
import GaussBonnetChern.DifferentialForms

/-! # Chartwise integration of actual top-degree forms

The integral is an explicit finite sum of ordinary Lebesgue integrals of the
coordinate coefficient of a genuine alternating form. Independence of atlas
and partition, automatic integrability, and Stokes are subsequent obligations.
-/

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace GaussBonnetChern

open DifferentialForm

/-- Evaluation on a fixed tuple is a bounded linear functional, with the
actual alternating-map operator-norm estimate. -/
def formEvaluation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (v : Fin k → E) : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  let L : (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun α ↦ α v
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  L.mkContinuous (∏ i, ‖v i‖) (fun α ↦ by
    simpa [L, mul_comm] using α.le_opNorm v)

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

/-- The actual coefficient of a top-degree form in an oriented chart. -/
def topFormCoefficient (e : OpenPartialHomeomorph M (Model n))
    (α : Form (model n) M (2 * n)) (y : Model n) : ℝ :=
  chartRepresentation e α y (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)

theorem contDiffOn_topFormCoefficient (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (α : Form (model n) M (2 * n)) (hα : IsSmooth α) :
    ContDiffOn ℝ ∞ (topFormCoefficient e α) e.target :=
  (formEvaluation (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)).contDiff.comp_contDiffOn
    (hα e he)

@[simp] theorem topFormCoefficient_zero (e : OpenPartialHomeomorph M (Model n)) :
    topFormCoefficient e (0 : Form (model n) M (2 * n)) = 0 := rfl

@[simp] theorem topFormCoefficient_add (e : OpenPartialHomeomorph M (Model n))
    (α β : Form (model n) M (2 * n)) :
    topFormCoefficient e (α + β) = topFormCoefficient e α + topFormCoefficient e β := rfl

@[simp] theorem topFormCoefficient_smul (e : OpenPartialHomeomorph M (Model n))
    (c : ℝ) (α : Form (model n) M (2 * n)) :
    topFormCoefficient e (c • α) = c • topFormCoefficient e α := rfl

/-- The weighted, chart-domain coefficient used in the integral. -/
def topFormIntegrand (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (α : Form (model n) M (2 * n)) (i : Fin a.card) (y : Model n) : ℝ :=
  ρ i ((a.chart i).symm y) * topFormCoefficient (a.chart i) α y

/-- Integrate a genuine top form using one actual oriented atlas and partition. -/
def integralTopForm (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (α : Form (model n) M (2 * n)) : ℝ :=
  ∑ i, ∫ y in (a.chart i).target, topFormIntegrand a ρ α i y ∂volume

@[simp] theorem integralTopForm_zero (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ) :
    integralTopForm a ρ (0 : Form (model n) M (2 * n)) = 0 := by
  simp [integralTopForm, topFormIntegrand]

theorem integralTopForm_add (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (α β : Form (model n) M (2 * n))
    (hα : ∀ i, IntegrableOn (topFormIntegrand a ρ α i) (a.chart i).target volume)
    (hβ : ∀ i, IntegrableOn (topFormIntegrand a ρ β i) (a.chart i).target volume) :
    integralTopForm a ρ (α + β) = integralTopForm a ρ α + integralTopForm a ρ β := by
  unfold integralTopForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hf : topFormIntegrand a ρ (α + β) i =
      topFormIntegrand a ρ α i + topFormIntegrand a ρ β i := by
    funext y
    simp [topFormIntegrand, topFormCoefficient_add, mul_add]
  rw [hf]
  exact integral_add (hα i) (hβ i)

end GaussBonnetChern
