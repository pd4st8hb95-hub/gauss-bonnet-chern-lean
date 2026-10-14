import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-! # Real differential forms on manifolds

A form is a section of the actual bundle of continuous alternating maps on tangent
spaces. Pullback is precomposition with the manifold derivative. No integration,
exterior derivative, or Stokes theorem is assumed here.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GaussBonnetChern
namespace DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- An unbundled real differential `k`-form. Smoothness is a separate condition. -/
abbrev Form (k : ℕ) := (x : M) →
  ContinuousAlternatingMap ℝ (TangentSpace I x) ℝ (Fin k)

variable {I M}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {k : ℕ}

/-- Pullback through the actual manifold derivative; functoriality below requires
manifold differentiability, since `mfderiv` is totalized outside that locus. -/
def pullback (f : M → M') (α : Form I' M' k) : Form I M k :=
  fun x ↦ (α (f x)).compContinuousLinearMap (mfderiv I I' f x)

@[simp] theorem pullback_apply (f : M → M') (α : Form I' M' k)
    (x : M) (v : Fin k → TangentSpace I x) :
    pullback (I := I) f α x v = α (f x) (fun j ↦ mfderiv I I' f x (v j)) := rfl

@[simp] theorem pullback_id (α : Form I M k) : pullback id α = α := by
  funext x
  ext v
  simp [pullback, mfderiv_id, ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- The pointwise chain rule is the local version needed for chart transitions. -/
theorem pullback_comp_at (f : M → M') (g : M' → M'') (α : Form I'' M'' k)
    (x : M) (hf : MDifferentiableAt I I' f x)
    (hg : MDifferentiableAt I' I'' g (f x)) :
    pullback (I := I) (g ∘ f) α x =
      pullback (I := I) f (pullback (I := I') g α) x := by
  ext v
  simp only [pullback_apply]
  rw [mfderiv_comp x hg hf]
  rfl

/-- Chain rule for pullback, with explicit genuine differentiability hypotheses. -/
theorem pullback_comp (f : M → M') (g : M' → M'') (α : Form I'' M'' k)
    (hf : MDifferentiable I I' f) (hg : MDifferentiable I' I'' g) :
    pullback (I := I) (g ∘ f) α = pullback (I := I) (I' := I') f (pullback (I := I') (I' := I'') g α) := by
  funext x
  ext v
  simp only [pullback_apply]
  rw [mfderiv_comp x (hg (f x)) (hf x)]
  rfl

/-- A function interpreted as a zero form. -/
def ofFunction (f : M → ℝ) : Form I M 0 :=
  fun x ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentSpace I x) (Fin 0) (f x)

/-- Evaluate a zero form on the unique empty tuple. -/
def toFunction (α : Form I M 0) : M → ℝ := fun x ↦ α x 0

@[simp] theorem toFunction_ofFunction (f : M → ℝ) :
    toFunction (ofFunction (I := I) f) = f := by
  funext x
  rfl

@[simp] theorem ofFunction_toFunction (α : Form I M 0) :
    ofFunction (toFunction α) = α := by
  funext x
  ext v
  simp [ofFunction, toFunction, Subsingleton.allEq v 0]

/-- Zero forms and scalar functions are exactly equivalent, without hypotheses. -/
def zeroFormEquiv : Form I M 0 ≃ (M → ℝ) where
  toFun := toFunction
  invFun := ofFunction
  left_inv := ofFunction_toFunction
  right_inv := toFunction_ofFunction

@[simp] theorem pullback_ofFunction (f : M → M') (h : M' → ℝ) :
    pullback (I := I) f (ofFunction (I := I') h) = ofFunction (h ∘ f) := by
  funext x
  ext v
  rfl

/-- Smooth maps give the differentiability required for functorial pullback. -/
theorem pullback_comp_smooth (f : M → M') (g : M' → M'') (α : Form I'' M'' k)
    (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I' I'' ∞ g) :
    pullback (I := I) (g ∘ f) α =
      pullback (I := I) f (pullback (I := I') g α) :=
  pullback_comp f g α (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp))

section FullSpaceCharts
variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N]

/-- A form in chart coordinates is its actual pullback by the inverse chart.
Only the open chart target is used for regularity statements. -/
def chartRepresentation (e : OpenPartialHomeomorph N E)
    (α : Form 𝓘(ℝ, E) N k) : E → ContinuousAlternatingMap ℝ E ℝ (Fin k) :=
  fun x ↦ ContinuousAlternatingMap.compContinuousLinearMap
    (pullback (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) e.symm α x)
    (NormedSpace.fromTangentSpace x).symm.toContinuousLinearMap

variable [IsManifold 𝓘(ℝ, E) ∞ N]

/-- Smoothness of a form on a manifold without boundary: every inverse smooth
chart pulls it back to a smooth normed-space form on that chart's target.
This uses the maximal atlas and the operator-norm topology on alternating maps. -/
def IsSmooth (α : Form 𝓘(ℝ, E) N k) : Prop :=
  ∀ e : OpenPartialHomeomorph N E,
    e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ N →
      ContDiffOn ℝ ∞ (chartRepresentation e α) e.target

/-- Bundle a form with the concrete chartwise regularity condition. -/
structure SmoothForm (k : ℕ) where
  toForm : Form 𝓘(ℝ, E) N k
  smooth : IsSmooth toForm

end FullSpaceCharts

end DifferentialForm
end GaussBonnetChern






