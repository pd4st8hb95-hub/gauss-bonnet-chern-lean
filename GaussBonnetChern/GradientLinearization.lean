import GaussBonnetChern.MorseIndex

/-! # Linearization of a vector field at a zero

The linearization below differentiates the actual scalar coefficients in a
smooth local frame. The connection terms disappear at a zero. This identifies
the index-relevant derivative of the gradient with its covariant derivative,
and therefore with the metric-raised Hessian.
-/

noncomputable section

open Bundle FiberBundle Module Filter
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

def coordinateFrame (p : M) (i : Fin (2 * n)) (y : M) : TangentSpace (model n) y :=
  (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).localFrame
    (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis i y

def fieldCoordinate (p : M) (X : (y : M) → TangentSpace (model n) y)
    (i : Fin (2 * n)) (y : M) : ℝ :=
  (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).localFrameCoeff
    (model n) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis i y (X y)

theorem contMDiffAt_coordinateFrame (p : M) (i : Fin (2 * n)) :
    ContMDiffAt (model n) (model n).tangent ∞ (T% (coordinateFrame n M p i)) p :=
  contMDiffAt_localFrame_of_mem ∞ _ _ i (mem_baseSet_trivializationAt' p)

theorem contMDiffAt_fieldCoordinate {p : M} {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) p) (i : Fin (2 * n)) :
    ContMDiffAt (model n) 𝓘(ℝ) ∞ (fieldCoordinate n M p X i) p :=
  contMDiffAt_localFrameCoeff _ (mem_baseSet_trivializationAt' p) hX i

theorem fieldCoordinate_at_zero {p : M} {X : (y : M) → TangentSpace (model n) y}
    (hX : X p = 0) (i : Fin (2 * n)) : fieldCoordinate n M p X i p = 0 := by
  simp only [fieldCoordinate, hX, map_zero]

/-- Derivatives of the true local coefficient functions, transported back
to the tangent fiber. This definition uses no connection. -/
def fieldLinearization (p : M) (X : (y : M) → TangentSpace (model n) y) :
    TangentSpace (model n) p →L[ℝ] TangentSpace (model n) p :=
  ∑ i, (mvfderiv (model n) (fieldCoordinate n M p X i) p).smulRight
    (coordinateFrame n M p i p)

theorem connection_sum {ι : Type*} (s : Finset ι)
    (X : ι → (y : M) → TangentSpace (model n) y) {p : M}
    (hX : ∀ i ∈ s, ContMDiffAt (model n) (model n).tangent ∞ (T% (X i)) p) :
    connection n M (fun y ↦ ∑ i ∈ s, X i y) p = ∑ i ∈ s, connection n M (X i) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, ← Pi.zero_def] using
      (connection n M).isCovariantDerivativeOnUniv.zero (x := p)
  | @insert i s hi ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hX
    simp only [Finset.sum_insert hi, ← ih hX.2]
    exact (connection n M).isCovariantDerivativeOnUniv.add
      (hX.1.mdifferentiableAt (by simp))
      ((ContMDiffAt.sum_section hX.2).mdifferentiableAt (by simp))

/-- The zero value removes every connection-coefficient term in the local
Leibniz formula. This is valid for the original chosen metric and connection. -/
theorem fieldLinearization_eq_connection {p : M}
    {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) p) (hzero : X p = 0) :
    fieldLinearization n M p X = connection n M X p := by
  classical
  let Y (i : Fin (2 * n)) : (y : M) → TangentSpace (model n) y :=
    fieldCoordinate n M p X i • coordinateFrame n M p i
  have hY i : ContMDiffAt (model n) (model n).tangent ∞ (T% (Y i)) p :=
    (contMDiffAt_fieldCoordinate n M hX i).smul_section (contMDiffAt_coordinateFrame n M p i)
  have heq : ∀ᶠ y in 𝓝 p, X y = ∑ i, Y i y :=
    (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).eventually_eq_localFrame_sum_coeff_smul
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
        (mem_baseSet_trivializationAt' p)
  have hc := (connection n M).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (hX.mdifferentiableAt (by simp))
    ((ContMDiffAt.sum_section (fun i _ ↦ hY i)).mdifferentiableAt (by simp))
    Filter.univ_mem heq
  rw [hc, connection_sum n M Finset.univ Y (fun i _ ↦ hY i)]
  unfold fieldLinearization
  apply Finset.sum_congr rfl
  intro i _
  have h := (connection n M).isCovariantDerivativeOnUniv.leibniz
    ((contMDiffAt_coordinateFrame n M p i).mdifferentiableAt (by simp))
    ((contMDiffAt_fieldCoordinate n M hX i).mdifferentiableAt (by simp))
  simpa only [fieldCoordinate_at_zero n M hzero, zero_smul, zero_add] using! h.symm

theorem gradientLinearization_eq_connection {p : M} {f : M → ℝ}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f p) (hcritical : mvfderiv (model n) f p = 0) :
    fieldLinearization n M p (gradient n M f) = connection n M (gradient n M f) p :=
  fieldLinearization_eq_connection n M (contMDiffAt_gradient n M hf)
    ((gradient_eq_zero_iff n M f p).mpr hcritical)

theorem sign_gradientLinearization_det {p : M} {f : M → ℝ}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f p) (hcritical : mvfderiv (model n) f p = 0)
    (hdet : LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap ≠ 0) :
    Real.sign (LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap) =
      (-1 : ℝ) ^ morseIndex n M hf := by
  rw [gradientLinearization_eq_connection n M hf hcritical] at hdet ⊢
  exact sign_gradient_covariant_det n M hf hdet

end GaussBonnetChern
