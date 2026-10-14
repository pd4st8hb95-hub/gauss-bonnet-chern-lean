import GaussBonnetChern.NormalizedSphereLimit
import GaussBonnetChern.SphereLinearIndexIntegral
import GaussBonnetChern.SphereFormIntegration
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.InnerProductSpace.Orientation

/-! # The actual normalized linear map on a sphere

Radial terms in the derivative disappear from the normal-first alternating
determinant. This is the pointwise computation behind the sphere pullback
density; the final integral uses the genuine polar-measure calculation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Module Set Metric Function
open scoped BigOperators Topology ContDiff Manifold

namespace GaussBonnetChern

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

theorem alternating_cons_smul (A : E [⋀^Fin (d+1)]→ₗ[ℝ] ℝ)
    (x : E) (v : Fin d → E) (r : ℝ) :
    A (Fin.cons (r • x) v) = r • A (Fin.cons x v) := by
  simpa only [Matrix.vecCons] using A.map_vecCons_smul v r x

/-- Adding arbitrary multiples of the first vector to the other slots leaves
an alternating expression unchanged. The dimension is symbolic. -/
theorem alternating_cons_radial_add (A : E [⋀^Fin (d+1)]→ₗ[ℝ] ℝ)
    (x : E) (v : Fin d → E) (c : Fin d → ℝ) :
    A (Fin.cons x (fun i ↦ v i + c i • x)) = A (Fin.cons x v) := by
  classical
  let B := A.curryLeft x
  change B (v + fun i ↦ c i • x) = B v
  rw [B.map_add_univ]
  rw [Finset.sum_eq_single Finset.univ]
  · simp
  · intro s hs hsne
    obtain ⟨i, hi⟩ : ∃ i : Fin d, i ∉ s := by
      simpa only [ne_eq, Finset.eq_univ_iff_forall, not_forall] using hsne
    let w := s.piecewise v (fun i ↦ c i • x)
    change B w = 0
    have hw : w i = c i • x := Finset.piecewise_eq_of_notMem _ _ _ hi
    rw [← Function.update_eq_self i w, hw, B.map_update_smul]
    have hz : B (Function.update w i x) = 0 := by
      change A (Fin.cons x (Function.update w i x)) = 0
      exact A.map_eq_zero_of_eq _ (i := 0) (j := i.succ)
        (by simp) (Fin.succ_ne_zero i).symm
    rw [hz, smul_zero]
  · simp

/-- Only the radial coefficient is left abstract here; it is the actual
Fréchet derivative of the inverse norm. -/
theorem fderiv_normalize_apply {x : E} (hx : x ≠ 0) (v : E) :
    fderiv ℝ LocalIndex.normalize x v = ‖x‖⁻¹ • v +
      (fderiv ℝ (fun y : E ↦ ‖y‖⁻¹) x v) • x := by
  change fderiv ℝ (fun y : E ↦ ‖y‖⁻¹ • y) x v = _
  have hc : DifferentiableAt ℝ (fun y : E ↦ ‖y‖⁻¹) x :=
    (((contDiffAt_norm ℝ hx : ContDiffAt ℝ ∞ (fun y : E ↦ ‖y‖) x).inv
      (norm_ne_zero_iff.mpr hx)).differentiableAt (by simp))
  rw [fderiv_fun_smul (c := fun y : E ↦ ‖y‖⁻¹) (f := fun y : E ↦ y)
    hc differentiableAt_id]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    fderiv_id', ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply]

theorem fderiv_normalized_linear_apply (L : E ≃L[ℝ] E) {x : E} (hx : x ≠ 0) (v : E) :
    fderiv ℝ (fun y ↦ LocalIndex.normalize (L y)) x v =
      ‖L x‖⁻¹ • L v + (fderiv ℝ (fun y : E ↦ ‖y‖⁻¹) (L x) (L v)) • L x := by
  have hLx : L x ≠ 0 := fun h ↦ hx (L.injective (by simpa using h))
  have hc := fderiv_comp x
    ((LocalIndex.contDiffAt_normalize hLx).differentiableAt (by simp)) L.differentiableAt
  simp only [ContinuousLinearEquiv.fderiv, Function.comp_def] at hc
  rw [hc]
  exact fderiv_normalize_apply hLx _

/-- Actual ambient determinant calculation for normalization, with all radial
derivative terms cancelled by alternation. -/
theorem det_normalized_linear (b : Basis (Fin (d+1)) ℝ E) (L : E ≃L[ℝ] E)
    {x : E} (hx : x ≠ 0) (v : Fin d → E) :
    b.det (Fin.cons (LocalIndex.normalize (L x))
      (fun i ↦ fderiv ℝ (fun y ↦ LocalIndex.normalize (L y)) x (v i))) =
      (LinearMap.det L.toLinearMap / ‖L x‖ ^ (d+1)) * b.det (Fin.cons x v) := by
  simp only [fderiv_normalized_linear_apply L hx]
  rw [LocalIndex.normalize, alternating_cons_smul,
    alternating_cons_radial_add]
  have hscale := (b.det.curryLeft (L x)).map_smul_univ
    (fun _ : Fin d ↦ ‖L x‖⁻¹) (fun i ↦ L (v i))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    AlternatingMap.curryLeft_apply_apply, Matrix.vecCons] at hscale
  rw [hscale]
  have hcomp : Fin.cons (L x) (fun i ↦ L (v i)) = L.toLinearMap ∘ Fin.cons x v := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [hcomp, b.det_comp]
  simp only [div_eq_mul_inv, inv_pow, pow_succ, smul_eq_mul]
  ring

/-- The actual normalized image of a unit vector under an invertible linear map. -/
def sphereNormalizedLinearMap (L : E ≃L[ℝ] E) (u : sphere (0 : E) 1) :
    sphere (0 : E) 1 :=
  ⟨LocalIndex.normalize (L u), by
    rw [mem_sphere_zero_iff_norm]
    apply LocalIndex.norm_normalize
    intro hz
    apply ne_of_mem_sphere u.property one_ne_zero
    exact L.injective (by simpa using hz)⟩

@[simp] theorem sphereNormalizedLinearMap_coe (L : E ≃L[ℝ] E)
    (u : sphere (0 : E) 1) :
    (sphereNormalizedLinearMap L u : E) = LocalIndex.normalize (L u) := rfl

section Sphere

variable [Fact (finrank ℝ E = d+1)]

theorem contMDiff_sphereNormalizedLinearMap (L : E ≃L[ℝ] E) :
    ContMDiff (𝓡 d) (𝓡 d) ∞ (sphereNormalizedLinearMap L) := by
  have hf : ContMDiff (𝓡 d) 𝓘(ℝ, E) ∞
      (fun u : sphere (0 : E) 1 ↦ LocalIndex.normalize (L u)) := by
    intro u
    have hne : L u ≠ 0 := by
      intro h
      exact ne_of_mem_sphere u.property one_ne_zero (L.injective (by simpa using h))
    exact (LocalIndex.contDiffAt_normalize hne).contMDiffAt.comp u
      ((L.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := d))) u)
  exact hf.codRestrict_sphere (fun u ↦ (sphereNormalizedLinearMap L u).property)

/-- The true sphere derivative, included back into the ambient space, is the
derivative of the actual ambient normalized map applied to the included tangent vector. -/
theorem sphereNormalizedLinearMap_derivative (L : E ≃L[ℝ] E)
    (u : sphere (0 : E) 1) (v : TangentSpace (𝓡 d) u) :
    mvfderiv (𝓡 d) ((↑) : sphere (0 : E) 1 → E) (sphereNormalizedLinearMap L u)
      (mfderiv (𝓡 d) (𝓡 d) (sphereNormalizedLinearMap L) u v) =
    fderiv ℝ (fun y ↦ LocalIndex.normalize (L y)) (u : E)
      (mvfderiv (𝓡 d) ((↑) : sphere (0 : E) 1 → E) u v) := by
  have hF := (contMDiff_sphereNormalizedLinearMap (d := d) L u).mdifferentiableAt (by simp)
  have hcoe (w : sphere (0 : E) 1) :=
    (contMDiff_coe_sphere (n := d) (m := ∞) w).mdifferentiableAt (by simp)
  have h1 := mvfderiv_comp_apply u (hcoe (sphereNormalizedLinearMap L u)) hF v
  have hne : L u ≠ 0 := by
    intro h
    exact ne_of_mem_sphere u.property one_ne_zero (L.injective (by simpa using h))
  have hg : ContDiffAt ℝ ∞ (fun y ↦ LocalIndex.normalize (L y)) (u : E) :=
    (LocalIndex.contDiffAt_normalize hne).comp (u : E) L.contDiff.contDiffAt
  have h2 := mvfderiv_comp_apply u (hg.contMDiffAt.mdifferentiableAt (by simp)) (hcoe u) v
  rw [mvfderiv_eq_fderiv] at h2
  exact h1.symm.trans h2

/-- The actual differential-form pullback, with the normal placed first.
No Jacobian-density identity is assumed. -/
theorem pullback_sphereVolumeForm_normalizedLinear
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (L : E ≃L[ℝ] E) :
    DifferentialForm.pullback (I := 𝓡 d) (I' := 𝓡 d)
      (sphereNormalizedLinearMap L) (sphereVolumeForm b) =
      fun u : sphere (0 : E) 1 ↦
        (LinearMap.det L.toLinearMap / ‖L u‖ ^ (d+1)) • sphereVolumeForm b u := by
  funext u
  ext v
  simp only [DifferentialForm.pullback_apply, sphereVolumeForm_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, sphereNormalizedLinearMap_coe]
  simp only [sphereNormalizedLinearMap_derivative]
  exact det_normalized_linear b.toBasis L (ne_of_mem_sphere u.property one_ne_zero)
    (fun i ↦ mvfderiv (𝓡 d) ((↑) : sphere (0 : E) 1 → E) u (v i))

theorem sphereFormCoefficient_normalizedLinear_pullback
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (L : E ≃L[ℝ] E)
    (u : sphere (0 : E) 1) :
    sphereFormCoefficient b (DifferentialForm.pullback (I := 𝓡 d) (I' := 𝓡 d)
      (sphereNormalizedLinearMap L) (sphereVolumeForm b)) u =
      LinearMap.det L.toLinearMap / ‖L u‖ ^ (d+1) := by
  rw [pullback_sphereVolumeForm_normalizedLinear, sphereFormCoefficient_fsmul_volume]

section Integral

open MeasureTheory
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual pullback form has integral equal to determinant sign times the
polar sphere mass. Its density is the preceding proved pullback identity. -/
theorem sphereFormIntegral_normalizedLinear_pullback
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (L : E ≃L[ℝ] E) :
    sphereFormIntegral b (DifferentialForm.pullback (I := 𝓡 d) (I' := 𝓡 d)
      (sphereNormalizedLinearMap L) (sphereVolumeForm b)) =
      Real.sign (LinearMap.det L.toLinearMap) * (volume : Measure E).toSphere.real univ := by
  have hdim : finrank ℝ E = d+1 := Fact.out
  letI : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hdim]; omega)
  rw [pullback_sphereVolumeForm_normalizedLinear, sphereFormIntegral_fsmul_volume]
  simpa only [hdim] using integral_sphere_linearIndex_density (volume : Measure E) L

end Integral
end Sphere

end GaussBonnetChern
