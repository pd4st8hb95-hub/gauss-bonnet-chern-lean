import GaussBonnetChern.ParametricIntegration
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Exact quadratic coefficient for the local Morse lemma

This module begins the local normal-form construction with the actual second
Fréchet derivative. The coefficient is a Bochner integral, not an assumed
quadratic representation. The full local coordinate normal form is a later
theorem, and is not asserted by these Taylor identities.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace GaussBonnetChern.MorseLocal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A function smooth on an open neighborhood agrees locally with a globally
smooth function. This permits use of the global Taylor coefficient without
adding any global hypothesis to the eventual Morse theorem. -/
theorem exists_global_smooth_extension {f : E → ℝ} {s : Set E} {p : E}
    (hs : IsOpen s) (hp : p ∈ s) (hf : ContDiffOn ℝ ∞ f s) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 p] f := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hp)
  let b : ContDiffBump p :=
    { rIn := r / 4, rOut := r / 2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hb : tsupport b ⊆ s := by
    rw [b.tsupport_eq]
    apply subset_trans _ hrs
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  refine ⟨fun x => b x * f x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact b.contDiff.contDiffAt.mul ((hf x (hb hx)).contDiffAt (hs.mem_nhds (hb hx)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
  · filter_upwards [b.eventuallyEq_one] with x hx
    simp [hx]

/-- The symmetric quadratic coefficient in the exact integral Taylor formula. -/
def quadraticCoefficient (f : E → ℝ) (p v : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ f) (p + t • v)

theorem contDiff_quadraticCoefficient {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (p : E) :
    ContDiff ℝ ∞ (quadraticCoefficient f p) := by
  letI : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _
  have hD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  unfold quadraticCoefficient
  apply ParametricIntegration.contDiff_integral
    (f := fun q : E × ℝ => (1 - q.2) • fderiv ℝ (fderiv ℝ f) (p + q.2 • q.1))
  have hm : ContDiff ℝ ∞ (fun q : ℝ × (E →L[ℝ] E →L[ℝ] ℝ) => q.1 • q.2) :=
    (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)).isBoundedBilinearMap.contDiff
  exact hm.comp ((contDiff_const.sub contDiff_snd).prodMk
    (hD.comp (contDiff_const.add (contDiff_snd.smul contDiff_fst))))

theorem quadraticCoefficient_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (p v u w : E) :
    quadraticCoefficient f p v u w =
      ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (p + t • v) u w := by
  have hD : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  have hI : Continuous (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ f) (p + t • v)) := by
    exact (continuous_const.sub continuous_id).smul
      (hD.comp (continuous_const.add (continuous_id.smul continuous_const)))
  unfold quadraticCoefficient
  rw [ContinuousLinearMap.intervalIntegral_apply (hI.intervalIntegrable 0 1)]
  rw [ContinuousLinearMap.intervalIntegral_apply
    ((hI.clm_apply continuous_const).intervalIntegrable 0 1)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem quadraticCoefficient_symmetric {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (p v u w : E) : quadraticCoefficient f p v u w = quadraticCoefficient f p v w u := by
  rw [quadraticCoefficient_apply hf, quadraticCoefficient_apply hf]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp
  rw [(hf.contDiffAt (x := p + t • v)).isSymmSndFDerivAt (by simp) |>.eq u w]

theorem quadraticCoefficient_zero (f : E → ℝ) (p : E) :
    quadraticCoefficient f p 0 = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) p := by
  unfold quadraticCoefficient
  simp only [smul_zero, add_zero]
  rw [intervalIntegral.integral_smul_const (fun t : ℝ => 1 - t)
    (fderiv ℝ (fderiv ℝ f) p)]
  congr 1
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun x : ℝ => x)
    (continuous_const.intervalIntegrable 0 1)
    (continuous_id.intervalIntegrable 0 1), intervalIntegral.integral_const,
    integral_id]
  norm_num

/-- Exact second-order Taylor formula, with the variable bilinear coefficient constructed above. -/
theorem taylor_quadratic {f : E → ℝ} (hf : ContDiff ℝ 2 f) (p v : E) :
    f (p + v) = f p + fderiv ℝ f p v + quadraticCoefficient f p v v v := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := p) (y := v)
    (n := 1) (fun _ _ => hf.contDiffAt)
  rw [quadraticCoefficient_apply hf]
  simpa [Finset.sum_range_succ, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
    iteratedFDeriv_two_apply, smul_eq_mul] using ht

/-- At a critical point the exact formula has no linear term. -/
theorem taylor_quadratic_at_critical {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {p : E} (hp : fderiv ℝ f p = 0) (v : E) :
    f (p + v) = f p + quadraticCoefficient f p v v v := by
  simpa [hp] using taylor_quadratic hf p v

/-- The finite-dimensional real vector space of symmetric continuous bilinear forms. -/
def symmetricForms (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (E →L[ℝ] E →L[ℝ] ℝ) where
  carrier := {B | ∀ u v, B u v = B v u}
  zero_mem' := by simp
  add_mem' := by
    intro B C hB hC u v
    simp only [ContinuousLinearMap.add_apply]
    rw [hB, hC]
  smul_mem' := by
    intro r B hB u v
    simp only [ContinuousLinearMap.smul_apply]
    rw [hB]

abbrev SymmetricForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ↥(symmetricForms E)

@[reducible] instance : NormedAddCommGroup (SymmetricForm E) :=
  @Submodule.normedAddCommGroup ℝ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ (symmetricForms E)

@[reducible] instance : NormedSpace ℝ (SymmetricForm E) :=
  Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ) (symmetricForms E)

instance : FiniteDimensional ℝ (SymmetricForm E) :=
  FiniteDimensional.finiteDimensional_submodule (K := ℝ)
    (V := E →L[ℝ] E →L[ℝ] ℝ) (symmetricForms E)

/-- Continuous linear projection onto the symmetric forms. -/
def symmetrize : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] SymmetricForm E :=
  ((1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ _ +
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap)).codRestrict
    (symmetricForms E) (by
      intro B u v
      change (1 / 2 : ℝ) * (B u v + B v u) = (1 / 2 : ℝ) * (B v u + B u v)
      ring)

theorem symmetrize_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) :
    (symmetrize B : E →L[ℝ] E →L[ℝ] ℝ) u v = (B u v + B v u) / 2 := by
  change (1 / 2 : ℝ) * (B u v + B v u) = _
  ring

@[simp] theorem symmetrize_symmetric (B : SymmetricForm E) : symmetrize B.val = B := by
  apply Subtype.ext
  ext u v
  rw [symmetrize_apply, B.property u v]
  ring

/-- Polynomial used for the local congruence of nearby nondegenerate quadratic forms. -/
def congruencePolynomial (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (S : SymmetricForm E) : SymmetricForm E :=
  symmetrize (S.val + (1 / 4 : ℝ) • S.val.comp (B.symm.toContinuousLinearMap.comp S.val))

@[simp] theorem congruencePolynomial_zero (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    congruencePolynomial B 0 = 0 := by
  simp [congruencePolynomial]

theorem contDiff_congruencePolynomial (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) {k : ℕ∞ω} :
    ContDiff ℝ k (congruencePolynomial B) := by
  let val : SymmetricForm E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) := (symmetricForms E).subtypeL
  have hs : ContDiff ℝ k (fun S : SymmetricForm E => S.val) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := SymmetricForm E)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (n := k) val
  exact symmetrize.contDiff.comp (hs.add
    ((hs.clm_comp (contDiff_const.clm_comp hs)).const_smul (1 / 4 : ℝ)))

theorem hasFDerivAt_congruencePolynomial_zero (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    HasFDerivAt (congruencePolynomial B)
      (ContinuousLinearMap.id ℝ (SymmetricForm E)) 0 := by
  let val : SymmetricForm E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) := (symmetricForms E).subtypeL
  have hs := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := SymmetricForm E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) val (x := (0 : SymmetricForm E))
  have hq := hs.clm_comp ((hasFDerivAt_const B.symm.toContinuousLinearMap
    (0 : SymmetricForm E)).clm_comp hs)
  have h := symmetrize.hasFDerivAt.comp (0 : SymmetricForm E)
    (hs.add (hq.const_smul (1 / 4 : ℝ)))
  convert! h using 1 <;> ext S <;> simp [congruencePolynomial, val]

/-- The genuine smooth local inverse of the congruence polynomial at zero. -/
def congruenceInverse (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) : SymmetricForm E → SymmetricForm E :=
  (contDiff_congruencePolynomial B (k := ω)).contDiffAt.localInverse
    (f' := ContinuousLinearEquiv.refl ℝ (SymmetricForm E))
    (hasFDerivAt_congruencePolynomial_zero B) (by simp)

@[simp] theorem congruenceInverse_zero (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    congruenceInverse B 0 = 0 := by
  simpa [congruenceInverse] using
    (contDiff_congruencePolynomial B (k := ω)).contDiffAt.localInverse_apply_image
      (f' := ContinuousLinearEquiv.refl ℝ (SymmetricForm E))
      (hasFDerivAt_congruencePolynomial_zero B) (by simp)

theorem contDiffAt_congruenceInverse (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    ContDiffAt ℝ ω (congruenceInverse B) 0 := by
  simpa [congruenceInverse] using
    (contDiff_congruencePolynomial B (k := ω)).contDiffAt.to_localInverse
      (f' := ContinuousLinearEquiv.refl ℝ (SymmetricForm E))
      (hasFDerivAt_congruencePolynomial_zero B) (by simp)

theorem eventually_congruenceInverse_right (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    ∀ᶠ S in 𝓝 (0 : SymmetricForm E),
      congruencePolynomial B (congruenceInverse B S) = S := by
  simpa [congruenceInverse, ContDiffAt.localInverse] using
    ((contDiff_congruencePolynomial B (k := ω)).contDiffAt.hasStrictFDerivAt'
      (f' := ContinuousLinearEquiv.refl ℝ (SymmetricForm E))
      (hasFDerivAt_congruencePolynomial_zero B) (by simp)).eventually_right_inverse

theorem symmetric_sandwich (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (hB : ∀ u v, B u v = B v u) (S : SymmetricForm E) (u v : E) :
    S.val (B.symm (S.val u)) v = S.val (B.symm (S.val v)) u := by
  calc
    S.val (B.symm (S.val u)) v = S.val v (B.symm (S.val u)) := S.property _ _
    _ = B (B.symm (S.val v)) (B.symm (S.val u)) := by simp
    _ = B (B.symm (S.val u)) (B.symm (S.val v)) := hB _ _
    _ = S.val u (B.symm (S.val v)) := by simp
    _ = S.val (B.symm (S.val v)) u := S.property _ _

theorem congruencePolynomial_apply (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (hB : ∀ u v, B u v = B v u) (S : SymmetricForm E) (u v : E) :
    (congruencePolynomial B S).val u v = S.val u v +
      (1 / 4 : ℝ) * S.val (B.symm (S.val u)) v := by
  unfold congruencePolynomial
  rw [symmetrize_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, smul_eq_mul]
  rw [← S.property u v, ← symmetric_sandwich B hB S u v]
  ring

/-- The coordinate correction associated to a symmetric perturbation. -/
def congruenceCorrection (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) (S : SymmetricForm E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (1 / 2 : ℝ) • B.symm.toContinuousLinearMap.comp S.val

/-- Exact algebraic congruence identity, valid in every finite dimension and signature. -/
theorem congruenceCorrection_identity (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (hB : ∀ u v, B u v = B v u) (S : SymmetricForm E) (u v : E) :
    B (congruenceCorrection B S u) (congruenceCorrection B S v) =
      B u v + (congruencePolynomial B S).val u v := by
  rw [congruencePolynomial_apply B hB]
  simp only [congruenceCorrection, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul]
  rw [hB u (B.symm (S.val v)), ContinuousLinearEquiv.apply_symm_apply,
    ← S.property u v, S.property u (B.symm (S.val v)),
    ← symmetric_sandwich B hB S u v]
  ring

/-- Solve the polynomial equation for the difference from the base quadratic form. -/
def congruenceParameter (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (A : E → SymmetricForm E) (v : E) : SymmetricForm E :=
  congruenceInverse B (A v - A 0)

@[simp] theorem congruenceParameter_zero (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (A : E → SymmetricForm E) : congruenceParameter B A 0 = 0 := by
  simp [congruenceParameter]

theorem contDiffAt_congruenceParameter (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    {A : E → SymmetricForm E} (hA : ContDiffAt ℝ ∞ A 0) :
    ContDiffAt ℝ ∞ (congruenceParameter B A) 0 := by
  have hI : ContDiffAt ℝ ∞ (congruenceInverse B) (A 0 - A 0) := by
    simpa using (contDiffAt_congruenceInverse B).of_le (show (∞ : ℕ∞ω) ≤ ω by simp)
  exact hI.comp 0 (hA.sub contDiffAt_const)

theorem contDiff_congruenceCorrection (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    ContDiff ℝ ∞ (congruenceCorrection B) := by
  exact contDiff_const.add ((contDiff_const.clm_comp
    (symmetricForms E).subtypeL.contDiff).const_smul (1 / 2 : ℝ))

/-- Actual coordinate map produced by the congruence equation. -/
def normalizingMap (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) (A : E → SymmetricForm E) (v : E) : E :=
  congruenceCorrection B (congruenceParameter B A v) v

@[simp] theorem normalizingMap_zero (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (A : E → SymmetricForm E) : normalizingMap B A 0 = 0 := by
  simp [normalizingMap]

theorem contDiffAt_normalizingMap (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    {A : E → SymmetricForm E} (hA : ContDiffAt ℝ ∞ A 0) :
    ContDiffAt ℝ ∞ (normalizingMap B A) 0 := by
  exact ((contDiff_congruenceCorrection B).contDiffAt.comp 0
    (contDiffAt_congruenceParameter B hA)).clm_apply contDiffAt_id

theorem hasFDerivAt_normalizingMap_zero (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    {A : E → SymmetricForm E} (hA : ContDiffAt ℝ ∞ A 0) :
    HasFDerivAt (normalizingMap B A) (ContinuousLinearMap.id ℝ E) 0 := by
  have hP := ((contDiff_congruenceCorrection B).contDiffAt.comp 0
    (contDiffAt_congruenceParameter B hA)).differentiableAt (by simp)
  unfold normalizingMap
  simpa only [Function.comp_apply, id_eq, congruenceParameter_zero, congruenceCorrection,
    Submodule.coe_zero, ContinuousLinearMap.comp_zero, smul_zero, add_zero,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, map_zero] using
    hP.hasFDerivAt.clm_apply (hasFDerivAt_id (𝕜 := ℝ) (0 : E))

/-- Nearby quadratic forms are carried into the constant base form by the
constructed coordinate map. The equality holds on a neighborhood obtained
from the inverse-function theorem, rather than being an assumed relation. -/
theorem eventually_normalizingMap_identity (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    {A : E → SymmetricForm E} (hA : ContDiffAt ℝ ∞ A 0)
    (hA0 : (A 0).val = B.toContinuousLinearMap) :
    ∀ᶠ v in 𝓝 (0 : E), B (normalizingMap B A v) (normalizingMap B A v) = (A v).val v v := by
  have hB : ∀ u v, B u v = B v u := by
    intro u v
    rw [← ContinuousLinearEquiv.coe_coe, ← hA0]
    exact (A 0).property u v
  have hcont : Tendsto (fun v => A v - A 0) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun v : E => A v - A 0) 0 :=
      hA.continuousAt.sub continuousAt_const
    simpa only [sub_self] using hc.tendsto
  filter_upwards [hcont.eventually (eventually_congruenceInverse_right B)] with v hv
  rw [normalizingMap, congruenceCorrection_identity B hB,
    show congruencePolynomial B (congruenceParameter B A v) = A v - A 0 from hv]
  have hb0 : B v v = (A 0).val v v := congrArg (fun C : E →L[ℝ] E →L[ℝ] ℝ => C v v) hA0.symm
  rw [hb0]
  simp

end GaussBonnetChern.MorseLocal
