import GaussBonnetChern.MorseLocalLemma
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-! # Morse normal coordinates in arbitrary finite dimension

The normalizing map is constructed from the exact integral Taylor coefficient
and the inverse function theorem. Smoothness is assumed only on an open
neighborhood. Both coordinate directions are smooth on fixed open domains.
The number of negative squares is the signature of the actual half Hessian.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff
namespace GaussBonnetChern.MorseLocal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def symmetricQuadraticCoefficient (f : E → ℝ) (p : E) : E → SymmetricForm E :=
  fun v => symmetrize (quadraticCoefficient f p v)

theorem symmetricQuadraticCoefficient_val {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (p v : E) : (symmetricQuadraticCoefficient f p v).val = quadraticCoefficient f p v := by
  ext u w
  simp only [symmetricQuadraticCoefficient, symmetrize_apply]
  rw [quadraticCoefficient_symmetric hf p v u w]
  ring

theorem contDiff_symmetricQuadraticCoefficient {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (p : E) :
    ContDiff ℝ ∞ (symmetricQuadraticCoefficient f p) := by
  exact (symmetrize (E := E)).contDiff.comp (contDiff_quadraticCoefficient hf p)

/-- The inverse of the quadratic congruence polynomial is smooth on one fixed
open neighborhood; analyticity of the polynomial supplies that neighborhood. -/
theorem exists_open_congruenceInverse (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    ∃ U : Set (SymmetricForm E), IsOpen U ∧ 0 ∈ U ∧
      ContDiffOn ℝ ∞ (congruenceInverse B) U := by
  obtain ⟨U, hU, hI⟩ := (contDiffAt_congruenceInverse B).contDiffOn (m := ∞)
    (by simp) (by simp)
  obtain ⟨V, hVU, hV, h0⟩ := mem_nhds_iff.mp hU
  exact ⟨V, hV, h0, hI.mono hVU⟩

theorem exists_open_normalizingMap (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    {A : E → SymmetricForm E} (hA : ContDiff ℝ ∞ A) :
    ∃ U : Set E, IsOpen U ∧ 0 ∈ U ∧ ContDiffOn ℝ ∞ (normalizingMap B A) U := by
  obtain ⟨V, hV, hV0, hI⟩ := exists_open_congruenceInverse B
  let U := (fun v => A v - A 0) ⁻¹' V
  have hU : IsOpen U := hV.preimage (hA.continuous.sub continuous_const)
  have hU0 : (0 : E) ∈ U := by simpa [U] using hV0
  refine ⟨U, hU, hU0, ?_⟩
  have hP : ContDiffOn ℝ ∞ (congruenceParameter B A) U :=
    hI.comp (hA.contDiffOn.sub contDiffOn_const) (fun _ hx => hx)
  exact ((contDiff_congruenceCorrection B).comp_contDiffOn hP).clm_apply contDiffOn_id

/-- A genuine local smooth coordinate equivalence obtained by shrinking the
inverse-function-theorem chart until the derivative is invertible throughout. -/
theorem exists_smooth_coordinate_equiv {f : E → E} {U : Set E} {p : E}
    (hU : IsOpen U) (hp : p ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    {L : E ≃L[ℝ] E} (hL : HasFDerivAt f L.toContinuousLinearMap p) :
    ∃ e : OpenPartialHomeomorph E E, p ∈ e.source ∧ (e : E → E) = f ∧
      e.source ⊆ U ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hfp : ContDiffAt ℝ ∞ f p := (hf p hp).contDiffAt (hU.mem_nhds hp)
  have hd : ∀ᶠ y in 𝓝 p, (fderiv ℝ f y).IsInvertible := by
    have hLp : (fderiv ℝ f p).IsInvertible := by
      rw [hL.fderiv]
      exact ContinuousLinearMap.isInvertible_equiv
    exact (hfp.continuousAt_fderiv (by simp)).tendsto.eventually hLp.eventually_nhds
  obtain ⟨V, hVd, hV, hpV⟩ := mem_nhds_iff.mp hd
  let e0 := hfp.toOpenPartialHomeomorph f hL (by simp)
  let e := e0.restrOpen (U ∩ V) (hU.inter hV)
  have he0 : p ∈ e0.source := hfp.mem_toOpenPartialHomeomorph_source hL (by simp)
  have he : p ∈ e.source := ⟨he0, hp, hpV⟩
  have hes : e.source ⊆ U := fun x hx => hx.2.1
  refine ⟨e, he, rfl, hes, hf.mono hes, ?_⟩
  intro y hy
  have hx := e.map_target hy
  have hxy : ContDiffAt ℝ ∞ f (e.symm y) :=
    (hf _ (hes hx)).contDiffAt (hU.mem_nhds (hes hx))
  obtain ⟨Lx, hLx⟩ := hVd hx.2.2
  apply (e.contDiffAt_symm hy (f₀' := Lx) ?_ hxy).contDiffWithinAt
  rw [hLx]
  exact (hxy.differentiableAt (by simp)).hasFDerivAt

/-- Morse's lemma in constant-Hessian form, for a globally smooth function.
The coordinate map and its inverse are both smooth on their open domains. -/
theorem morse_quadratic_normal_form {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (p : E)
    (hp : fderiv ℝ f p = 0) (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (hB : B.toContinuousLinearMap = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) p) :
    ∃ e : OpenPartialHomeomorph E E,
      (0 : E) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      HasFDerivAt e (ContinuousLinearMap.id ℝ E) 0 ∧
      ∀ v ∈ e.source, f (p + v) = f p + B (e v) (e v) := by
  let A := symmetricQuadraticCoefficient f p
  have hA : ContDiff ℝ ∞ A := contDiff_symmetricQuadraticCoefficient hf p
  have hA0 : (A 0).val = B.toContinuousLinearMap := by
    rw [symmetricQuadraticCoefficient_val (hf.of_le (by simp)), quadraticCoefficient_zero, hB]
  obtain ⟨U, hU, hU0, hφ⟩ := exists_open_normalizingMap B hA
  have hId := hasFDerivAt_normalizingMap_zero B hA.contDiffAt
  obtain ⟨e, he0, hef, heU, he, hes⟩ := exists_smooth_coordinate_equiv hU hU0 hφ
    (L := ContinuousLinearEquiv.refl ℝ E) hId
  have hEq := eventually_normalizingMap_identity B hA.contDiffAt hA0
  obtain ⟨V, hVeq, hV, hV0⟩ := mem_nhds_iff.mp hEq
  let e' := e.restrOpen V hV
  refine ⟨e', ⟨he0, hV0⟩, ?_, ?_, ?_, ?_, ?_⟩
  · change e 0 = 0
    rw [hef, normalizingMap_zero]
  · exact he.mono inter_subset_left
  · exact hes.mono inter_subset_left
  · simpa only [e', OpenPartialHomeomorph.coe_restrOpen, hef] using hId
  · intro v hv
    rw [taylor_quadratic_at_critical (hf.of_le (by simp)) hp]
    congr 1
    change quadraticCoefficient f p v v v = B (e v) (e v)
    rw [hef, hVeq hv.2, symmetricQuadraticCoefficient_val (hf.of_le (by simp))]

/-- The local version requires smoothness only on the given open neighborhood. -/
theorem morse_quadratic_normal_form_on {f : E → ℝ} {s : Set E} {p : E}
    (hs : IsOpen s) (hps : p ∈ s) (hf : ContDiffOn ℝ ∞ f s)
    (hp : fderiv ℝ f p = 0) (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (hB : B.toContinuousLinearMap = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) p) :
    ∃ e : OpenPartialHomeomorph E E,
      (0 : E) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      HasFDerivAt e (ContinuousLinearMap.id ℝ E) 0 ∧
      ∀ v ∈ e.source, p + v ∈ s ∧ f (p + v) = f p + B (e v) (e v) := by
  obtain ⟨g, hg, hgf⟩ := exists_global_smooth_extension hs hps hf
  have hgp : fderiv ℝ g p = 0 := by rw [hgf.fderiv_eq, hp]
  have hBg : B.toContinuousLinearMap = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ g) p := by
    rw [hgf.fderiv.fderiv_eq, hB]
  obtain ⟨e, he0, he00, he, hes, hed, heq⟩ := morse_quadratic_normal_form hg p hgp B hBg
  have htr : Tendsto (fun v : E => p + v) (𝓝 0) (𝓝 p) := by
    have hc : Continuous (fun v : E => p + v) := continuous_const.add continuous_id
    simpa using hc.continuousAt.tendsto (x := (0 : E))
  have hnhds : {v : E | p + v ∈ s ∧ g (p + v) = f (p + v)} ∈ 𝓝 0 :=
    htr.eventually ((show ∀ᶠ x in 𝓝 p, x ∈ s from hs.mem_nhds hps).and hgf)
  obtain ⟨V, hVeq, hV, hV0⟩ := mem_nhds_iff.mp hnhds
  let e' := e.restrOpen V hV
  refine ⟨e', ⟨he0, hV0⟩, he00, he.mono inter_subset_left,
    hes.mono inter_subset_left, hed, ?_⟩
  intro v hv
  have hfv := hVeq hv.2
  refine ⟨hfv.1, ?_⟩
  rw [← hfv.2, heq v hv.1, hgf.self_of_nhds]
  rfl

/-- Fixed linear normal coordinates for a nondegenerate symmetric real form,
including the exact intrinsic negative index. -/
theorem symmetric_form_signed_coordinates (B : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (hB : ∀ u v, B u v = B v u) :
    ∃ (w : Fin (Module.finrank ℝ E) → ℝ)
      (C : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)),
      (∀ i, w i = -1 ∨ w i = 1) ∧
      (∀ v, B v v = ∑ i, w i * (C v i) ^ 2) ∧
      sigNeg B.toContinuousLinearMap.toBilinForm.toQuadraticMap = {i | w i < 0}.ncard := by
  let L := B.toContinuousLinearMap.toBilinForm
  have hsep : (QuadraticMap.associated (R := ℝ) L.toQuadraticMap).SeparatingLeft := by
    rw [QuadraticMap.associated_left_inverse ℝ (B₁ := L) hB]
    intro v hv
    apply B.injective
    apply ContinuousLinearMap.ext
    intro u
    simpa [L] using hv u
  obtain ⟨w, hw, he⟩ := QuadraticForm.equivalent_one_neg_one_weighted_sum_squared L.toQuadraticMap hsep
  obtain ⟨e⟩ := he
  let C := e.toLinearEquiv.toContinuousLinearEquiv
  refine ⟨w, C, hw, ?_, ?_⟩
  · intro v
    have heq := (e.map_app v).symm
    change B v v = QuadraticMap.weightedSumSquares ℝ w (e v) at heq
    simpa only [C, LinearEquiv.coe_toContinuousLinearEquiv',
      QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
      QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using heq
  · exact QuadraticForm.sigNeg_of_equiv_weightedSumSquares ⟨e⟩

/-- Full local Morse normal form in arbitrary real finite dimension. The
negative weights are counted by the intrinsic signature of the actual Hessian. -/
theorem morse_normal_form {f : E → ℝ} {s : Set E} {p : E}
    (hs : IsOpen s) (hps : p ∈ s) (hf : ContDiffOn ℝ ∞ f s)
    (hp : fderiv ℝ f p = 0) (hH : (fderiv ℝ (fderiv ℝ f) p).IsInvertible) :
    ∃ (w : Fin (Module.finrank ℝ E) → ℝ)
      (e : OpenPartialHomeomorph E (Fin (Module.finrank ℝ E) → ℝ)),
      (∀ i, w i = -1 ∨ w i = 1) ∧
      (0 : E) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ v ∈ e.source, p + v ∈ s ∧
        f (p + v) = f p + ∑ i, w i * (e v i) ^ 2) ∧
      sigNeg (((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) p).toBilinForm.toQuadraticMap) =
        {i | w i < 0}.ncard := by
  obtain ⟨H, hHe⟩ := hH
  let scale := (LinearEquiv.smulOfNeZero ℝ (E →L[ℝ] ℝ) (1 / 2 : ℝ)
    (by norm_num)).toContinuousLinearEquiv
  let B := H.trans scale
  have hBe : B.toContinuousLinearMap = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) p := by
    ext u v
    simp [B, scale]
    exact congrArg (fun D : E →L[ℝ] E →L[ℝ] ℝ => D u v) hHe
  have hB : ∀ u v, B u v = B v u := by
    intro u v
    have hsym := ((hf p hps).contDiffAt (hs.mem_nhds hps)).isSymmSndFDerivAt (by simp)
    change B.toContinuousLinearMap u v = B.toContinuousLinearMap v u
    rw [hBe]
    simp only [ContinuousLinearMap.smul_apply]
    rw [hsym.eq u v]
  obtain ⟨e₀, h0, h00, hsm, hsi, hd, hform⟩ := morse_quadratic_normal_form_on hs hps hf hp B hBe
  obtain ⟨w, C, hw, hC, hindex⟩ := symmetric_form_signed_coordinates B hB
  let e := e₀.trans C.toHomeomorph.toOpenPartialHomeomorph
  have hsource : e.source = e₀.source := by simp [e, OpenPartialHomeomorph.trans_source]
  refine ⟨w, e, hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hsource] using h0
  · change C (e₀ 0) = 0
    rw [h00, map_zero]
  · rw [hsource]
    exact C.contDiff.comp_contDiffOn hsm
  · apply hsi.comp C.symm.contDiff.contDiffOn
    intro y hy
    exact hy.2
  · intro v hv
    have hf0 := hform v (hsource ▸ hv)
    refine ⟨hf0.1, ?_⟩
    rw [hf0.2, hC]
    rfl
  · rwa [hBe] at hindex

end GaussBonnetChern.MorseLocal
