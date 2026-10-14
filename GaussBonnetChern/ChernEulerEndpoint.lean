import GaussBonnetChern.ChernAngularRecurrence
import GaussBonnetChern.ChernPatchGeometry
import GaussBonnetChern.AngularPolynomialLimit
import GaussBonnetChern.PositiveOrthonormalFrames

/-! Identification of Chern's terminal recurrence polynomial with the
actual curvature Euler form, retaining both normalization factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle Filter
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.Chern
open DifferentialForm

private def endpointLeftBlockPerm (r s : ℕ) (τ : Equiv.Perm (Fin r)) :
    Equiv.Perm (Fin (r+s)) :=
  (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r+s)).permCongr
    (Equiv.sumCongr τ (Equiv.refl _))

private theorem endpointSignedSum_left {V : Type*} (r s : ℕ)
    (h : (Fin r → V) → ℝ) (g : (Fin s → V) → ℝ) (v : Fin (r+s) → V) :
    (∑ σ : Equiv.Perm (Fin (r+s)), permutationSignReal σ *
      ((∑ τ : Equiv.Perm (Fin r), permutationSignReal τ *
        h (fun i ↦ v (σ (Fin.castAdd s (τ i))))) *
        g (fun i ↦ v (σ (Fin.natAdd r i))))) =
      (r.factorial : ℝ) * ∑ σ : Equiv.Perm (Fin (r+s)), permutationSignReal σ *
        (h (fun i ↦ v (σ (Fin.castAdd s i))) * g (fun i ↦ v (σ (Fin.natAdd r i)))) := by
  let H : Equiv.Perm (Fin (r+s)) → ℝ := fun σ ↦
    h (fun i ↦ v (σ (Fin.castAdd s i))) * g (fun i ↦ v (σ (Fin.natAdd r i)))
  have he (τ : Equiv.Perm (Fin r)) :
      permutationSignReal (endpointLeftBlockPerm r s τ) = permutationSignReal τ := by
    simp [endpointLeftBlockPerm, permutationSignReal]
  have hτ (τ : Equiv.Perm (Fin r)) :
      (∑ σ : Equiv.Perm (Fin (r+s)),
        permutationSignReal σ * permutationSignReal τ * H (σ * endpointLeftBlockPerm r s τ)) =
        ∑ σ : Equiv.Perm (Fin (r+s)), permutationSignReal σ * H σ := by
    simp_rw [← he τ, ← permutationSignReal_mul]
    exact Equiv.sum_comp (Equiv.mulRight (endpointLeftBlockPerm r s τ))
      (fun σ ↦ permutationSignReal σ * H σ)
  have ha : (∑ σ : Equiv.Perm (Fin (r+s)), ∑ τ : Equiv.Perm (Fin r),
      permutationSignReal σ * permutationSignReal τ * H (σ * endpointLeftBlockPerm r s τ)) =
        (r.factorial : ℝ) * ∑ σ : Equiv.Perm (Fin (r+s)), permutationSignReal σ * H σ := by
    rw [Finset.sum_comm]
    simp_rw [hτ]
    simp [Fintype.card_perm]
  convert ha using 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  simp [H, endpointLeftBlockPerm, Equiv.Perm.mul_apply, mul_assoc]

section Products
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

/-- The raw ordered pair product before direction alternatization. -/
def endpointPairProduct : (n : ℕ) →
    (Fin n → DifferentialForm.Form 𝓘(ℝ,E) P 2) → (x : P) →
    (Fin (2*n) → TangentSpace 𝓘(ℝ,E) x) → ℝ
  | 0, _, _, _ => 1
  | n+1, B, x, v =>
      endpointPairProduct n (fun i ↦ B i.castSucc) x
        (fun i ↦ v ⟨i.val, by have := i.isLt; omega⟩) *
      B (Fin.last n) x ![v ⟨2*n, by omega⟩, v ⟨2*n+1, by omega⟩]

theorem endpointPairProduct_eq_prod (n : ℕ) (B : Fin n → Form 𝓘(ℝ,E) P 2)
    (x : P) (v : Fin (2*n) → TangentSpace 𝓘(ℝ,E) x) :
    endpointPairProduct n B x v = ∏ j : Fin n, B j x ![v (pairFirst j),v (pairSecond j)] := by
  induction n with
  | zero => simp [endpointPairProduct]
  | succ n ih =>
    rw [endpointPairProduct, ih, Fin.prod_univ_castSucc]
    congr 1

/-- The actual normalized n-fold exterior product has exactly one factor
`1/2` per curvature two-form in the full direction alternatization. -/
theorem twoFormProduct_apply_endpoint (n : ℕ) (B : Fin n → Form 𝓘(ℝ,E) P 2)
    (x : P) (v : Fin (2*n) → TangentSpace 𝓘(ℝ,E) x) :
    twoFormProduct n B x v = (2^n : ℝ)⁻¹ *
      signedPermutationSum (endpointPairProduct n B x) v := by
  letI : NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TangentSpace 𝓘(ℝ,E) x) :=
    inferInstanceAs (NormedSpace ℝ E)
  induction n with
  | zero =>
    simp [twoFormProduct, signedPermutationSum, endpointPairProduct,
      permutationSignReal]
    rfl
  | succ n ih =>
    let hc : 2*n+2=2*(n+1) := by omega
    let w : Fin (2*n+2) → TangentSpace 𝓘(ℝ,E) x := v ∘ finCongr hc
    let h : (Fin (2*n) → TangentSpace 𝓘(ℝ,E) x) → ℝ :=
      endpointPairProduct n (fun j ↦ B j.castSucc) x
    let g : (Fin 2 → TangentSpace 𝓘(ℝ,E) x) → ℝ := B (Fin.last n) x
    have hexp : wedgeFiber (twoFormProduct n (fun j ↦ B j.castSucc) x) (B (Fin.last n) x) w =
        ((2*n).factorial : ℝ)⁻¹ * (2:ℝ)⁻¹ * (2^n : ℝ)⁻¹ *
          (∑ σ : Equiv.Perm (Fin (2*n+2)), permutationSignReal σ *
            ((∑ τ : Equiv.Perm (Fin (2*n)), permutationSignReal τ *
              h (fun i ↦ w (σ (Fin.castAdd 2 (τ i))))) *
              g (fun i ↦ w (σ (Fin.natAdd (2*n) i))))) := by
      rw [wedgeFiber_apply_realSign]
      simp_rw [ih]
      simp only [signedPermutationSum]
      simp only [Nat.factorial_two, Nat.cast_ofNat, mul_inv_rev]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      dsimp only [h,g,Function.comp_def]
      rw [← Finset.mul_sum]
      ring
    have hraw : (fun z : Fin (2*n+2) → TangentSpace 𝓘(ℝ,E) x ↦
        h (fun i ↦ z (Fin.castAdd 2 i)) * g (fun i ↦ z (Fin.natAdd (2*n) i))) =
        fun z ↦ endpointPairProduct (n+1) B x (z ∘ (finCongr hc).symm) := by
      funext z
      have ht : (fun j : Fin 2 ↦ z (Fin.natAdd (2*n) j)) =
          ![(z ∘ (finCongr hc).symm) ⟨2*n,by omega⟩,
            (z ∘ (finCongr hc).symm) ⟨2*n+1,by omega⟩] := by
        funext j
        fin_cases j <;> rfl
      dsimp only [h,g]
      rw [ht]
      rfl
    have hsum : (∑ σ : Equiv.Perm (Fin (2*n+2)), permutationSignReal σ *
        (h (fun i ↦ w (σ (Fin.castAdd 2 i))) * g (fun i ↦ w (σ (Fin.natAdd (2*n) i))))) =
        signedPermutationSum (endpointPairProduct (n+1) B x) v := by
      change signedPermutationSum
        (fun z ↦ h (fun i ↦ z (Fin.castAdd 2 i)) * g (fun i ↦ z (Fin.natAdd (2*n) i))) w = _
      rw [hraw]
      rw [signedPermutationSum_domCongr (finCongr hc)]
      congr 1
    have hf : ((2*n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hcoef : ((2*n).factorial : ℝ)⁻¹ * (2:ℝ)⁻¹ * (2^n : ℝ)⁻¹ *
        ((2*n).factorial : ℝ) = (2^(n+1) : ℝ)⁻¹ := by
      rw [pow_succ]
      field_simp
    change wedgeFiber (twoFormProduct n (fun j ↦ B j.castSucc) x) (B (Fin.last n) x) w = _
    rw [hexp, endpointSignedSum_left (2*n) 2 h g w]
    rw [← mul_assoc, hcoef, hsum]

theorem twoFormProduct_apply_full_alternation (n : ℕ)
    (B : Fin n → Form 𝓘(ℝ,E) P 2) (x : P)
    (v : Fin (2*n) → TangentSpace 𝓘(ℝ,E) x) :
    twoFormProduct n B x v = (2^n : ℝ)⁻¹ *
      ∑ τ : Equiv.Perm (Fin (2*n)), (↑(Equiv.Perm.sign τ) : ℝ) *
        ∏ j : Fin n, B j x ![v (τ (pairFirst j)),v (τ (pairSecond j))] := by
  rw [twoFormProduct_apply_endpoint]
  simp only [signedPermutationSum, endpointPairProduct_eq_prod,
    Function.comp_apply, permutationSignReal]

end Products
end GaussBonnetChern.Chern

namespace GaussBonnetChern
open DifferentialForm
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

/-- The top recurrence polynomial in the actual curvature forms has the
exact frozen Euler normalization. No structure-equation premise is needed. -/
theorem recurrencePolynomial_smoothFrame_top_euler
    (b : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x))
    (θ : Fin (2*n) → Form (model n) M 1) :
    Chern.angularCoefficient n n • Chern.recurrencePolynomial n ⟨n,by omega⟩
      θ (smoothFrameCurvatureTwoForm n M b) =
      fun x ↦ frameEulerForm n M x (b x) := by
  rw [Chern.recurrencePolynomial_top, Chern.angularCoefficient_top]
  funext x
  ext v
  simp only [Finset.sum_apply, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sum_apply, smul_eq_mul,
    Chern.twoFormProduct_apply_full_alternation, smoothFrameCurvatureTwoForm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, frameEulerForm_apply,
    frameEulerAlternating, AlternatingMap.smul_apply, alternating_finset_sum_apply,
    alternatingFamilyForm_apply, curvatureDirectionPairing_apply]
  simp_rw [Finset.mul_sum]
  have hc : (1 / ((2:ℝ)^n * (n.factorial:ℝ) * (2*Real.pi)^n)) * (2^n : ℝ)⁻¹ =
      (4^n * (n.factorial:ℝ) * (2*Real.pi)^n)⁻¹ := by
    rw [show (4:ℝ)^n = (2:ℝ)^n * (2:ℝ)^n by rw [← mul_pow]; norm_num]
    simp only [one_div, mul_inv_rev]
    ring
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  rw [← hc]
  ring

end GaussBonnetChern
