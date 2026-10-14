import GaussBonnetChern.ChernProductDifferential
import GaussBonnetChern.ScalarDifferential
import GaussBonnetChern.ChernAngularContraction

/-! Genuine differentiation of the weighted products occurring in `Φ_k`.
This is an expansion into actual derivatives, not an assumed recurrence. -/
noncomputable section
open scoped Manifold ContDiff BigOperators
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section FrameSlotPermutations

/-- Full signed alternation of an actual expression in its frame-index tuple.
No multilinearity assumption is required for this finite reindexing operation. -/
def signedFrameSum {d : ℕ} {W V : Type*} [AddCommGroup V] [Module ℝ V]
    (F : (Fin d → W) → V) (w : Fin d → W) : V :=
  ∑ σ : Equiv.Perm (Fin d), permutationSignReal σ • F (w ∘ σ)

theorem signedFrameSum_domPerm {d : ℕ} {W V : Type*} [AddCommGroup V] [Module ℝ V]
    (F : (Fin d → W) → V) (w : Fin d → W) (τ : Equiv.Perm (Fin d)) :
    signedFrameSum (fun z ↦ F (z ∘ τ)) w =
      permutationSignReal τ • signedFrameSum F w := by
  let H : Equiv.Perm (Fin d) → V := fun σ ↦ permutationSignReal σ • F (w ∘ σ)
  change (∑ σ, permutationSignReal σ • F ((w ∘ σ) ∘ τ)) =
    permutationSignReal τ • ∑ σ, H σ
  rw [← Equiv.sum_comp (Equiv.mulRight τ) H, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  dsimp only [H, Equiv.mulRight]
  change permutationSignReal σ • F ((w ∘ σ) ∘ τ) =
    permutationSignReal τ • (permutationSignReal (σ*τ) •
      F (w ∘ ((σ*τ : Equiv.Perm (Fin d)) : Fin d → Fin d)))
  rw [permutationSignReal_mul, smul_smul]
  have hc : permutationSignReal τ * (permutationSignReal σ * permutationSignReal τ) =
      permutationSignReal σ := by
    calc
      _ = permutationSignReal σ * (permutationSignReal τ * permutationSignReal τ) := by ring
      _ = _ := by rw [permutationSignReal_sq, mul_one]
  rw [hc]
  rfl

/-- Once the concrete factor reindexing identities have been proved, their
permutation signs cancel the Leibniz signs and produce the exact slot count. -/
theorem signedFrameSum_compress {d r : ℕ} {W V : Type*} [AddCommGroup V] [Module ℝ V]
    (F : (Fin d → W) → V) (G : Fin r → (Fin d → W) → V)
    (τ : Fin r → Equiv.Perm (Fin d)) (w : Fin d → W)
    (hG : ∀ i z, G i z = F (z ∘ τ i))
    (hτ : ∀ i, permutationSignReal (τ i) = (-1 : ℝ)^i.val) :
    (∑ i : Fin r, (-1 : ℝ)^i.val • signedFrameSum (G i) w) =
      (r : ℝ) • signedFrameSum F w := by
  have hi (i : Fin r) : (-1 : ℝ)^i.val • signedFrameSum (G i) w = signedFrameSum F w := by
    have heq : G i = fun z ↦ F (z ∘ τ i) := funext (hG i)
    rw [heq, signedFrameSum_domPerm, hτ, smul_smul]
    have hs : (-1 : ℝ)^i.val * (-1 : ℝ)^i.val = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    rw [hs, one_smul]
  simp_rw [hi]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]

/-- Permute only the one-form frame slots, fixing the scalar and curvature slots. -/
def thetaSlotPerm (r k : ℕ) (σ : Equiv.Perm (Fin r)) :
    Equiv.Perm (Fin (1+(r+2*k))) :=
  (finSumFinEquiv : Fin 1 ⊕ Fin (r+2*k) ≃ Fin (1+(r+2*k))).permCongr
    (Equiv.sumCongr (Equiv.refl _)
      ((finSumFinEquiv : Fin r ⊕ Fin (2*k) ≃ Fin (r+2*k)).permCongr
        (Equiv.sumCongr σ (Equiv.refl _))))

theorem sign_thetaSlotPerm (r k : ℕ) (σ : Equiv.Perm (Fin r)) :
    Equiv.Perm.sign (thetaSlotPerm r k σ) = Equiv.Perm.sign σ := by
  simp [thetaSlotPerm]

theorem thetaSlotPerm_scalar (r k : ℕ) (σ : Equiv.Perm (Fin r)) :
    thetaSlotPerm r k σ (Fin.castAdd (r+2*k) (0 : Fin 1)) =
      Fin.castAdd (r+2*k) (0 : Fin 1) := by
  simp [thetaSlotPerm]

theorem thetaSlotPerm_theta (r k : ℕ) (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    thetaSlotPerm r k σ (Fin.natAdd 1 (Fin.castAdd (2*k) i)) =
      Fin.natAdd 1 (Fin.castAdd (2*k) (σ i)) := by
  simp [thetaSlotPerm]

theorem thetaSlotPerm_curvature (r k : ℕ) (σ : Equiv.Perm (Fin r)) (i : Fin (2*k)) :
    thetaSlotPerm r k σ (Fin.natAdd 1 (Fin.natAdd r i)) = Fin.natAdd 1 (Fin.natAdd r i) := by
  simp [thetaSlotPerm]

/-- The concrete permutation bringing a selected direction frame slot first. -/
def thetaPromotionPerm (r k : ℕ) (i : Fin (r+1)) :
    Equiv.Perm (Fin (1+((r+1)+2*k))) := thetaSlotPerm (r+1) k i.cycleRange.symm

theorem sign_thetaPromotionPerm (r k : ℕ) (i : Fin (r+1)) :
    Equiv.Perm.sign (thetaPromotionPerm r k i) = (-1 : ℤˣ)^i.val := by
  rw [thetaPromotionPerm, sign_thetaSlotPerm, Equiv.Perm.sign_symm, Fin.sign_cycleRange]

theorem thetaPromotionPerm_first (r k : ℕ) (i : Fin (r+1)) :
    thetaPromotionPerm r k i (Fin.natAdd 1 (Fin.castAdd (2*k) (0 : Fin (r+1)))) =
      Fin.natAdd 1 (Fin.castAdd (2*k) i) := by
  rw [thetaPromotionPerm, thetaSlotPerm_theta, Fin.cycleRange_symm_zero]

theorem thetaPromotionPerm_tail (r k : ℕ) (i : Fin (r+1)) (j : Fin r) :
    thetaPromotionPerm r k i (Fin.natAdd 1 (Fin.castAdd (2*k) j.succ)) =
      Fin.natAdd 1 (Fin.castAdd (2*k) (i.succAbove j)) := by
  rw [thetaPromotionPerm, thetaSlotPerm_theta, Fin.cycleRange_symm_succ]

end FrameSlotPermutations

section OneFormEvaluation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized exterior product with a one-form is the exact alternating
insertion sum. This identifies connection-wedge terms with directional frame
insertions, with no hidden factorial. -/
theorem wedgeFiber_oneForm_apply {q : ℕ}
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin 1))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin q)) (v : Fin (q+1) → E) :
    wedgeFiber a b (v ∘ finCongr (show 1+q=q+1 by omega)) =
      ∑ i : Fin (q+1), (-1 : ℝ)^i.val * a (fun _ : Fin 1 ↦ v i) * b (i.removeNth v) := by
  let L : E →L[ℝ] ℝ := (ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)).symm a
  let p : E →L[ℝ] ContinuousAlternatingMap ℝ E ℝ (Fin 0) :=
    (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)).toContinuousLinearEquiv.toContinuousLinearMap.comp L
  have hp : ContinuousAlternatingMap.alternatizeUncurryFin p = a := by
    rw [show p = ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0) ∘L L from rfl,
      ContinuousAlternatingMap.alternatizeUncurryFin_constOfIsEmptyLIE_comp]
    exact (ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)).apply_symm_apply a
  let e : Fin (0+q+1) ≃ Fin (q+1) := finCongr (by omega)
  let t : Fin (0+q+1) → E := v ∘ e
  have h := uncurry_wedgeFiber_left (k := 0) (l := q) p b t
  rw [hp] at h
  have ht : t ∘ finCongr (show 0+1+q=0+q+1 by omega) =
      v ∘ finCongr (show 1+q=q+1 by omega) := by
    funext i
    apply congrArg v
    apply Fin.ext
    rfl
  have hv (i : Fin (0+q+1)) :
      (i.removeNth t) ∘ finCongr (Nat.zero_add q).symm = (e i).removeNth v := by
    funext j
    change v (e (i.succAbove (finCongr (Nat.zero_add q).symm j))) =
      v ((e i).succAbove j)
    apply congrArg v
    apply Fin.ext
    simp [e, Fin.succAbove, Fin.lt_def]
    split_ifs <;> rfl
  have hb (i : Fin (0+q+1)) :
      wedgeFiber (p (t i)) b (i.removeNth t) =
        a (fun _ : Fin 1 ↦ t i) * b ((e i).removeNth v) := by
    change wedgeFiber (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (L (t i))) b _ = _
    rw [wedgeFiber_const_left]
    rw [hv]
    simp [L, Function.comp_def]
  rw [ht] at h
  simp_rw [hb] at h
  calc
    _ = ∑ i : Fin (0+q+1), (-1 : ℝ)^i.val *
        (a (fun _ : Fin 1 ↦ t i) * b ((e i).removeNth v)) := h.symm
    _ = _ := by
      simpa only [t, e, Function.comp_def, finCongr_apply, Fin.val_cast, mul_assoc] using
        (Equiv.sum_comp e (fun i : Fin (q+1) ↦ (-1 : ℝ)^i.val *
          (a (fun _ : Fin 1 ↦ v i) * b (i.removeNth v))))

end OneFormEvaluation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

theorem functionSmulLinear_eq_wedge (r : ℕ) (f : P → ℝ)
    (α : Form 𝓘(ℝ,E) P r) :
    functionSmulLinear r f α =
      degreeCastForm (Nat.zero_add r) (wedge (ofFunction f) α) := by
  funext x
  ext v
  rw [degreeCastForm_apply_intrinsic]
  change f x * α x v =
    wedgeFiber (ContinuousAlternatingMap.constOfIsEmpty ℝ _ (Fin 0) (f x)) (α x)
      (v ∘ finCongr (Nat.zero_add r))
  rw [wedgeFiber_const_left]
  congr 2

variable [IsManifold 𝓘(ℝ,E) ∞ P]

theorem isSmooth_functionSmulLinear (r : ℕ) (f : P → ℝ)
    (α : Form 𝓘(ℝ,E) P r) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ f) (hα : IsSmooth α) :
    IsSmooth (functionSmulLinear r f α) := by
  rw [functionSmulLinear_eq_wedge]
  exact IsSmooth.degreeCast _ ((IsSmooth.ofFunction hf).wedge hα)

theorem exteriorDerivative_functionSmulLinear (r : ℕ) (f : P → ℝ)
    (α : Form 𝓘(ℝ,E) P r) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ f) (hα : IsSmooth α) :
    exteriorDerivative (functionSmulLinear r f α) =
      degreeCastForm (show 1+r=r+1 by omega) (wedge (scalarDifferential f) α) +
        functionSmulLinear (r+1) f (exteriorDerivative α) := by
  rw [functionSmulLinear_eq_wedge, exteriorDerivative_degreeCast,
    exteriorDerivative_wedge _ _ (IsSmooth.ofFunction hf) hα,
    exteriorDerivative_ofFunction (hf.mdifferentiable (by simp))]
  funext x
  ext v
  simp only [degreeCastForm_apply_intrinsic, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, Nat.zero_add, Nat.zero_mul, pow_zero,
    one_smul, degreeCastForm_trans]
  change _ = _ + f x * (exteriorDerivative α x) v
  congr 1
  change wedgeFiber (ContinuousAlternatingMap.constOfIsEmpty ℝ _ (Fin 0) (f x))
    (exteriorDerivative α x) _ = _
  rw [wedgeFiber_const_left]
  congr 2

/-- A raw ordered product with one scalar coefficient, exactly the summand
of the original angular polynomial before its final degree transport. -/
def weightedMixedProduct (r k : ℕ) (f : P → ℝ)
    (θ : Fin r → Form 𝓘(ℝ,E) P 1) (B : Fin k → Form 𝓘(ℝ,E) P 2) :
    Form 𝓘(ℝ,E) P (r+2*k) :=
  functionSmulLinear (r+2*k) f (wedge (oneFormProduct r θ) (twoFormProduct k B))

/-- Uncompressed genuine Leibniz formula for the exact products in `Φ_k`.
The curvature term has sign `(-1)^r`; Chern's `r=2n-2k-1` is odd. -/
theorem exteriorDerivative_weightedMixedProduct (r k : ℕ) (f : P → ℝ)
    (θ : Fin r → Form 𝓘(ℝ,E) P 1) (B : Fin k → Form 𝓘(ℝ,E) P 2)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ f)
    (hθ : ∀ i, IsSmooth (θ i)) (hB : ∀ i, IsSmooth (B i)) :
    exteriorDerivative (weightedMixedProduct r k f θ B) =
      degreeCastForm (show 1+(r+2*k)=r+2*k+1 by omega)
        (wedge (scalarDifferential f) (wedge (oneFormProduct r θ) (twoFormProduct k B))) +
      functionSmulLinear (r+2*k+1) f
        (degreeCastForm (show (r+1)+2*k=r+2*k+1 by omega)
          (wedge (∑ i : Fin r, (-1 : ℝ)^i.val •
            oneFormProductReplacement r θ (fun i ↦ exteriorDerivative (θ i)) i)
              (twoFormProduct k B)) +
          (-1 : ℝ)^r • degreeCastForm (show r+(2*k+1)=r+2*k+1 by omega)
            (wedge (oneFormProduct r θ)
              (∑ i : Fin k, twoFormProductReplacement k B (fun i ↦ exteriorDerivative (B i)) i))) := by
  rw [weightedMixedProduct,
    exteriorDerivative_functionSmulLinear _ _ _ hf
      ((isSmooth_oneFormProduct r θ hθ).wedge (isSmooth_twoFormProduct k B hB)),
    exteriorDerivative_wedge _ _ (isSmooth_oneFormProduct r θ hθ)
      (isSmooth_twoFormProduct k B hB),
    exteriorDerivative_oneFormProduct r θ hθ, exteriorDerivative_twoFormProduct k B hB]

/-- The actual unalternated summand of Chern's polynomial, using the original
frame-index embeddings and only the canonical degree transport. -/
def angularSummand (n : ℕ) (k : Fin n)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (σ : Equiv.Perm (Fin (2*n))) : Form 𝓘(ℝ,E) P (2*n-1) :=
  degreeCastForm (show (2*n-2*k.val-1)+2*k.val = 2*n-1 by have := k.isLt; omega)
    (weightedMixedProduct (2*n-2*k.val-1) k.val
      (u (σ ⟨0, by have := k.isLt; omega⟩))
      (fun i ↦ θ (σ (directionIndex k i)))
      (fun j ↦ B (σ (curvatureIndexFirst k j)) (σ (curvatureIndexSecond k j))))

theorem angularTerm_eq_sum_angularSummand (n : ℕ) (k : Fin n)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2) :
    angularTerm n k u θ B =
      ∑ σ : Equiv.Perm (Fin (2*n)), (↑(Equiv.Perm.sign σ) : ℝ) •
        angularSummand n k u θ B σ := by
  unfold angularTerm
  apply Finset.sum_congr rfl
  intro σ _
  apply congrArg (fun α ↦ (↑(Equiv.Perm.sign σ) : ℝ) • α)
  funext x
  ext v
  simp only [angularSummand, weightedMixedProduct, functionSmulLinear,
    LinearMap.mk₂_apply, degreeCastForm_apply_intrinsic, ContinuousAlternatingMap.smul_apply]

theorem isSmooth_angularSummand (n : ℕ) (k : Fin n)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (hu : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (u i))
    (hθ : ∀ i, IsSmooth (θ i)) (hB : ∀ i j, IsSmooth (B i j))
    (σ : Equiv.Perm (Fin (2*n))) : IsSmooth (angularSummand n k u θ B σ) := by
  apply IsSmooth.degreeCast
  apply isSmooth_functionSmulLinear _ _ _ (hu _)
  exact (isSmooth_oneFormProduct _ _ (fun i ↦ hθ _)).wedge
    (isSmooth_twoFormProduct _ _ (fun j ↦ hB _ _))

theorem isSmooth_angularTerm (n : ℕ) (k : Fin n)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (hu : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (u i))
    (hθ : ∀ i, IsSmooth (θ i)) (hB : ∀ i j, IsSmooth (B i j)) :
    IsSmooth (angularTerm n k u θ B) := by
  rw [angularTerm_eq_sum_angularSummand]
  apply IsSmooth.sum
  intro σ _
  exact (isSmooth_angularSummand n k u θ B hu hθ hB σ).const_smul _

/-- The actual derivative commutes with this finite alternation only after
smoothness is established for all genuine summands. -/
theorem exteriorDerivative_angularTerm_expansion (n : ℕ) (k : Fin n)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (hu : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (u i))
    (hθ : ∀ i, IsSmooth (θ i)) (hB : ∀ i j, IsSmooth (B i j)) :
    exteriorDerivative (angularTerm n k u θ B) =
      ∑ σ : Equiv.Perm (Fin (2*n)), (↑(Equiv.Perm.sign σ) : ℝ) •
        degreeCastForm (show ((2*n-2*k.val-1)+2*k.val)+1=(2*n-1)+1 by
          have := k.isLt; omega)
          (exteriorDerivative (weightedMixedProduct (2*n-2*k.val-1) k.val
            (u (σ ⟨0, by have := k.isLt; omega⟩))
            (fun i ↦ θ (σ (directionIndex k i)))
            (fun j ↦ B (σ (curvatureIndexFirst k j)) (σ (curvatureIndexSecond k j))))) := by
  rw [angularTerm_eq_sum_angularSummand,
    exteriorDerivative_sum Finset.univ _ (fun σ _ ↦
      (isSmooth_angularSummand n k u θ B hu hθ hB σ).const_smul _)]
  apply Finset.sum_congr rfl
  intro σ _
  rw [exteriorDerivative_smul, angularSummand, exteriorDerivative_degreeCast]

/-- The alternating directional evaluation of the complete connection-frame
correction is zero. The expression uses the actual Chern polynomial, actual
slot insertions, and actual skew matrices evaluated on the tangent arguments.
Identifying the Leibniz connection terms with this expression is a separate
required step in the derivative recurrence. -/
theorem angularConnectionCorrection_zero (n : ℕ) (k : Fin n)
    (U : (Fin (2*n) → ℝ) →ₗ[ℝ] P → ℝ)
    (Θ : (Fin (2*n) → ℝ) →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : (Fin (2*n) → ℝ) →ₗ[ℝ] (Fin (2*n) → ℝ) →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (x : P) (K : TangentSpace 𝓘(ℝ,E) x → Matrix (Fin (2*n)) (Fin (2*n)) ℝ)
    (hK : ∀ w, (K w).transpose = -K w)
    (v : Fin ((2*n-1)+1) → TangentSpace 𝓘(ℝ,E) x) :
    (∑ s : Fin ((2*n-1)+1), (-1 : ℝ)^s.val *
      ∑ i : Fin (2*n),
        (slotInsertion (angularMultilinear n k U Θ B) (Matrix.toLin' (K (v s))) i).alternatization
          (Pi.basisFun ℝ (Fin (2*n))) x (v ∘ s.succAbove)) = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  have h := congrArg
    (fun α : Form 𝓘(ℝ,E) P (2*n-1) ↦ α x (v ∘ s.succAbove))
    (angularTerm_skew_matrix_insertion n k U Θ B (K (v s)) (hK (v s)))
  simp only [Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
    Pi.zero_apply, ContinuousAlternatingMap.coe_zero] at h
  rw [h, mul_zero]


section InverseContraction
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Solving the actual contraction identity gives exactly the reciprocal
`1/(2k)` used in Chern's recurrence, with no dimension enumeration. -/
theorem mixed_curvature_contraction_inverse (r k : ℕ) (hk : 0 < k)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (hB : ∀ u v, B u v = -B v u)
    (b : Basis (Fin (r+2*k)) ℝ W) (U : W →ₗ[ℝ] ℝ) (u : W) (x : P)
    (hu : U u = 1) (hΘ : Θ u x = 0) :
    (slotInsertion (mixedMultilinear r k Θ B) (U.smulRight u)
      (Fin.natAdd r (pairFirst (⟨0, hk⟩ : Fin k)))).alternatization b x =
      (2*(k : ℝ))⁻¹ • (mixedMultilinear r k Θ B).alternatization b x := by
  have hc : (2*(k : ℝ)) ≠ 0 := by positivity
  rw [mixed_curvature_contraction r k hk Θ B hB b U u x hu hΘ,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

end InverseContraction

end GaussBonnetChern.Chern



