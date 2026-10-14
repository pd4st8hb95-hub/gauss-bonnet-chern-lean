import GaussBonnetChern.ChernCovariantExterior
import GaussBonnetChern.ChernAngularDifferential
import GaussBonnetChern.ChernProductReplacement

noncomputable section
open scoped Manifold ContDiff BigOperators
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false

section CastAlternation
variable {W V : Type*} [AddCommGroup W] [Module ℝ W]
  [AddCommGroup V] [Module ℝ V]

theorem alternatization_domFinCast {r s : ℕ} (h : r = s)
    (F : MultilinearMap ℝ (fun _ : Fin r ↦ W) V) (w : Fin s → W) :
    (F.domDomCongr (finCongr h)).alternatization w = F.alternatization (w ∘ finCongr h) := by
  subst s
  rfl

end CastAlternation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

private theorem recurrenceCast_add {p q : ℕ} (h : p=q)
    (α β : Form 𝓘(ℝ,E) P p) :
    degreeCastForm h (α+β) = degreeCastForm h α + degreeCastForm h β := by
  subst q
  rfl

private theorem recurrenceCast_smul {p q : ℕ} (h : p=q)
    (t : ℝ) (α : Form 𝓘(ℝ,E) P p) :
    degreeCastForm h (t • α) = t • degreeCastForm h α := by
  subst q
  rfl

private theorem recurrenceCast_zero {p q : ℕ} (h : p=q) :
    degreeCastForm (E := E) (M := P) h (0 : Form 𝓘(ℝ,E) P p) = 0 := by
  subst q
  rfl

private theorem recurrenceCast_neg {p q : ℕ} (h : p=q)
    (α : Form 𝓘(ℝ,E) P p) : degreeCastForm h (-α) = -degreeCastForm h α := by
  subst q
  rfl

private theorem recurrence_wedge_neg_left {p q : ℕ}
    (α : Form 𝓘(ℝ,E) P p) (β : Form 𝓘(ℝ,E) P q) :
    wedge (-α) β = -wedge α β :=
  ((wedgeLinear p q).flip β).map_neg α

private theorem recurrence_wedge_smul_left {p q : ℕ} (t : ℝ)
    (α : Form 𝓘(ℝ,E) P p) (β : Form 𝓘(ℝ,E) P q) :
    wedge (t • α) β = t • wedge α β :=
  ((wedgeLinear p q).flip β).map_smul t α

private theorem recurrence_wedge_smul_right {p q : ℕ} (t : ℝ)
    (α : Form 𝓘(ℝ,E) P p) (β : Form 𝓘(ℝ,E) P q) :
    wedge α (t • β) = t • wedge α β := (wedgeLinear p q α).map_smul t β

/-- The original uniform `Y_k` frame expression as a genuine multilinear map,
with the input and output degrees transported by the same arithmetic equality. -/
def recurrenceFrameMultilinear (n : ℕ) (k : Fin (n+1))
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) :
    MultilinearMap ℝ (fun _ : Fin (2*n) ↦ W) (Form 𝓘(ℝ,E) P (2*n)) :=
  (formCastLinear (show (2*n-2*k.val)+2*k.val=2*n by have := k.isLt; omega)).compMultilinearMap
    ((mixedMultilinear (2*n-2*k.val) k.val Θ B).domDomCongr
      (finCongr (show (2*n-2*k.val)+2*k.val=2*n by have := k.isLt; omega)))

theorem recurrenceFrameMultilinear_apply (n : ℕ) (k : Fin (n+1))
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) (w : Fin (2*n) → W) :
    recurrenceFrameMultilinear n k Θ B w =
      degreeCastForm (show (2*n-2*k.val)+2*k.val=2*n by have := k.isLt; omega)
        (wedge (oneFormProduct (2*n-2*k.val)
          (fun i ↦ Θ (w ⟨i.val, by have := i.isLt; omega⟩)))
          (twoFormProduct k.val (fun j ↦ B
            (w ⟨2*n-2*k.val+2*j.val, by have := j.isLt; have := k.isLt; omega⟩)
            (w ⟨2*n-2*k.val+2*j.val+1, by have := j.isLt; have := k.isLt; omega⟩)))) := by
  rw [recurrenceFrameMultilinear, LinearMap.compMultilinearMap_apply,
    MultilinearMap.domDomCongr_apply, mixedMultilinear_apply, formCastLinear_apply]
  apply congrArg (degreeCastForm (show (2*n-2*k.val)+2*k.val=2*n by have := k.isLt; omega))
  apply congrArg₂ wedge
  · apply congrArg (oneFormProduct (2*n-2*k.val))
    funext i
    apply congrArg Θ
    apply congrArg w
    apply Fin.ext
    rfl
  · apply congrArg (twoFormProduct k.val)
    funext j
    apply congrArg₂ (fun a b : W ↦ B a b) <;> apply congrArg w <;> apply Fin.ext <;>
      simp [pairFirst, pairSecond, Nat.add_assoc]

/-- Full alternation is exactly the existing recurrence polynomial; no new
definition of the Pfaffian, Euler form, or `Y_k` is substituted. -/
theorem recurrenceFrameMultilinear_alternatization (n : ℕ) (k : Fin (n+1))
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) (w : Fin (2*n) → W) :
    (recurrenceFrameMultilinear n k Θ B).alternatization w =
      recurrencePolynomial n k (fun i ↦ Θ (w i)) (fun i j ↦ B (w i) (w j)) := by
  rw [MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply, recurrenceFrameMultilinear_apply,
    recurrencePolynomial]
  apply Finset.sum_congr rfl
  intro σ _
  funext x
  ext v
  simp only [Units.smul_def, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, zsmul_eq_mul, smul_eq_mul]

/-- Input-index and output-degree casts commute with actual alternation. -/
theorem recurrenceFrameMultilinear_alternatization_eq_cast (n : ℕ) (k : Fin (n+1))
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) (w : Fin (2*n) → W) :
    (recurrenceFrameMultilinear n k Θ B).alternatization w =
      degreeCastForm (show (2*n-2*k.val)+2*k.val=2*n by have := k.isLt; omega)
        ((mixedMultilinear (2*n-2*k.val) k.val Θ B).alternatization
          (w ∘ finCongr (show (2*n-2*k.val)+2*k.val=2*n by have := k.isLt; omega))) := by
  rw [recurrenceFrameMultilinear, LinearMap.compMultilinearMap_alternatization,
    LinearMap.compAlternatingMap_apply, formCastLinear_apply, alternatization_domFinCast]

/-- Transfer the verified contraction identity to the original `Y_k`
polynomial, retaining both genuine basis reindexing and form-degree transport. -/
theorem recurrencePolynomial_curvature_contraction (n : ℕ) (k : Fin (n+1))
    (hk : 0 < k.val) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) (hB : ∀ u v, B u v = -B v u)
    (b : Basis (Fin (2*n)) ℝ W) (U : W →ₗ[ℝ] ℝ) (u : W) (x : P)
    (hu : U u = 1) (hΘ : Θ u x = 0) :
    recurrencePolynomial n k (fun i ↦ Θ (b i)) (fun i j ↦ B (b i) (b j)) x =
      (2*(k.val : ℝ)) • degreeCastForm
        (show (2*n-2*k.val)+2*k.val=2*n by have := k.isLt; omega)
        ((slotInsertion (mixedMultilinear (2*n-2*k.val) k.val Θ B) (U.smulRight u)
          (Fin.natAdd (2*n-2*k.val) (pairFirst (⟨0, hk⟩ : Fin k.val)))).alternatization
            (b ∘ finCongr (show (2*n-2*k.val)+2*k.val=2*n by have := k.isLt; omega))) x := by
  let e : Fin ((2*n-2*k.val)+2*k.val) ≃ Fin (2*n) :=
    finCongr (show (2*n-2*k.val)+2*k.val=2*n by have := k.isLt; omega)
  let b' : Basis (Fin ((2*n-2*k.val)+2*k.val)) ℝ W := b.reindex e.symm
  have hc := mixed_curvature_contraction (2*n-2*k.val) k.val hk Θ B hB b' U u x hu hΘ
  have hb' : (b' : Fin ((2*n-2*k.val)+2*k.val) → W) = b ∘ e := by
    simp only [b', Basis.coe_reindex, Equiv.symm_symm]
  rw [hb'] at hc
  rw [← recurrenceFrameMultilinear_alternatization,
    recurrenceFrameMultilinear_alternatization_eq_cast]
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [degreeCastForm_apply_intrinsic, ContinuousAlternatingMap.smul_apply]
  exact congrArg (fun α ↦ α (v ∘ e)) hc

end GaussBonnetChern.Chern



noncomputable section
open scoped Manifold ContDiff BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  [IsManifold 𝓘(ℝ,E) ∞ P] {W : Type*}

def directionReplacementExpression (r k : ℕ)
    (U : W → P → ℝ) (Θ : W → Form 𝓘(ℝ,E) P 1)
    (Δ : W → Form 𝓘(ℝ,E) P 2) (B : W → W → Form 𝓘(ℝ,E) P 2)
    (i : Fin (r+1)) (w : Fin (1+((r+1)+2*k)) → W) :
    Form 𝓘(ℝ,E) P ((r+1)+1+2*k) :=
  functionSmulLinear _ (U (w (Fin.castAdd ((r+1)+2*k) (0 : Fin 1))))
    (wedge
      (oneFormProductReplacement (r+1)
        (fun j ↦ Θ (w (Fin.natAdd 1 (Fin.castAdd (2*k) j))))
        (fun j ↦ Δ (w (Fin.natAdd 1 (Fin.castAdd (2*k) j)))) i)
      (twoFormProduct k (fun j ↦ B
        (w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairFirst j))))
        (w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairSecond j)))))))

def directionLeadingExpression (r k : ℕ)
    (U : W → P → ℝ) (Θ : W → Form 𝓘(ℝ,E) P 1)
    (Δ : W → Form 𝓘(ℝ,E) P 2) (B : W → W → Form 𝓘(ℝ,E) P 2)
    (w : Fin (1+((r+1)+2*k)) → W) : Form 𝓘(ℝ,E) P ((r+1)+1+2*k) :=
  functionSmulLinear _ (U (w (Fin.castAdd ((r+1)+2*k) (0 : Fin 1))))
    (wedge
      (degreeCastForm (show 2+r=(r+1)+1 by omega)
        (wedge (Δ (w (Fin.natAdd 1 (Fin.castAdd (2*k) (0 : Fin (r+1))))))
          (oneFormProduct r (fun j ↦ Θ (w (Fin.natAdd 1 (Fin.castAdd (2*k) j.succ)))))))
      (twoFormProduct k (fun j ↦ B
        (w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairFirst j))))
        (w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairSecond j)))))))

/-- Actual replacement summands are the concrete promoted leading summand.
The even derivative form crosses the preceding one-forms with positive sign. -/
theorem directionReplacementExpression_eq_promoted (r k : ℕ)
    (U : W → P → ℝ) (Θ : W → Form 𝓘(ℝ,E) P 1)
    (Δ : W → Form 𝓘(ℝ,E) P 2) (B : W → W → Form 𝓘(ℝ,E) P 2)
    (i : Fin (r+1)) (w : Fin (1+((r+1)+2*k)) → W) :
    directionReplacementExpression r k U Θ Δ (fun v z : W ↦ B v z) i w =
      directionLeadingExpression r k U Θ Δ (fun v z : W ↦ B v z) (w ∘ thetaPromotionPerm r k i) := by
  rw [directionReplacementExpression, oneFormProductReplacement_front]
  unfold directionLeadingExpression
  apply congrArg₂ (fun f α ↦ functionSmulLinear _ f α)
  · exact congrArg (fun t ↦ U (w t))
      (thetaSlotPerm_scalar (r+1) k i.cycleRange.symm).symm
  · apply congrArg₂ wedge
    · apply congrArg (degreeCastForm (show 2+r=(r+1)+1 by omega))
      apply congrArg₂ wedge
      · exact congrArg (fun t ↦ Δ (w t)) (thetaPromotionPerm_first r k i).symm
      · apply congrArg (oneFormProduct r)
        funext j
        exact congrArg (fun t ↦ Θ (w t)) (thetaPromotionPerm_tail r k i j).symm
    · apply congrArg (twoFormProduct k)
      funext j
      exact congrArg₂ (fun s t ↦ B (w s) (w t))
        (thetaSlotPerm_curvature (r+1) k i.cycleRange.symm (pairFirst j)).symm
        (thetaSlotPerm_curvature (r+1) k i.cycleRange.symm (pairSecond j)).symm
/-- The exact arbitrary-dimension compression of all one-form derivative
slots in the actual fully alternated polynomial. -/
theorem directionReplacement_alternation_sum (r k : ℕ)
    (U : W → P → ℝ) (Θ : W → Form 𝓘(ℝ,E) P 1)
    (Δ : W → Form 𝓘(ℝ,E) P 2) (B : W → W → Form 𝓘(ℝ,E) P 2)
    (w : Fin (1+((r+1)+2*k)) → W) :
    (∑ i : Fin (r+1), (-1 : ℝ)^i.val •
      signedFrameSum (directionReplacementExpression r k U Θ Δ (fun v z : W ↦ B v z) i) w) =
      ((r+1 : ℕ) : ℝ) • signedFrameSum (directionLeadingExpression r k U Θ Δ (fun v z : W ↦ B v z)) w := by
  apply signedFrameSum_compress _ _ (thetaPromotionPerm r k) w
  · exact fun i z ↦ directionReplacementExpression_eq_promoted r k U Θ Δ B i z
  · intro i
    rw [permutationSignReal, sign_thetaPromotionPerm]
    simp

end GaussBonnetChern.Chern



noncomputable section
open scoped Manifold ContDiff BigOperators
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  [IsManifold 𝓘(ℝ,E) ∞ P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The checked genuine block rule evaluated on actual multilinear factors. -/
theorem covariantExterior_multilinearBlock {d r s p q : ℕ}
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F : MultilinearMap ℝ (fun _ : Fin r ↦ W) (Form 𝓘(ℝ,E) P p))
    (G : MultilinearMap ℝ (fun _ : Fin s ↦ W) (Form 𝓘(ℝ,E) P q))
    (w : Fin (r+s) → W)
    (hF : IsSmooth (F (fun i ↦ w (Fin.castAdd s i))))
    (hG : IsSmooth (G (fun j ↦ w (Fin.natAdd r j)))) :
    covariantExterior b Γ (multilinearBlock (wedgeLinear p q) F G) w =
      degreeCastForm (show (p+1)+q=p+q+1 by omega)
        (wedge (covariantExterior b Γ F (fun i ↦ w (Fin.castAdd s i)))
          (G (fun j ↦ w (Fin.natAdd r j)))) +
      (-1 : ℝ)^p • degreeCastForm (show p+(q+1)=p+q+1 by omega)
        (wedge (F (fun i ↦ w (Fin.castAdd s i)))
          (covariantExterior b Γ G (fun j ↦ w (Fin.natAdd r j)))) := by
  have heq : (multilinearBlock (wedgeLinear p q) F G :
      (Fin (r+s) → W) → Form 𝓘(ℝ,E) P (p+q)) =
      (fun z ↦ wedge (F (fun i ↦ z (Fin.castAdd s i)))
        (G (fun j ↦ z (Fin.natAdd r j)))) := by
    funext z
    exact multilinearBlock_apply _ _ _ z
  rw [heq]
  exact covariantExterior_block_wedge b Γ F G w hF hG

/-- The corrected derivative of the actual ordered direction product. -/
theorem covariantExterior_oneFormProduct {d : ℕ}
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1) (Δ : W → Form 𝓘(ℝ,E) P 2)
    (hΘ : ∀ v, IsSmooth (Θ v))
    (hCartan : ∀ v, exteriorDerivative (Θ v) =
      Δ v + ∑ j : Fin d, wedge (Γ j v) (Θ (b j)))
    (r : ℕ) (w : Fin r → W) :
    covariantExterior b Γ (oneFormProductMultilinear Θ r) w =
      ∑ i : Fin r, (-1 : ℝ)^i.val •
        oneFormProductReplacement r (fun i ↦ Θ (w i)) (fun i ↦ Δ (w i)) i := by
  induction r with
  | zero =>
    rw [show (oneFormProductMultilinear Θ 0 : (Fin 0 → W) → Form 𝓘(ℝ,E) P 0) =
      (fun _ ↦ ofFunction (fun _ : P ↦ (1 : ℝ))) from rfl]
    rw [covariantExterior_unit]
    simp
  | succ r ih =>
    rw [oneFormProductMultilinear]
    rw [covariantExterior_multilinearBlock b Γ _ _ w]
    · have hc : covariantExterior b Γ
          (MultilinearMap.ofSubsingleton ℝ W _ (0 : Fin 1) Θ)
          (fun i ↦ w (Fin.natAdd r i)) = Δ (w (Fin.last r)) := by
        exact covariantExterior_one_of_Cartan b Γ Θ Δ hCartan _
      rw [hc, ih, Fin.sum_univ_castSucc]
      simp only [oneFormProductReplacement_castSucc, oneFormProductReplacement_last,
        Fin.val_castSucc, Fin.val_last, oneFormProductMultilinear_apply]
      change wedge (∑ i : Fin r, (-1 : ℝ)^i.val •
          oneFormProductReplacement r (fun i ↦ Θ (w i.castSucc))
            (fun i ↦ Δ (w i.castSucc)) i) (Θ (w (Fin.last r))) +
        (-1 : ℝ)^r • wedge (oneFormProduct r (fun i ↦ Θ (w i.castSucc)))
          (Δ (w (Fin.last r))) = _
      congr 1
      change ((wedgeLinear (r+1) 1).flip (Θ (w (Fin.last r)))) _ = _
      rw [map_sum]
      simp_rw [map_smul]
      rfl
    · rw [oneFormProductMultilinear_apply]
      exact isSmooth_oneFormProduct _ _ (fun i ↦ hΘ _)
    · exact hΘ _

/-- Genuine Bianchi plus genuine Leibniz annihilates every ordered curvature product. -/
theorem covariantExterior_twoFormProduct {d : ℕ}
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (hB : ∀ v z, IsSmooth (B v z))
    (hBianchi : ∀ v z, exteriorDerivative (B v z) =
      (∑ j : Fin d, wedge (Γ j v) (B (b j) z)) +
        ∑ j : Fin d, wedge (Γ j z) (B v (b j)))
    (k : ℕ) (w : Fin (2*k) → W) :
    covariantExterior b Γ (twoFormProductMultilinear B k) w = 0 := by
  induction k with
  | zero =>
    exact covariantExterior_unit b Γ w
  | succ k ih =>
    have heq : (twoFormProductMultilinear B (k+1) :
        (Fin (2*(k+1)) → W) → Form 𝓘(ℝ,E) P (2*(k+1))) =
        (fun z ↦ degreeCastForm (show 2*k+2=2*(k+1) by omega)
          (multilinearBlock (wedgeLinear (2*k) 2) (twoFormProductMultilinear B k)
            (bilinearAsMultilinear B)
            (z ∘ finCongr (show 2*k+2=2*(k+1) by omega)))) := by
      funext z
      rw [twoFormProductMultilinear, LinearMap.compMultilinearMap_apply,
        MultilinearMap.domDomCongr_apply, formCastLinear_apply]
      rfl
    rw [heq, covariantExterior_degreeCast, covariantExterior_domDegreeCast]
    rw [covariantExterior_multilinearBlock]
    · rw [ih]
      have hc : covariantExterior b Γ (bilinearAsMultilinear B)
          (fun j : Fin 2 ↦ (w ∘ finCongr (show 2*k+2=2*(k+1) by omega))
            (Fin.natAdd (2*k) j)) = 0 := by
        have hpair : (bilinearAsMultilinear B :
            (Fin 2 → W) → Form 𝓘(ℝ,E) P 2) = (fun z ↦ B (z 0) (z 1)) := rfl
        rw [hpair]
        exact covariantExterior_pair_of_Bianchi b Γ (fun v z : W ↦ B v z) hBianchi
          (fun j : Fin 2 ↦ (w ∘ finCongr (show 2*k+2=2*(k+1) by omega))
            (Fin.natAdd (2*k) j))
      rw [hc]
      simp only [← wedgeLinear_apply, map_zero, LinearMap.zero_apply, recurrenceCast_zero,
        smul_zero, add_zero]
    · rw [twoFormProductMultilinear_apply]
      exact isSmooth_twoFormProduct _ _ (fun i ↦ hB _ _)
    · exact hB _ _

end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold ContDiff BigOperators
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  [IsManifold 𝓘(ℝ,E) ∞ P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The scalar-weighted corrected product rule is derived from the zero-form
wedge rule, with the true scalar Cartan identity. -/
theorem covariantExterior_functionSmul_block {d s p : ℕ}
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (U : W → P → ℝ) (Θ : W → Form 𝓘(ℝ,E) P 1)
    (G : (Fin s → W) → Form 𝓘(ℝ,E) P p) (w : Fin (1+s) → W)
    (hU : ∀ v, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (U v))
    (hCartan : ∀ v, exteriorDerivative (ofFunction (U v)) =
      Θ v + ∑ j : Fin d, functionSmulLinear 1 (U (b j)) (Γ j v))
    (hG : IsSmooth (G (fun i ↦ w (Fin.natAdd 1 i)))) :
    covariantExterior b Γ
      (fun z ↦ functionSmulLinear p (U (z (Fin.castAdd s (0 : Fin 1))))
        (G (fun i ↦ z (Fin.natAdd 1 i)))) w =
      degreeCastForm (show 1+p=p+1 by omega)
        (wedge (Θ (w (Fin.castAdd s (0 : Fin 1)))) (G (fun i ↦ w (Fin.natAdd 1 i)))) +
      functionSmulLinear (p+1) (U (w (Fin.castAdd s (0 : Fin 1))))
        (covariantExterior b Γ G (fun i ↦ w (Fin.natAdd 1 i))) := by
  have heq : (fun z : Fin (1+s) → W ↦
      functionSmulLinear p (U (z (Fin.castAdd s (0 : Fin 1))))
        (G (fun i ↦ z (Fin.natAdd 1 i)))) =
      (fun z ↦ degreeCastForm (Nat.zero_add p)
        (wedge (ofFunction (U (z (Fin.castAdd s (0 : Fin 1)))))
          (G (fun i ↦ z (Fin.natAdd 1 i))))) := by
    funext z
    exact functionSmulLinear_eq_wedge p _ _
  rw [heq, covariantExterior_degreeCast,
    covariantExterior_block_wedge b Γ (fun z : Fin 1 → W ↦ ofFunction (U (z 0))) G w
      (IsSmooth.ofFunction (hU _)) hG,
    covariantExterior_scalar_of_Cartan b Γ U Θ hCartan]
  simp only [pow_zero, one_smul, recurrenceCast_add, degreeCastForm_trans]
  change _ + degreeCastForm (Nat.zero_add (p+1))
      (wedge (ofFunction (U (w (Fin.castAdd s (0 : Fin 1)))))
        (covariantExterior b Γ G (fun i ↦ w (Fin.natAdd 1 i)))) = _
  rw [← functionSmulLinear_eq_wedge]

/-- The genuine corrected derivative of the mixed direction/curvature product.
Bianchi removes the entire curvature-product contribution. -/
theorem covariantExterior_mixedMultilinear {d : ℕ}
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1) (Δ : W → Form 𝓘(ℝ,E) P 2)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (hΘ : ∀ v, IsSmooth (Θ v)) (hB : ∀ v z, IsSmooth (B v z))
    (hCartan : ∀ v, exteriorDerivative (Θ v) =
      Δ v + ∑ j : Fin d, wedge (Γ j v) (Θ (b j)))
    (hBianchi : ∀ v z, exteriorDerivative (B v z) =
      (∑ j : Fin d, wedge (Γ j v) (B (b j) z)) +
        ∑ j : Fin d, wedge (Γ j z) (B v (b j)))
    (r k : ℕ) (w : Fin (r+2*k) → W) :
    covariantExterior b Γ (mixedMultilinear r k Θ B) w =
      degreeCastForm (show (r+1)+2*k=r+2*k+1 by omega)
        (wedge (∑ i : Fin r, (-1 : ℝ)^i.val •
          oneFormProductReplacement r (fun i ↦ Θ (w (Fin.castAdd (2*k) i)))
            (fun i ↦ Δ (w (Fin.castAdd (2*k) i))) i)
          (twoFormProduct k (fun j ↦ B (w (Fin.natAdd r (pairFirst j)))
            (w (Fin.natAdd r (pairSecond j)))))) := by
  rw [mixedMultilinear, covariantExterior_multilinearBlock]
  · rw [covariantExterior_oneFormProduct b Γ Θ Δ hΘ hCartan,
      covariantExterior_twoFormProduct b Γ B hB hBianchi]
    simp only [twoFormProductMultilinear_apply, ← wedgeLinear_apply,
      map_zero, degreeCastForm, smul_zero, add_zero]
  · rw [oneFormProductMultilinear_apply]
    exact isSmooth_oneFormProduct _ _ (fun i ↦ hΘ _)
  · rw [twoFormProductMultilinear_apply]
    exact isSmooth_twoFormProduct _ _ (fun i ↦ hB _ _)

end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold ContDiff BigOperators
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  [IsManifold 𝓘(ℝ,E) ∞ P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The exact multilinear polynomial before angular degree/index transport. -/
def weightedFrameMultilinear (r k : ℕ) (U : W →ₗ[ℝ] P → ℝ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) :
    MultilinearMap ℝ (fun _ : Fin (1+(r+2*k)) ↦ W) (Form 𝓘(ℝ,E) P (r+2*k)) :=
  multilinearBlock (functionSmulLinear (r+2*k))
    (MultilinearMap.ofSubsingleton ℝ W _ (0 : Fin 1) U)
    (mixedMultilinear r k Θ B)

@[simp] theorem weightedFrameMultilinear_apply (r k : ℕ)
    (U : W →ₗ[ℝ] P → ℝ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (w : Fin (1+(r+2*k)) → W) :
    weightedFrameMultilinear r k U Θ B w =
      functionSmulLinear (r+2*k) (U (w (Fin.castAdd (r+2*k) (0 : Fin 1))))
        (mixedMultilinear r k Θ B (fun i ↦ w (Fin.natAdd 1 i))) := by
  rfl

/-- Genuine weighted differentiation after assembling every actual connection
term into the explicit connection variation. -/
theorem covariantExterior_weightedFrameMultilinear {d : ℕ}
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (U : W →ₗ[ℝ] P → ℝ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (Δ : W → Form 𝓘(ℝ,E) P 2)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (hU : ∀ v, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (U v))
    (hΘ : ∀ v, IsSmooth (Θ v)) (hB : ∀ v z, IsSmooth (B v z))
    (hScalar : ∀ v, exteriorDerivative (ofFunction (U v)) =
      Θ v + ∑ j : Fin d, functionSmulLinear 1 (U (b j)) (Γ j v))
    (hCartan : ∀ v, exteriorDerivative (Θ v) =
      Δ v + ∑ j : Fin d, wedge (Γ j v) (Θ (b j)))
    (hBianchi : ∀ v z, exteriorDerivative (B v z) =
      (∑ j : Fin d, wedge (Γ j v) (B (b j) z)) +
        ∑ j : Fin d, wedge (Γ j z) (B v (b j)))
    (r k : ℕ) (w : Fin (1+(r+2*k)) → W) :
    covariantExterior b Γ (weightedFrameMultilinear r k U Θ B) w =
      degreeCastForm (show 1+(r+2*k)=r+2*k+1 by omega)
        (wedge (Θ (w (Fin.castAdd (r+2*k) (0 : Fin 1))))
          (mixedMultilinear r k Θ B (fun i ↦ w (Fin.natAdd 1 i)))) +
      functionSmulLinear (r+2*k+1) (U (w (Fin.castAdd (r+2*k) (0 : Fin 1))))
        (degreeCastForm (show (r+1)+2*k=r+2*k+1 by omega)
          (wedge (∑ i : Fin r, (-1 : ℝ)^i.val •
            oneFormProductReplacement r
              (fun i ↦ Θ (w (Fin.natAdd 1 (Fin.castAdd (2*k) i))))
              (fun i ↦ Δ (w (Fin.natAdd 1 (Fin.castAdd (2*k) i)))) i)
            (twoFormProduct k (fun j ↦ B
              (w (Fin.natAdd 1 (Fin.natAdd r (pairFirst j))))
              (w (Fin.natAdd 1 (Fin.natAdd r (pairSecond j)))))))) := by
  have heq : (weightedFrameMultilinear r k U Θ B :
      (Fin (1+(r+2*k)) → W) → Form 𝓘(ℝ,E) P (r+2*k)) =
      (fun z ↦ functionSmulLinear (r+2*k) (U (z (Fin.castAdd (r+2*k) (0 : Fin 1))))
        (mixedMultilinear r k Θ B (fun i ↦ z (Fin.natAdd 1 i)))) := by
    funext z
    exact weightedFrameMultilinear_apply r k U Θ B z
  rw [heq, covariantExterior_functionSmul_block b Γ U Θ _ w hU hScalar]
  · rw [covariantExterior_mixedMultilinear b Γ Θ Δ B hΘ hB hCartan hBianchi]
  · rw [mixedMultilinear_apply]
    exact (isSmooth_oneFormProduct _ _ (fun i ↦ hΘ _)).wedge
      (isSmooth_twoFormProduct _ _ (fun i ↦ hB _ _))

end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold ContDiff BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false

/-- Move the first pair of frame slots past all remaining direction slots.
The two cycles have equal sign, so this concrete permutation is even. -/
def curvatureLeadingPerm (r k : ℕ) : Equiv.Perm (Fin (1+((r+1)+2*k))) :=
  let i : Fin (1+((r+1)+2*k)) := ⟨r+1, by omega⟩
  i.cycleRange * i.cycleRange

theorem sign_curvatureLeadingPerm (r k : ℕ) :
    permutationSignReal (curvatureLeadingPerm r k) = 1 := by
  unfold curvatureLeadingPerm
  rw [permutationSignReal_mul, permutationSignReal_sq]

theorem curvatureLeadingPerm_theta (r k : ℕ) (i : Fin r) :
    curvatureLeadingPerm r k ⟨i.val, by have := i.isLt; omega⟩ =
      ⟨i.val+2, by have := i.isLt; omega⟩ := by
  let a : Fin (1+((r+1)+2*k)) := ⟨r+1, by omega⟩
  have h₁ : (⟨i.val, by have := i.isLt; omega⟩ : Fin (1+((r+1)+2*k))) < a := by
    change i.val < r+1
    omega
  have h₂ : (a.cycleRange ⟨i.val, by have := i.isLt; omega⟩) < a := by
    rw [Fin.lt_def, Fin.coe_cycleRange_of_lt h₁]
    change i.val+1 < r+1
    omega
  apply Fin.ext
  change (a.cycleRange (a.cycleRange ⟨i.val, by have := i.isLt; omega⟩)).val = i.val+2
  rw [Fin.coe_cycleRange_of_lt h₂, Fin.coe_cycleRange_of_lt h₁]

theorem curvatureLeadingPerm_scalar (r k : ℕ) :
    curvatureLeadingPerm r k ⟨r, by omega⟩ = 0 := by
  let a : Fin (1+((r+1)+2*k)) := ⟨r+1, by omega⟩
  have h₁ : (⟨r, by omega⟩ : Fin (1+((r+1)+2*k))) < a := by
    change r < r+1
    omega
  have h₂ : a.cycleRange ⟨r, by omega⟩ = a := by
    apply Fin.ext
    rw [Fin.coe_cycleRange_of_lt h₁]
  change a.cycleRange (a.cycleRange ⟨r, by omega⟩) = 0
  rw [h₂, Fin.cycleRange_self]

theorem curvatureLeadingPerm_second (r k : ℕ) :
    curvatureLeadingPerm r k ⟨r+1, by omega⟩ = 1 := by
  let a : Fin (1+((r+1)+2*k)) := ⟨r+1, by omega⟩
  have h₀ : (0 : Fin (1+((r+1)+2*k))) < a := by
    change 0 < r+1
    omega
  change a.cycleRange (a.cycleRange a) = 1
  rw [Fin.cycleRange_self, Fin.cycleRange_of_lt h₀]
  simp

theorem curvatureLeadingPerm_curvature (r k : ℕ) (i : Fin (2*k)) :
    curvatureLeadingPerm r k ⟨r+2+i.val, by have := i.isLt; omega⟩ =
      ⟨r+2+i.val, by have := i.isLt; omega⟩ := by
  let a : Fin (1+((r+1)+2*k)) := ⟨r+1, by omega⟩
  have h : a < (⟨r+2+i.val, by have := i.isLt; omega⟩ : Fin (1+((r+1)+2*k))) := by
    change r+1 < r+2+i.val
    omega
  change a.cycleRange (a.cycleRange _) = _
  rw [Fin.cycleRange_of_gt h, Fin.cycleRange_of_gt h]

end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold ContDiff BigOperators
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  [IsManifold 𝓘(ℝ,E) ∞ P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

private theorem recurrenceCast_functionSmul {p q : ℕ} (h : p=q)
    (f : P → ℝ) (α : Form 𝓘(ℝ,E) P p) :
    degreeCastForm h (functionSmulLinear p f α) =
      functionSmulLinear q f (degreeCastForm h α) := by
  subst q
  rfl

theorem signedFrameSum_linear {d : ℕ} {V V' : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
    (L : V →ₗ[ℝ] V') (F : (Fin d → W) → V) (w : Fin d → W) :
    signedFrameSum (fun z ↦ L (F z)) w = L (signedFrameSum F w) := by
  simp only [signedFrameSum, map_sum, map_smul]

theorem signedFrameSum_add {d : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (F G : (Fin d → W) → V) (w : Fin d → W) :
    signedFrameSum (F+G) w = signedFrameSum F w + signedFrameSum G w := by
  simp only [signedFrameSum, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem signedFrameSum_sum {d : ℕ} {V : Type*} {ι : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (F : ι → (Fin d → W) → V) (w : Fin d → W) :
    signedFrameSum (∑ i, F i) w = ∑ i, signedFrameSum (F i) w := by
  simp only [signedFrameSum, Finset.sum_apply, Finset.smul_sum]
  rw [Finset.sum_comm]

/-- The actual scalar Cartan contribution, before identifying its first one-form
with the existing recurrence polynomial. -/
def scalarLeadingExpression (r k : ℕ)
    (Θ : W → Form 𝓘(ℝ,E) P 1) (B : W → W → Form 𝓘(ℝ,E) P 2)
    (w : Fin (1+(r+2*k)) → W) : Form 𝓘(ℝ,E) P (r+2*k+1) :=
  degreeCastForm (show 1+(r+2*k)=r+2*k+1 by omega)
    (wedge (Θ (w (Fin.castAdd (r+2*k) (0 : Fin 1))))
      (wedge (oneFormProduct r (fun i ↦ Θ (w (Fin.natAdd 1 (Fin.castAdd (2*k) i)))))
        (twoFormProduct k (fun j ↦ B (w (Fin.natAdd 1 (Fin.natAdd r (pairFirst j))))
          (w (Fin.natAdd 1 (Fin.natAdd r (pairSecond j))))))))

/-- Exact raw weighted derivative as a scalar leading term and the finitely
many actual direction replacements, with canonical degree transport. -/
theorem covariantExterior_weightedFrameMultilinear_replacements {d : ℕ}
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (U : W →ₗ[ℝ] P → ℝ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (Δ : W → Form 𝓘(ℝ,E) P 2)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (hU : ∀ v, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (U v))
    (hΘ : ∀ v, IsSmooth (Θ v)) (hB : ∀ v z, IsSmooth (B v z))
    (hScalar : ∀ v, exteriorDerivative (ofFunction (U v)) =
      Θ v + ∑ j : Fin d, functionSmulLinear 1 (U (b j)) (Γ j v))
    (hCartan : ∀ v, exteriorDerivative (Θ v) =
      Δ v + ∑ j : Fin d, wedge (Γ j v) (Θ (b j)))
    (hBianchi : ∀ v z, exteriorDerivative (B v z) =
      (∑ j : Fin d, wedge (Γ j v) (B (b j) z)) +
        ∑ j : Fin d, wedge (Γ j z) (B v (b j)))
    (r k : ℕ) (w : Fin (1+((r+1)+2*k)) → W) :
    covariantExterior b Γ (weightedFrameMultilinear (r+1) k U Θ B) w =
      scalarLeadingExpression (r+1) k Θ (fun v z : W ↦ B v z) w +
      ∑ i : Fin (r+1), (-1 : ℝ)^i.val •
        degreeCastForm (show (r+1)+1+2*k=(r+1)+2*k+1 by omega)
          (directionReplacementExpression r k U Θ Δ (fun v z : W ↦ B v z) i w) := by
  rw [covariantExterior_weightedFrameMultilinear b Γ U Θ Δ B hU hΘ hB hScalar hCartan hBianchi,
    mixedMultilinear_apply]
  change scalarLeadingExpression (r+1) k Θ (fun v z : W ↦ B v z) w +
      functionSmulLinear _ _ (degreeCastForm _
        (wedge (∑ i : Fin (r+1), (-1 : ℝ)^i.val • _) _)) = _
  congr 1
  let L := (functionSmulLinear _ (U (w (Fin.castAdd ((r+1)+2*k) (0 : Fin 1))))).comp
    ((formCastLinear (show ((r+1)+1)+2*k=(r+1)+2*k+1 by omega)).comp
      ((wedgeLinear ((r+1)+1) (2*k)).flip (twoFormProduct k (fun j ↦ B
        (w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairFirst j))))
        (w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairSecond j))))))))
  rw [← formCastLinear_apply (show ((r+1)+1)+2*k=(r+1)+2*k+1 by omega)]
  change L (∑ i : Fin (r+1), (-1 : ℝ)^i.val • _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  apply congrArg (fun α ↦ (-1 : ℝ)^i.val • α)
  have hcast := (recurrenceCast_functionSmul
    (show ((r+1)+1)+2*k=(r+1)+2*k+1 by omega)
    (U (w (Fin.castAdd ((r+1)+2*k) (0 : Fin 1))))
    (wedge
      (oneFormProductReplacement (r+1)
        (fun j ↦ Θ (w (Fin.natAdd 1 (Fin.castAdd (2*k) j))))
        (fun j ↦ Δ (w (Fin.natAdd 1 (Fin.castAdd (2*k) j)))) i)
      (twoFormProduct k (fun j ↦ B
        (w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairFirst j))))
        (w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairSecond j)))))))).symm
  simpa only [L, LinearMap.comp_apply, LinearMap.flip_apply, wedgeLinear_apply,
    formCastLinear_apply, directionReplacementExpression] using hcast

end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold ContDiff BigOperators
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  [IsManifold 𝓘(ℝ,E) ∞ P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem signedFrameSum_smul {d : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (t : ℝ) (F : (Fin d → W) → V) (w : Fin d → W) :
    signedFrameSum (t • F) w = t • signedFrameSum F w := by
  simp only [signedFrameSum, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact smul_comm _ _ _

/-- Genuine differentiation of the full alternating angular polynomial,
with all explicit connection terms cancelled and every direction derivative
compressed to its exact leading slot count. -/
theorem exteriorDerivative_weightedFrameMultilinear_compressed (r k : ℕ)
    (b : Basis (Fin (1+((r+1)+2*k))) ℝ W)
    (Γ : Fin (1+((r+1)+2*k)) → W → Form 𝓘(ℝ,E) P 1)
    (U : W →ₗ[ℝ] P → ℝ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (Δ : W → Form 𝓘(ℝ,E) P 2)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (hΓ : ∀ i j, Γ i (b j) = -Γ j (b i))
    (hU : ∀ v, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (U v))
    (hΘ : ∀ v, IsSmooth (Θ v)) (hB : ∀ v z, IsSmooth (B v z))
    (hScalar : ∀ v, exteriorDerivative (ofFunction (U v)) =
      Θ v + ∑ j, functionSmulLinear 1 (U (b j)) (Γ j v))
    (hCartan : ∀ v, exteriorDerivative (Θ v) =
      Δ v + ∑ j, wedge (Γ j v) (Θ (b j)))
    (hBianchi : ∀ v z, exteriorDerivative (B v z) =
      (∑ j, wedge (Γ j v) (B (b j) z)) +
        ∑ j, wedge (Γ j z) (B v (b j))) :
    exteriorDerivative ((weightedFrameMultilinear (r+1) k U Θ B).alternatization b) =
      signedFrameSum (scalarLeadingExpression (r+1) k Θ (fun v z : W ↦ B v z)) b +
      degreeCastForm (show (r+1)+1+2*k=(r+1)+2*k+1 by omega)
        (((r+1 : ℕ) : ℝ) • signedFrameSum (directionLeadingExpression r k U Θ Δ (fun v z : W ↦ B v z)) b) := by
  have hSmooth (σ : Equiv.Perm (Fin (1+((r+1)+2*k)))) :
      IsSmooth (weightedFrameMultilinear (r+1) k U Θ B (b ∘ σ)) := by
    rw [weightedFrameMultilinear_apply, mixedMultilinear_apply]
    exact isSmooth_functionSmulLinear _ _ _ (hU _)
      ((isSmooth_oneFormProduct _ _ (fun i ↦ hΘ _)).wedge
        (isSmooth_twoFormProduct _ _ (fun i ↦ hB _ _)))
  rw [exteriorDerivative_alternatization_eq_covariantExterior _ b Γ hΓ hSmooth]
  change signedFrameSum (covariantExterior b Γ
    (weightedFrameMultilinear (r+1) k U Θ B)) b = _
  have hC : covariantExterior b Γ (weightedFrameMultilinear (r+1) k U Θ B) =
      scalarLeadingExpression (r+1) k Θ (fun v z : W ↦ B v z) +
        ∑ i : Fin (r+1), (-1 : ℝ)^i.val •
          (fun w ↦ degreeCastForm (show (r+1)+1+2*k=(r+1)+2*k+1 by omega)
            (directionReplacementExpression r k U Θ Δ (fun v z : W ↦ B v z) i w)) := by
    funext w
    simpa only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply] using
      covariantExterior_weightedFrameMultilinear_replacements
        b Γ U Θ Δ B hU hΘ hB hScalar hCartan hBianchi r k w
  rw [hC, signedFrameSum_add, signedFrameSum_sum]
  simp_rw [signedFrameSum_smul]
  congr 1
  let L := formCastLinear (E := E) (P := P)
    (show (r+1)+1+2*k=(r+1)+2*k+1 by omega)
  simp_rw [← formCastLinear_apply (show (r+1)+1+2*k=(r+1)+2*k+1 by omega)]
  change (∑ i : Fin (r+1), (-1 : ℝ)^i.val •
      signedFrameSum (fun z ↦ L (directionReplacementExpression r k U Θ Δ (fun v z : W ↦ B v z) i z)) b) =
    L (((r+1 : ℕ) : ℝ) • signedFrameSum (directionLeadingExpression r k U Θ Δ (fun v z : W ↦ B v z)) b)
  simp_rw [signedFrameSum_linear, ← map_smul]
  rw [← map_sum, directionReplacement_alternation_sum]

end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold ContDiff BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Splitting the first genuine direction factor identifies the scalar
Cartan term with the exact mixed polynomial, with no normalization change. -/
theorem scalarLeadingExpression_eq_mixed (r k : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (w : Fin (1+(r+2*k)) → W) :
    degreeCastForm (show r+2*k+1=(r+1)+2*k by omega)
      (scalarLeadingExpression r k Θ (fun v z : W ↦ B v z) w) =
      mixedMultilinear (r+1) k Θ B
        (w ∘ finCongr (show (r+1)+2*k=1+(r+2*k) by omega)) := by
  let a := Θ (w (Fin.castAdd (r+2*k) (0 : Fin 1)))
  let T := oneFormProduct r (fun i ↦ Θ (w (Fin.natAdd 1 (Fin.castAdd (2*k) i))))
  let Q := twoFormProduct k (fun j ↦ B
    (w (Fin.natAdd 1 (Fin.natAdd r (pairFirst j))))
    (w (Fin.natAdd 1 (Fin.natAdd r (pairSecond j)))))
  have hRight : mixedMultilinear (r+1) k Θ B
        (w ∘ finCongr (show (r+1)+2*k=1+(r+2*k) by omega)) =
      wedge (degreeCastForm (show 1+r=r+1 by omega) (wedge a T)) Q := by
    rw [mixedMultilinear_apply, oneFormProduct_cons]
    apply congrArg₂ wedge
    · apply congrArg (degreeCastForm (show 1+r=r+1 by omega))
      apply congrArg₂ wedge
      · apply congrArg Θ
        apply congrArg w
        apply Fin.ext
        rfl
      · apply congrArg (oneFormProduct r)
        funext i
        apply congrArg Θ
        apply congrArg w
        apply Fin.ext
        simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ]
        omega
    · apply congrArg (twoFormProduct k)
      funext j
      apply congrArg₂ (fun a b : W ↦ B a b) <;> apply congrArg w <;> apply Fin.ext <;>
        simp [pairFirst, pairSecond] <;> omega
  rw [hRight, degreeCastForm_wedge_left]
  unfold scalarLeadingExpression
  rw [degreeCastForm_trans]
  change degreeCastForm (show 1+(r+2*k)=(r+1)+2*k by omega) (wedge a (wedge T Q)) =
    degreeCastForm (show (1+r)+2*k=(r+1)+2*k by omega) (wedge (wedge a T) Q)
  rw [← wedge_assoc, degreeCastForm_trans]

end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold ContDiff BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The actual first-curvature rank-one insertion, split into its first
curvature factor and the remaining ordered products. -/
theorem mixed_slotInsertion_first_curvature_apply (r k : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (U : W →ₗ[ℝ] ℝ) (u : W) (w : Fin (r+2*(k+1)) → W) :
    slotInsertion (mixedMultilinear r (k+1) Θ B) (U.smulRight u)
      (Fin.natAdd r (pairFirst (0 : Fin (k+1)))) w =
      degreeCastForm (show r+(2+2*k)=r+2*(k+1) by omega)
        (wedge (oneFormProduct r (fun i ↦ Θ (w (Fin.castAdd (2*(k+1)) i))))
          (wedge ((U (w (Fin.natAdd r (pairFirst (0 : Fin (k+1)))))) •
            B u (w (Fin.natAdd r (pairSecond (0 : Fin (k+1))))))
            (twoFormProduct k (fun j ↦ B
              (w (Fin.natAdd r (pairFirst j.succ)))
              (w (Fin.natAdd r (pairSecond j.succ))))))) := by
  let a := Fin.natAdd r (pairFirst (0 : Fin (k+1)))
  let w' := Function.update w a ((U.smulRight u) (w a))
  have ht : (fun i : Fin r ↦ Θ (w' (Fin.castAdd (2*(k+1)) i))) =
      (fun i : Fin r ↦ Θ (w (Fin.castAdd (2*(k+1)) i))) := by
    funext i
    apply congrArg Θ
    change Function.update w a _ _ = _
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    simp only [a, Fin.val_castAdd, Fin.val_natAdd, pairFirst, Fin.val_mk] at hv
    have := i.isLt
    omega
  have hsecond : w' (Fin.natAdd r (pairSecond (0 : Fin (k+1)))) =
      w (Fin.natAdd r (pairSecond (0 : Fin (k+1)))) := by
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    simp [a, pairFirst, pairSecond] at hv
  have htail (j : Fin k) :
      B (w' (Fin.natAdd r (pairFirst j.succ)))
        (w' (Fin.natAdd r (pairSecond j.succ))) =
      B (w (Fin.natAdd r (pairFirst j.succ)))
        (w (Fin.natAdd r (pairSecond j.succ))) := by
    apply congrArg₂ (fun a b : W ↦ B a b)
    · apply Function.update_of_ne
      intro h
      have hv := congrArg Fin.val h
      simp only [a, Fin.val_natAdd, pairFirst, Fin.val_mk, Fin.val_succ, Fin.val_zero] at hv
      omega
    · apply Function.update_of_ne
      intro h
      have hv := congrArg Fin.val h
      simp only [a, Fin.val_natAdd, pairFirst, pairSecond, Fin.val_mk,
        Fin.val_succ, Fin.val_zero] at hv
      omega
  rw [slotInsertion_apply, mixedMultilinear_apply]
  change wedge (oneFormProduct r (fun i ↦ Θ (w' (Fin.castAdd (2*(k+1)) i))))
    (twoFormProduct (k+1) (fun j ↦ B (w' (Fin.natAdd r (pairFirst j)))
      (w' (Fin.natAdd r (pairSecond j))))) = _
  rw [ht, twoFormProduct_cons, degreeCastForm_wedge_right]
  apply congrArg (degreeCastForm (show r+(2+2*k)=r+2*(k+1) by omega))
  apply congrArg₂ wedge rfl
  apply congrArg₂ wedge
  · rw [hsecond]
    change B (Function.update w a ((U.smulRight u) (w a)) a) _ = _
    rw [Function.update_self]
    exact congrArg (fun L ↦ L (w (Fin.natAdd r (pairSecond (0 : Fin (k+1))))))
      (B.map_smul (U (w a)) u)
  · apply congrArg (twoFormProduct k)
    funext j
    exact htail j

end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold ContDiff BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

private theorem recurrence_even_two_move {r q : ℕ}
    (T : Form 𝓘(ℝ,E) P r) (A : Form 𝓘(ℝ,E) P 2) (Q : Form 𝓘(ℝ,E) P q) :
    degreeCastForm (show r+(2+q)=(2+r)+q by omega) (wedge T (wedge A Q)) =
      wedge (wedge A T) Q := by
  rw [← wedge_assoc, degreeCastForm_trans]
  rw [← degreeCastForm_wedge_left (Nat.add_comm r 2), wedge_degreeCast_comm]
  have hs : (-1 : ℝ)^(r*2) = 1 := by
    rw [Nat.mul_comm r 2, pow_mul, neg_one_sq, one_pow]
  rw [hs, one_smul]

/-- Move the genuine curvature two-form past the direction block and retain
the scalar weight. This is a form identity, with no derivative assumption. -/
private theorem recurrence_leading_product_neg (r k : ℕ) (t : ℝ)
    (T : Form 𝓘(ℝ,E) P r) (A : Form 𝓘(ℝ,E) P 2)
    (Q : Form 𝓘(ℝ,E) P (2*k)) :
    functionSmulLinear ((r+1)+1+2*k) (fun _ : P ↦ t)
      (wedge (degreeCastForm (show 2+r=(r+1)+1 by omega) (wedge (-A) T)) Q) =
      -degreeCastForm (show r+(2+2*k)=(r+1)+1+2*k by omega)
        (wedge T (wedge (t • A) Q)) := by
  have hconstant (α : Form 𝓘(ℝ,E) P ((r+1)+1+2*k)) :
      functionSmulLinear ((r+1)+1+2*k) (fun _ : P ↦ t) α = t • α := by
    funext x
    rfl
  have hmove := congrArg
    (degreeCastForm (show (2+r)+2*k=(r+1)+1+2*k by omega))
    (recurrence_even_two_move T A Q)
  simp only [degreeCastForm_trans] at hmove
  rw [hconstant, recurrence_wedge_neg_left, recurrenceCast_neg,
    recurrence_wedge_neg_left, smul_neg, recurrence_wedge_smul_left,
    recurrence_wedge_smul_right, recurrenceCast_smul, degreeCastForm_wedge_left, hmove]

/-- Exact algebraic identification of the leading direction contribution
with the first curvature rank-one insertion. The only minus sign is the true
skew relation `B(v,u)=-B(u,v)`. -/
theorem directionLeadingExpression_eq_neg_insertion (r k : ℕ)
    (U : W →ₗ[ℝ] ℝ) (u : W)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (hB : ∀ v z, B v z = -B z v)
    (w : Fin (1+((r+1)+2*k)) → W) :
    directionLeadingExpression r k (fun (v : W) (_ : P) ↦ U v) Θ (fun v ↦ B v u) (fun v z : W ↦ B v z) w =
      -degreeCastForm (show r+2*(k+1)=(r+1)+1+2*k by omega)
        (slotInsertion (mixedMultilinear r (k+1) Θ B) (U.smulRight u)
          (Fin.natAdd r (pairFirst (0 : Fin (k+1))))
          ((w ∘ curvatureLeadingPerm r k) ∘
            finCongr (show r+2*(k+1)=1+((r+1)+2*k) by omega))) := by
  let e := finCongr (show r+2*(k+1)=1+((r+1)+2*k) by omega)
  let z := (w ∘ curvatureLeadingPerm r k) ∘ e
  have ht (i : Fin r) : z (Fin.castAdd (2*(k+1)) i) =
      w (Fin.natAdd 1 (Fin.castAdd (2*k) i.succ)) := by
    change w (curvatureLeadingPerm r k (e (Fin.castAdd (2*(k+1)) i))) = _
    have he : e (Fin.castAdd (2*(k+1)) i) = ⟨i.val, by have := i.isLt; omega⟩ := by
      apply Fin.ext; rfl
    rw [he, curvatureLeadingPerm_theta]
    apply congrArg w
    apply Fin.ext
    simp only [Fin.val_mk, Fin.val_natAdd, Fin.val_castAdd, Fin.val_succ]
    omega
  have ha : z (Fin.natAdd r (pairFirst (0 : Fin (k+1)))) =
      w (Fin.castAdd ((r+1)+2*k) (0 : Fin 1)) := by
    change w (curvatureLeadingPerm r k (e _)) = _
    have he : e (Fin.natAdd r (pairFirst (0 : Fin (k+1)))) = ⟨r, by omega⟩ := by
      apply Fin.ext; simp [e, pairFirst]
    rw [he, curvatureLeadingPerm_scalar]
    rfl
  have hz : z (Fin.natAdd r (pairSecond (0 : Fin (k+1)))) =
      w (Fin.natAdd 1 (Fin.castAdd (2*k) (0 : Fin (r+1)))) := by
    change w (curvatureLeadingPerm r k (e _)) = _
    have he : e (Fin.natAdd r (pairSecond (0 : Fin (k+1)))) = ⟨r+1, by omega⟩ := by
      apply Fin.ext
      simp [e, pairSecond, Nat.mod_eq_of_lt (show 1 < 2*(k+1) by omega)]
    rw [he, curvatureLeadingPerm_second]
    apply congrArg w
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (show 1 < 1+((r+1)+2*k) by omega)]
  have hfirst (j : Fin k) : z (Fin.natAdd r (pairFirst j.succ)) =
      w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairFirst j))) := by
    change w (curvatureLeadingPerm r k (e _)) = _
    have he : e (Fin.natAdd r (pairFirst j.succ)) =
        ⟨r+2+(pairFirst j).val, by have := j.isLt; simp [pairFirst] at *; omega⟩ := by
      apply Fin.ext; simp [e, pairFirst]; omega
    rw [he, curvatureLeadingPerm_curvature]
    apply congrArg w
    apply Fin.ext
    simp [pairFirst]
    omega
  have hsecond (j : Fin k) : z (Fin.natAdd r (pairSecond j.succ)) =
      w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairSecond j))) := by
    change w (curvatureLeadingPerm r k (e _)) = _
    have he : e (Fin.natAdd r (pairSecond j.succ)) =
        ⟨r+2+(pairSecond j).val, by have := j.isLt; simp [pairSecond] at *; omega⟩ := by
      apply Fin.ext; simp [e, pairSecond]; omega
    rw [he, curvatureLeadingPerm_curvature]
    apply congrArg w
    apply Fin.ext
    simp [pairSecond]
    omega
  rw [mixed_slotInsertion_first_curvature_apply]
  change _ = -degreeCastForm _ (degreeCastForm _
    (wedge
      (oneFormProduct r (fun i ↦ Θ (z (Fin.castAdd (2*(k+1)) i))))
      (wedge
        (U (z (Fin.natAdd r (pairFirst (0 : Fin (k+1))))) •
          B u (z (Fin.natAdd r (pairSecond (0 : Fin (k+1))))))
        (twoFormProduct k (fun j ↦ B
          (z (Fin.natAdd r (pairFirst j.succ)))
          (z (Fin.natAdd r (pairSecond j.succ))))))))
  simp_rw [ht, ha, hz, hfirst, hsecond]
  unfold directionLeadingExpression
  simp only [degreeCastForm_trans,
    hB (w (Fin.natAdd 1 (Fin.castAdd (2*k) (0 : Fin (r+1))))) u]
  exact recurrence_leading_product_neg r k
    (U (w (Fin.castAdd ((r+1)+2*k) (0 : Fin 1))))
    (oneFormProduct r (fun i ↦ Θ (w (Fin.natAdd 1 (Fin.castAdd (2*k) i.succ)))))
    (B u (w (Fin.natAdd 1 (Fin.castAdd (2*k) (0 : Fin (r+1))))))
    (twoFormProduct k (fun j ↦ B
      (w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairFirst j))))
      (w (Fin.natAdd 1 (Fin.natAdd (r+1) (pairSecond j))))))

end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold ContDiff BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The algebraic leading expression depends only on its actual pointwise
scalar and curvature-direction values; no smoothness of a frozen unit vector
or extension from the patch is required. -/
theorem directionLeadingExpression_congr_at (r k : ℕ)
    (U U' : W → P → ℝ) (Θ : W → Form 𝓘(ℝ,E) P 1)
    (Δ Δ' : W → Form 𝓘(ℝ,E) P 2) (B : W → W → Form 𝓘(ℝ,E) P 2)
    (w : Fin (1+((r+1)+2*k)) → W) (x : P)
    (hU : ∀ v, U v x = U' v x) (hΔ : ∀ v, Δ v x = Δ' v x) :
    directionLeadingExpression r k U Θ Δ (fun v z : W ↦ B v z) w x =
      directionLeadingExpression r k U' Θ Δ' B w x := by
  have hδ :
      degreeCastForm (show 2+r=(r+1)+1 by omega)
        (wedge (Δ (w (Fin.natAdd 1 (Fin.castAdd (2*k) (0 : Fin (r+1))))))
          (oneFormProduct r (fun j ↦ Θ (w (Fin.natAdd 1 (Fin.castAdd (2*k) j.succ)))))) x =
      degreeCastForm (show 2+r=(r+1)+1 by omega)
        (wedge (Δ' (w (Fin.natAdd 1 (Fin.castAdd (2*k) (0 : Fin (r+1))))))
          (oneFormProduct r (fun j ↦ Θ (w (Fin.natAdd 1 (Fin.castAdd (2*k) j.succ)))))) x := by
    ext v
    simp only [degreeCastForm_apply_intrinsic, wedge]
    rw [hΔ]
  ext v
  simp only [directionLeadingExpression, functionSmulLinear, LinearMap.mk₂_apply,
    ContinuousAlternatingMap.smul_apply, wedge]
  rw [hU, hδ]

/-- Finite signed alternation is the true multilinear alternatization. -/
theorem signedFrameSum_multilinear {d : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (F : MultilinearMap ℝ (fun _ : Fin d ↦ W) V) (w : Fin d → W) :
    signedFrameSum F w = F.alternatization w := by
  exact (chernAlternatization_apply_realSign F w).symm

/-- The exact leading direction alternation is the negative curvature
rank-one contraction, with the concrete even permutation eliminated. -/
theorem directionLeadingExpression_alternation_eq_neg_insertion (r k : ℕ)
    (U : W →ₗ[ℝ] ℝ) (u : W)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (hB : ∀ v z, B v z = -B z v)
    (w : Fin (1+((r+1)+2*k)) → W) :
    signedFrameSum (directionLeadingExpression r k (fun (v : W) (_ : P) ↦ U v) Θ
      (fun v ↦ B v u) (fun v z : W ↦ B v z)) w =
      -degreeCastForm (show r+2*(k+1)=(r+1)+1+2*k by omega)
        ((slotInsertion (mixedMultilinear r (k+1) Θ B) (U.smulRight u)
          (Fin.natAdd r (pairFirst (0 : Fin (k+1))))).alternatization
          (w ∘ finCongr (show r+2*(k+1)=1+((r+1)+2*k) by omega))) := by
  let e := finCongr (show r+2*(k+1)=1+((r+1)+2*k) by omega)
  let F := (slotInsertion (mixedMultilinear r (k+1) Θ B) (U.smulRight u)
    (Fin.natAdd r (pairFirst (0 : Fin (k+1))))).domDomCongr e
  let L := -(formCastLinear (E := E) (P := P)
    (show r+2*(k+1)=(r+1)+1+2*k by omega))
  have heq : directionLeadingExpression r k (fun (v : W) (_ : P) ↦ U v) Θ (fun v ↦ B v u) (fun v z : W ↦ B v z) =
      (fun z ↦ L (F (z ∘ curvatureLeadingPerm r k))) := by
    funext z
    simpa only [L, F, e, LinearMap.neg_apply, formCastLinear_apply,
      MultilinearMap.domDomCongr_apply, Function.comp_def] using
        directionLeadingExpression_eq_neg_insertion r k U u Θ B hB z
  rw [heq, signedFrameSum_linear, signedFrameSum_domPerm,
    sign_curvatureLeadingPerm, one_smul, signedFrameSum_multilinear]
  simp only [L, F, e, LinearMap.neg_apply, formCastLinear_apply]
  rw [alternatization_domFinCast]

end GaussBonnetChern.Chern


