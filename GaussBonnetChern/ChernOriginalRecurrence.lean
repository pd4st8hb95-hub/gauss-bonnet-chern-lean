import GaussBonnetChern.ChernDifferentialRecurrence

/-! # The actual Chern derivative recurrence

The unit direction is frozen only for pointwise multilinear algebra. Every
exterior derivative below is taken on the original smooth varying form data.
The supplied primitive Cartan/Bianchi equalities are equalities for actual d.
-/
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

private theorem originalCast_smul {p q : ℕ} (h : p=q) (t : ℝ)
    (α : Form 𝓘(ℝ,E) P p) : degreeCastForm h (t • α) = t • degreeCastForm h α := by
  subst q
  rfl

private theorem originalCast_neg {p q : ℕ} (h : p=q)
    (α : Form 𝓘(ℝ,E) P p) : degreeCastForm h (-α) = -degreeCastForm h α := by
  subst q
  rfl

private theorem originalCast_congr_at {p q : ℕ} (h : p=q)
    (α β : Form 𝓘(ℝ,E) P p) (x : P) (hα : α x = β x) :
    degreeCastForm h α x = degreeCastForm h β x := by
  ext v
  simp only [degreeCastForm_apply_intrinsic]
  rw [hα]

/-- Actual pointwise unit/orthogonality contracts the complete leading
curvature contribution, without differentiating a frozen unit vector. -/
theorem directionLeadingExpression_alternation_of_unit (r k : ℕ)
    (b : Basis (Fin (1+((r+1)+2*k))) ℝ W)
    (U : W →ₗ[ℝ] P → ℝ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (u : P → W) (hB : ∀ v z, B v z = -B z v)
    (hu : ∀ x, U (u x) x = 1) (hΘ : ∀ x, Θ (u x) x = 0) :
    signedFrameSum
      (directionLeadingExpression r k U Θ (fun v x ↦ B v (u x) x)
        (fun v z : W ↦ B v z)) b =
      -(2*((k+1 : ℕ) : ℝ))⁻¹ •
        degreeCastForm (show r+2*(k+1)=(r+1)+1+2*k by omega)
          ((mixedMultilinear r (k+1) Θ B).alternatization
            (b ∘ finCongr (show r+2*(k+1)=1+((r+1)+2*k) by omega))) := by
  funext x
  let Ux : W →ₗ[ℝ] ℝ := (LinearMap.proj x).comp U
  let e : Fin (r+2*(k+1)) ≃ Fin (1+((r+1)+2*k)) := finCongr (by omega)
  let b' : Basis (Fin (r+2*(k+1))) ℝ W := b.reindex e.symm
  have hb' : (b' : Fin (r+2*(k+1)) → W) = b ∘ e := by
    simp only [b', Basis.coe_reindex, Equiv.symm_symm]
  have hpoint (w : Fin (1+((r+1)+2*k)) → W) :
      directionLeadingExpression r k U Θ (fun v y ↦ B v (u y) y)
        (fun v z : W ↦ B v z) w x =
      directionLeadingExpression r k (fun (v : W) (_ : P) ↦ Ux v) Θ
        (fun v ↦ B v (u x)) (fun v z : W ↦ B v z) w x := by
    exact directionLeadingExpression_congr_at r k U (fun (v : W) (_ : P) ↦ Ux v)
      Θ (fun v y ↦ B v (u y) y) (fun v ↦ B v (u x))
      (fun v z : W ↦ B v z) w x (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hsum :
      signedFrameSum (directionLeadingExpression r k U Θ (fun v y ↦ B v (u y) y)
        (fun v z : W ↦ B v z)) b x =
      signedFrameSum (directionLeadingExpression r k (fun (v : W) (_ : P) ↦ Ux v) Θ
        (fun v ↦ B v (u x)) (fun v z : W ↦ B v z)) b x := by
    simp only [signedFrameSum, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro σ _
    exact congrArg (fun α ↦ permutationSignReal σ • α) (hpoint (b ∘ σ))
  have hinv := mixed_curvature_contraction_inverse r (k+1) (by omega) Θ B hB b' Ux (u x) x
    (hu x) (hΘ x)
  rw [hb'] at hinv
  let C : Form 𝓘(ℝ,E) P (r+2*(k+1)) :=
    (slotInsertion (mixedMultilinear r (k+1) Θ B) (Ux.smulRight (u x))
      (Fin.natAdd r (pairFirst (0 : Fin (k+1))))).alternatization (b ∘ e)
  let Y : Form 𝓘(ℝ,E) P (r+2*(k+1)) :=
    (mixedMultilinear r (k+1) Θ B).alternatization (b ∘ e)
  have hc : C x = ((2*((k+1 : ℕ) : ℝ))⁻¹ • Y) x := hinv
  have hcast := originalCast_congr_at (show r+2*(k+1)=(r+1)+1+2*k by omega)
    C ((2*((k+1 : ℕ) : ℝ))⁻¹ • Y) x hc
  rw [hsum, directionLeadingExpression_alternation_eq_neg_insertion r k Ux (u x) Θ B hB]
  change -degreeCastForm (show r+2*(k+1)=(r+1)+1+2*k by omega) C x = _
  rw [hcast, originalCast_smul]
  change -((2*((k+1 : ℕ) : ℝ))⁻¹ • degreeCastForm _ Y x) =
    -(2*((k+1 : ℕ) : ℝ))⁻¹ • degreeCastForm _ Y x
  ext v
  simp only [ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  ring

/-- The complete genuine derivative recurrence on the actual raw angular
multilinear polynomial, for every dimension and curvature count. -/
theorem exteriorDerivative_weightedFrameMultilinear_recurrence (r k : ℕ)
    (b : Basis (Fin (1+((r+1)+2*k))) ℝ W)
    (Γ : Fin (1+((r+1)+2*k)) → W → Form 𝓘(ℝ,E) P 1)
    (U : W →ₗ[ℝ] P → ℝ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) (u : P → W)
    (hΓ : ∀ i j, Γ i (b j) = -Γ j (b i))
    (hBskew : ∀ v z, B v z = -B z v)
    (hU : ∀ v, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (U v))
    (hΘ : ∀ v, IsSmooth (Θ v)) (hB : ∀ v z, IsSmooth (B v z))
    (hScalar : ∀ v, exteriorDerivative (ofFunction (U v)) =
      Θ v + ∑ j, functionSmulLinear 1 (U (b j)) (Γ j v))
    (hCartan : ∀ v, exteriorDerivative (Θ v) =
      (fun x ↦ B v (u x) x) + ∑ j, wedge (Γ j v) (Θ (b j)))
    (hBianchi : ∀ v z, exteriorDerivative (B v z) =
      (∑ j, wedge (Γ j v) (B (b j) z)) + ∑ j, wedge (Γ j z) (B v (b j)))
    (hu : ∀ x, U (u x) x = 1) (horth : ∀ x, Θ (u x) x = 0) :
    exteriorDerivative ((weightedFrameMultilinear (r+1) k U Θ B).alternatization b) =
      signedFrameSum (scalarLeadingExpression (r+1) k Θ (fun v z : W ↦ B v z)) b -
      (((r+1 : ℕ) : ℝ)/(2*((k+1 : ℕ) : ℝ))) •
        degreeCastForm (show r+2*(k+1)=(r+1)+2*k+1 by omega)
          ((mixedMultilinear r (k+1) Θ B).alternatization
            (b ∘ finCongr (show r+2*(k+1)=1+((r+1)+2*k) by omega))) := by
  rw [exteriorDerivative_weightedFrameMultilinear_compressed r k b Γ U Θ
    (fun v x ↦ B v (u x) x) B hΓ hU hΘ hB hScalar hCartan hBianchi,
    directionLeadingExpression_alternation_of_unit r k b U Θ B u hBskew hu horth,
    originalCast_smul, originalCast_smul, degreeCastForm_trans, smul_smul]
  simp only [div_eq_mul_inv, mul_neg, _root_.neg_smul, sub_eq_add_neg]
  funext x
  ext v
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

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

private theorem originalCast_sub {p q : ℕ} (h : p=q)
    (α β : Form 𝓘(ℝ,E) P p) :
    degreeCastForm h (α-β) = degreeCastForm h α - degreeCastForm h β := by
  subst q
  rfl

/-- Full alternation of the true scalar contribution is exactly the next
mixed polynomial, including its canonical arity and output-degree transport. -/
theorem scalarLeadingExpression_alternation_eq_mixed (t k : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (w : Fin (1+(t+2*k)) → W) :
    degreeCastForm (show t+2*k+1=(t+1)+2*k by omega)
      (signedFrameSum (scalarLeadingExpression t k Θ (fun v z : W ↦ B v z)) w) =
      (mixedMultilinear (t+1) k Θ B).alternatization
        (w ∘ finCongr (show (t+1)+2*k=1+(t+2*k) by omega)) := by
  let L := formCastLinear (E := E) (P := P)
    (show t+2*k+1=(t+1)+2*k by omega)
  let e := finCongr (show (t+1)+2*k=1+(t+2*k) by omega)
  have hF : (fun z ↦ L (scalarLeadingExpression t k Θ (fun v z : W ↦ B v z) z)) =
      (mixedMultilinear (t+1) k Θ B).domDomCongr e := by
    funext z
    simpa only [L, e, formCastLinear_apply, MultilinearMap.domDomCongr_apply,
      Function.comp_def] using scalarLeadingExpression_eq_mixed t k Θ B z
  rw [← formCastLinear_apply (show t+2*k+1=(t+1)+2*k by omega)]
  change L (signedFrameSum (scalarLeadingExpression t k Θ (fun v z : W ↦ B v z)) w) = _
  rw [← signedFrameSum_linear, hF, signedFrameSum_multilinear]
  simp only [e, alternatization_domFinCast]

/-- The raw angular polynomial is precisely the original angularTerm; no
replacement definition of Φ is introduced. -/
theorem angularTerm_eq_weightedFrame_alternatization (n : ℕ) (k : Fin n)
    (r : ℕ) (hr : r+1=2*n-2*k.val-1)
    (U : W →ₗ[ℝ] P → ℝ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) (w : Fin (2*n) → W) :
    degreeCastForm (show (r+1)+2*k.val=2*n-1 by have := k.isLt; omega)
      ((weightedFrameMultilinear (r+1) k.val U Θ B).alternatization
        (w ∘ finCongr (show 1+((r+1)+2*k.val)=2*n by have := k.isLt; omega))) =
      angularTerm n k (fun i ↦ U (w i)) (fun i ↦ Θ (w i)) (fun i j ↦ B (w i) (w j)) := by
  have hgeneral (t : ℕ) (ht : t=2*n-2*k.val-1) :
      degreeCastForm (show t+2*k.val=2*n-1 by have := k.isLt; omega)
        ((weightedFrameMultilinear t k.val U Θ B).alternatization
          (w ∘ finCongr (show 1+(t+2*k.val)=2*n by have := k.isLt; omega))) =
        angularTerm n k (fun i ↦ U (w i)) (fun i ↦ Θ (w i))
          (fun i j ↦ B (w i) (w j)) := by
    subst t
    rw [← angularMultilinear_alternatization, angularMultilinear,
      LinearMap.compMultilinearMap_alternatization, LinearMap.compAlternatingMap_apply,
      formCastLinear_apply, alternatization_domFinCast]
    rfl
  exact hgeneral (r+1) hr

/-- Exact original all-dimensional Chern recurrence for the actual exterior
 derivative, under the actual primitive Cartan/Bianchi and unit identities. -/
theorem exteriorDerivative_angularTerm_recurrence (n : ℕ) (k : Fin n)
    (b : Basis (Fin (2*n)) ℝ W)
    (Γ : Fin (2*n) → W → Form 𝓘(ℝ,E) P 1)
    (U : W →ₗ[ℝ] P → ℝ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) (u : P → W)
    (hΓ : ∀ i j, Γ i (b j) = -Γ j (b i))
    (hBskew : ∀ v z, B v z = -B z v)
    (hU : ∀ v, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (U v))
    (hΘ : ∀ v, IsSmooth (Θ v)) (hB : ∀ v z, IsSmooth (B v z))
    (hScalar : ∀ v, exteriorDerivative (ofFunction (U v)) =
      Θ v + ∑ j, functionSmulLinear 1 (U (b j)) (Γ j v))
    (hCartan : ∀ v, exteriorDerivative (Θ v) =
      (fun x ↦ B v (u x) x) + ∑ j, wedge (Γ j v) (Θ (b j)))
    (hBianchi : ∀ v z, exteriorDerivative (B v z) =
      (∑ j, wedge (Γ j v) (B (b j) z)) + ∑ j, wedge (Γ j z) (B v (b j)))
    (hu : ∀ x, U (u x) x = 1) (horth : ∀ x, Θ (u x) x = 0) :
    degreeCastForm (show (2*n-1)+1=2*n by have := k.isLt; omega)
      (exteriorDerivative (angularTerm n k (fun i ↦ U (b i))
        (fun i ↦ Θ (b i)) (fun i j ↦ B (b i) (b j)))) =
      recurrencePolynomial n k.castSucc (fun i ↦ Θ (b i)) (fun i j ↦ B (b i) (b j)) -
      recurrenceCoefficient n k.val •
        recurrencePolynomial n k.succ (fun i ↦ Θ (b i)) (fun i j ↦ B (b i) (b j)) := by
  let r := 2*n-2*k.val-2
  have hr : r+1=2*n-2*k.val-1 := by dsimp only [r]; have := k.isLt; omega
  have hd : 1+((r+1)+2*k.val)=2*n := by have := k.isLt; omega
  have hp : (r+1)+2*k.val=2*n-1 := by have := k.isLt; omega
  have htop : (r+1)+2*k.val+1=2*n := by have := k.isLt; omega
  have hdir : (r+1)+1=2*n-2*k.val := by have := k.isLt; omega
  have hcurv : r=2*n-2*(k.val+1) := by dsimp only [r]; have := k.isLt; omega
  let e : Fin (1+((r+1)+2*k.val)) ≃ Fin (2*n) := finCongr hd
  let b' : Basis (Fin (1+((r+1)+2*k.val))) ℝ W := b.reindex e.symm
  let Γ' : Fin (1+((r+1)+2*k.val)) → W → Form 𝓘(ℝ,E) P 1 := fun j ↦ Γ (e j)
  have hb' : (b' : Fin (1+((r+1)+2*k.val)) → W) = b ∘ e := by
    simp only [b', Basis.coe_reindex, Equiv.symm_symm]
  have hΓ' : ∀ i j, Γ' i (b' j) = -Γ' j (b' i) := by
    intro i j
    simpa only [Γ', hb', Function.comp_apply] using hΓ (e i) (e j)
  have hScalar' : ∀ v, exteriorDerivative (ofFunction (U v)) =
      Θ v + ∑ j, functionSmulLinear 1 (U (b' j)) (Γ' j v) := by
    intro v
    rw [hScalar]
    apply congrArg (fun α ↦ Θ v + α)
    simpa only [Γ', hb', Function.comp_apply] using
      (Equiv.sum_comp e (fun j ↦ functionSmulLinear 1 (U (b j)) (Γ j v))).symm
  have hCartan' : ∀ v, exteriorDerivative (Θ v) =
      (fun x ↦ B v (u x) x) + ∑ j, wedge (Γ' j v) (Θ (b' j)) := by
    intro v
    rw [hCartan]
    apply congrArg (fun α ↦ (fun x ↦ B v (u x) x) + α)
    simpa only [Γ', hb', Function.comp_apply] using
      (Equiv.sum_comp e (fun j ↦ wedge (Γ j v) (Θ (b j)))).symm
  have hBianchi' : ∀ v z, exteriorDerivative (B v z) =
      (∑ j, wedge (Γ' j v) (B (b' j) z)) + ∑ j, wedge (Γ' j z) (B v (b' j)) := by
    intro v z
    rw [hBianchi]
    apply congrArg₂ (· + ·)
    · simpa only [Γ', hb', Function.comp_apply] using
        (Equiv.sum_comp e (fun j ↦ wedge (Γ j v) (B (b j) z))).symm
    · simpa only [Γ', hb', Function.comp_apply] using
        (Equiv.sum_comp e (fun j ↦ wedge (Γ j z) (B v (b j)))).symm
  have hraw := exteriorDerivative_weightedFrameMultilinear_recurrence r k.val b' Γ'
    U Θ B u hΓ' hBskew hU hΘ hB hScalar' hCartan' hBianchi' hu horth
  rw [hb'] at hraw
  have hang := angularTerm_eq_weightedFrame_alternatization n k r hr U Θ B b
  rw [← hang, exteriorDerivative_degreeCast, degreeCastForm_trans]
  have htransport := congrArg (degreeCastForm htop) hraw
  simp only [originalCast_sub, originalCast_smul, degreeCastForm_trans] at htransport
  have hscalar := congrArg
    (degreeCastForm (show ((r+1)+1)+2*k.val=2*n by have := k.isLt; omega))
    (scalarLeadingExpression_alternation_eq_mixed (r+1) k.val Θ B (b ∘ e))
  simp only [degreeCastForm_trans] at hscalar
  have hscalarTuple : (b ∘ e) ∘
      finCongr (show ((r+1)+1)+2*k.val=1+((r+1)+2*k.val) by omega) =
      b ∘ finCongr (show ((r+1)+1)+2*k.val=2*n by have := k.isLt; omega) := by
    funext i
    apply congrArg b
    apply Fin.ext
    rfl
  rw [hscalarTuple] at hscalar
  have hy0 := (recurrenceFrameMultilinear_alternatization_eq_cast n k.castSucc Θ B b).symm
  rw [recurrenceFrameMultilinear_alternatization] at hy0
  have hy0' : degreeCastForm (show ((r+1)+1)+2*k.val=2*n by have := k.isLt; omega)
      ((mixedMultilinear ((r+1)+1) k.val Θ B).alternatization
        (b ∘ finCongr (show ((r+1)+1)+2*k.val=2*n by have := k.isLt; omega))) =
      recurrencePolynomial n k.castSucc (fun i ↦ Θ (b i)) (fun i j ↦ B (b i) (b j)) := by
    have hgeneral (t : ℕ) (ht : t=2*n-2*k.val) :
        degreeCastForm (show t+2*k.val=2*n by have := k.isLt; omega)
          ((mixedMultilinear t k.val Θ B).alternatization
            (b ∘ finCongr (show t+2*k.val=2*n by have := k.isLt; omega))) =
          recurrencePolynomial n k.castSucc (fun i ↦ Θ (b i))
            (fun i j ↦ B (b i) (b j)) := by
      subst t
      simpa only [Fin.val_castSucc] using hy0
    exact hgeneral ((r+1)+1) hdir
  have hcurvTuple : (b ∘ e) ∘
      finCongr (show r+2*(k.val+1)=1+((r+1)+2*k.val) by omega) =
      b ∘ finCongr (show r+2*(k.val+1)=2*n by have := k.isLt; omega) := by
    funext i
    apply congrArg b
    apply Fin.ext
    rfl
  rw [hcurvTuple] at htransport
  have hy1 := (recurrenceFrameMultilinear_alternatization_eq_cast n k.succ Θ B b).symm
  rw [recurrenceFrameMultilinear_alternatization] at hy1
  have hy1' : degreeCastForm (show r+2*(k.val+1)=2*n by have := k.isLt; omega)
      ((mixedMultilinear r (k.val+1) Θ B).alternatization
        (b ∘ finCongr (show r+2*(k.val+1)=2*n by have := k.isLt; omega))) =
      recurrencePolynomial n k.succ (fun i ↦ Θ (b i)) (fun i j ↦ B (b i) (b j)) := by
    have hgeneral (t : ℕ) (ht : t=2*n-2*(k.val+1)) :
        degreeCastForm (show t+2*(k.val+1)=2*n by have := k.isLt; omega)
          ((mixedMultilinear t (k.val+1) Θ B).alternatization
            (b ∘ finCongr (show t+2*(k.val+1)=2*n by have := k.isLt; omega))) =
          recurrencePolynomial n k.succ (fun i ↦ Θ (b i))
            (fun i j ↦ B (b i) (b j)) := by
      subst t
      simpa only [Fin.val_succ] using hy1
    exact hgeneral r hcurv
  have hnum : ((r+1 : ℕ) : ℝ) = 2*(n:ℝ)-2*k.val-1 := by
    rw [hr, Nat.cast_sub (by have := k.isLt; omega), Nat.cast_sub (by have := k.isLt; omega)]
    push_cast
    ring
  have hcoef : ((r+1 : ℕ) : ℝ)/(2*((k.val+1 : ℕ) : ℝ)) = recurrenceCoefficient n k.val := by
    simp only [recurrenceCoefficient, hnum, Nat.cast_add, Nat.cast_one]
  rw [hscalar, hy0', hy1', hcoef] at htransport
  exact htransport

end GaussBonnetChern.Chern
