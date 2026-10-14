import GaussBonnetChern.ChernProductDifferential

/-! # Linearity and order of the genuine Chern derivative replacement terms

Each replacement term depends linearly on exactly its selected derivative
factor. The differentiated factor can be moved to the front without a sign:
its degree is two among one-forms, or three among two-forms. All constructions
use the project's actual normalized wedge product and explicit degree transport.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

/-- The selected differentiated one-form slot is a genuine linear input. -/
def oneFormProductReplacementLinear : (r : ℕ) →
    (Fin r → Form 𝓘(ℝ, E) P 1) → Fin r →
    (Form 𝓘(ℝ, E) P 2 →ₗ[ℝ] Form 𝓘(ℝ, E) P (r+1))
  | 0, _, i => Fin.elim0 i
  | r+1, θ, i => Fin.lastCases
      (wedgeLinear r 2 (oneFormProduct r (fun j ↦ θ j.castSucc)))
      (fun j ↦ ((wedgeLinear (r+1) 1).flip (θ (Fin.last r))).comp
        (oneFormProductReplacementLinear r (fun j ↦ θ j.castSucc) j)) i

theorem oneFormProductReplacement_eq_linear (r : ℕ)
    (θ : Fin r → Form 𝓘(ℝ, E) P 1) (δ : Fin r → Form 𝓘(ℝ, E) P 2) (i : Fin r) :
    oneFormProductReplacement r θ δ i = oneFormProductReplacementLinear r θ i (δ i) := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [oneFormProductReplacement, oneFormProductReplacementLinear]
    · simp only [oneFormProductReplacement_castSucc, oneFormProductReplacementLinear,
        Fin.lastCases_castSucc, LinearMap.comp_apply, LinearMap.flip_apply, wedgeLinear_apply]
      rw [ih]

theorem oneFormProductReplacement_add (r : ℕ)
    (θ : Fin r → Form 𝓘(ℝ, E) P 1)
    (δ ε : Fin r → Form 𝓘(ℝ, E) P 2) (i : Fin r) :
    oneFormProductReplacement r θ (δ+ε) i =
      oneFormProductReplacement r θ δ i + oneFormProductReplacement r θ ε i := by
  simp only [oneFormProductReplacement_eq_linear, Pi.add_apply, map_add]

theorem oneFormProductReplacement_congr (r : ℕ)
    (θ : Fin r → Form 𝓘(ℝ, E) P 1)
    (δ ε : Fin r → Form 𝓘(ℝ, E) P 2) (i : Fin r) (h : δ i = ε i) :
    oneFormProductReplacement r θ δ i = oneFormProductReplacement r θ ε i := by
  simp only [oneFormProductReplacement_eq_linear, h]

theorem oneFormProductReplacement_smul (r : ℕ)
    (θ : Fin r → Form 𝓘(ℝ, E) P 1)
    (δ : Fin r → Form 𝓘(ℝ, E) P 2) (i : Fin r) (c : ℝ) :
    oneFormProductReplacement r θ (c • δ) i = c • oneFormProductReplacement r θ δ i := by
  simp only [oneFormProductReplacement_eq_linear, Pi.smul_apply, map_smul]

def twoFormProductReplacementLinear : (r : ℕ) →
    (Fin r → Form 𝓘(ℝ, E) P 2) → Fin r →
    (Form 𝓘(ℝ, E) P 3 →ₗ[ℝ] Form 𝓘(ℝ, E) P (2*r+1))
  | 0, _, i => Fin.elim0 i
  | r+1, B, i => (formCastLinear (show 2*r+3 = 2*(r+1)+1 by omega)).comp
      (Fin.lastCases
        (wedgeLinear (2*r) 3 (twoFormProduct r (fun j ↦ B j.castSucc)))
        (fun j ↦ ((wedgeLinear (2*r+1) 2).flip (B (Fin.last r))).comp
          (twoFormProductReplacementLinear r (fun j ↦ B j.castSucc) j)) i)

variable [IsManifold 𝓘(ℝ, E) ∞ P]

theorem twoFormProductReplacement_eq_linear (r : ℕ)
    (B : Fin r → Form 𝓘(ℝ, E) P 2) (δ : Fin r → Form 𝓘(ℝ, E) P 3) (i : Fin r) :
    twoFormProductReplacement r B δ i = twoFormProductReplacementLinear r B i (δ i) := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [twoFormProductReplacement, twoFormProductReplacementLinear]
    · simp only [twoFormProductReplacement_castSucc, twoFormProductReplacementLinear,
        Fin.lastCases_castSucc, LinearMap.comp_apply, LinearMap.flip_apply,
        wedgeLinear_apply, formCastLinear_apply]
      rw [ih]

theorem twoFormProductReplacement_add (r : ℕ)
    (B : Fin r → Form 𝓘(ℝ, E) P 2)
    (δ ε : Fin r → Form 𝓘(ℝ, E) P 3) (i : Fin r) :
    twoFormProductReplacement r B (δ+ε) i =
      twoFormProductReplacement r B δ i + twoFormProductReplacement r B ε i := by
  simp only [twoFormProductReplacement_eq_linear, Pi.add_apply, map_add]

theorem twoFormProductReplacement_congr (r : ℕ)
    (B : Fin r → Form 𝓘(ℝ, E) P 2)
    (δ ε : Fin r → Form 𝓘(ℝ, E) P 3) (i : Fin r) (h : δ i = ε i) :
    twoFormProductReplacement r B δ i = twoFormProductReplacement r B ε i := by
  simp only [twoFormProductReplacement_eq_linear, h]

theorem twoFormProductReplacement_smul (r : ℕ)
    (B : Fin r → Form 𝓘(ℝ, E) P 2)
    (δ : Fin r → Form 𝓘(ℝ, E) P 3) (i : Fin r) (c : ℝ) :
    twoFormProductReplacement r B (c • δ) i = c • twoFormProductReplacement r B δ i := by
  simp only [twoFormProductReplacement_eq_linear, Pi.smul_apply, map_smul]

end GaussBonnetChern.Chern


noncomputable section
open scoped Manifold ContDiff BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

private theorem gradedForm_commute_of_even {r s : ℕ}
    (α : Form 𝓘(ℝ, E) P r) (β : Form 𝓘(ℝ, E) P s)
    (h : Even (r*s)) : Commute (⟨r, α⟩ : GradedForm) ⟨s, β⟩ := by
  change (⟨r, α⟩ : GradedForm) * (⟨s, β⟩ : GradedForm) =
    (⟨s, β⟩ : GradedForm) * (⟨r, α⟩ : GradedForm)
  apply GradedForm.eq_of_degreeCast (Nat.add_comm r s)
  funext x
  ext v
  simp only [degreeCastForm_apply_intrinsic]
  have hw := wedgeFiber_graded_comm (α x) (β x)
    (v ∘ finCongr (Nat.add_comm r s))
  have hv : (fun i ↦ (v ∘ finCongr (Nat.add_comm r s))
      (finCongr (Nat.add_comm s r) i)) = v := by
    funext i
    apply congrArg v
    apply Fin.ext
    rfl
  rw [hv, h.neg_one_pow, one_mul] at hw
  exact hw.symm

private theorem graded_oneReplacement_front (r : ℕ)
    (θ : Fin (r+1) → Form 𝓘(ℝ, E) P 1)
    (δ : Fin (r+1) → Form 𝓘(ℝ, E) P 2) (i : Fin (r+1)) :
    (⟨r+1+1, oneFormProductReplacement (r+1) θ δ i⟩ : GradedForm) =
      (⟨2, δ i⟩ : GradedForm) * ⟨r, oneFormProduct r (θ ∘ i.succAbove)⟩ := by
  induction r with
  | zero =>
    have hi : i = Fin.last 0 := by
      apply Fin.ext
      have := i.isLt
      simp only [Fin.val_last]
      omega
    subst i
    rw [oneFormProductReplacement_last]
    change (1 : GradedForm) * ⟨2, δ (Fin.last 0)⟩ = ⟨2, δ (Fin.last 0)⟩ * 1
    simp
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [oneFormProductReplacement_last]
      simp only [Fin.succAbove_last, Function.comp_def]
      change (⟨r+1, oneFormProduct (r+1) (fun j ↦ θ j.castSucc)⟩ : GradedForm) *
        ⟨2, δ (Fin.last (r+1))⟩ =
          (⟨2, δ (Fin.last (r+1))⟩ : GradedForm) *
            ⟨r+1, oneFormProduct (r+1) (fun j ↦ θ j.castSucc)⟩
      exact (gradedForm_commute_of_even _ _ (by exact even_two.mul_left _)).eq
    · rw [oneFormProductReplacement_castSucc]
      change (⟨r+1+1, oneFormProductReplacement (r+1)
        (fun j ↦ θ j.castSucc) (fun j ↦ δ j.castSucc) j⟩ : GradedForm) *
          ⟨1, θ (Fin.last (r+1))⟩ = _
      rw [ih, mul_assoc]
      congr 1
      change (⟨r+1, wedge (oneFormProduct r
        (fun k ↦ θ (j.succAbove k).castSucc)) (θ (Fin.last (r+1)))⟩ : GradedForm) = _
      apply congrArg (fun α ↦ (⟨r+1, α⟩ : GradedForm))
      conv_rhs => rw [oneFormProduct]
      simp only [Function.comp_def, Fin.castSucc_succAbove_castSucc,
        Fin.succAbove_ne_last_last (Fin.castSucc_ne_last j)]

/-- Move the selected two-form derivative to the front of a one-form product.
The move has positive sign because it crosses factors of degree one with degree two. -/
theorem oneFormProductReplacement_front (r : ℕ)
    (θ : Fin (r+1) → Form 𝓘(ℝ, E) P 1)
    (δ : Fin (r+1) → Form 𝓘(ℝ, E) P 2) (i : Fin (r+1)) :
    oneFormProductReplacement (r+1) θ δ i =
      degreeCastForm (show 2+r = (r+1)+1 by omega)
        (wedge (δ i) (oneFormProduct r (θ ∘ i.succAbove))) := by
  have hp := graded_oneReplacement_front r θ δ i
  have hc := GradedForm.eq_of_degreeCast
    (a := (⟨2, δ i⟩ : GradedForm) * ⟨r, oneFormProduct r (θ ∘ i.succAbove)⟩)
    (b := (⟨r+1+1, degreeCastForm (show 2+r = (r+1)+1 by omega)
      (wedge (δ i) (oneFormProduct r (θ ∘ i.succAbove)))⟩ : GradedForm))
    (show 2+r = (r+1)+1 by omega) rfl
  exact GradedForm.mk_injective (hp.trans hc)

private theorem gradedForm_degreeCast {r s : ℕ} (h : r = s)
    (α : Form 𝓘(ℝ, E) P r) :
    (⟨s, degreeCastForm h α⟩ : GradedForm) = ⟨r, α⟩ := by
  subst s
  rfl

variable [IsManifold 𝓘(ℝ, E) ∞ P]

private theorem graded_twoReplacement_front (r : ℕ)
    (B : Fin (r+1) → Form 𝓘(ℝ, E) P 2)
    (δ : Fin (r+1) → Form 𝓘(ℝ, E) P 3) (i : Fin (r+1)) :
    (⟨2*(r+1)+1, twoFormProductReplacement (r+1) B δ i⟩ : GradedForm) =
      (⟨3, δ i⟩ : GradedForm) * ⟨2*r, twoFormProduct r (B ∘ i.succAbove)⟩ := by
  induction r with
  | zero =>
    have hi : i = Fin.last 0 := by
      apply Fin.ext
      have := i.isLt
      simp only [Fin.val_last]
      omega
    subst i
    rw [twoFormProductReplacement_last, gradedForm_degreeCast]
    change (1 : GradedForm) * ⟨3, δ (Fin.last 0)⟩ = ⟨3, δ (Fin.last 0)⟩ * 1
    simp
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [twoFormProductReplacement_last, gradedForm_degreeCast]
      simp only [Fin.succAbove_last, Function.comp_def]
      change (⟨2*(r+1), twoFormProduct (r+1) (fun j ↦ B j.castSucc)⟩ : GradedForm) *
        ⟨3, δ (Fin.last (r+1))⟩ =
          (⟨3, δ (Fin.last (r+1))⟩ : GradedForm) *
            ⟨2*(r+1), twoFormProduct (r+1) (fun j ↦ B j.castSucc)⟩
      exact (gradedForm_commute_of_even _ _ ((even_two.mul_right (r+1)).mul_right 3)).eq
    · rw [twoFormProductReplacement_castSucc, gradedForm_degreeCast]
      change (⟨2*(r+1)+1, twoFormProductReplacement (r+1)
        (fun j ↦ B j.castSucc) (fun j ↦ δ j.castSucc) j⟩ : GradedForm) *
          ⟨2, B (Fin.last (r+1))⟩ = _
      rw [ih, mul_assoc]
      congr 1
      conv_rhs => rw [twoFormProduct, gradedForm_degreeCast]
      change (⟨2*r+2, wedge (twoFormProduct r
        (fun k ↦ B (j.succAbove k).castSucc)) (B (Fin.last (r+1)))⟩ : GradedForm) = _
      apply congrArg (fun α ↦ (⟨2*r+2, α⟩ : GradedForm))
      simp only [Function.comp_def, Fin.castSucc_succAbove_castSucc,
        Fin.succAbove_ne_last_last (Fin.castSucc_ne_last j)]

/-- Moving the selected three-form derivative across two-form factors has
positive sign and preserves the original order of the remaining factors. -/
theorem twoFormProductReplacement_front (r : ℕ)
    (B : Fin (r+1) → Form 𝓘(ℝ, E) P 2)
    (δ : Fin (r+1) → Form 𝓘(ℝ, E) P 3) (i : Fin (r+1)) :
    twoFormProductReplacement (r+1) B δ i =
      degreeCastForm (show 3+2*r = 2*(r+1)+1 by omega)
        (wedge (δ i) (twoFormProduct r (B ∘ i.succAbove))) := by
  have hp := graded_twoReplacement_front r B δ i
  have hc := GradedForm.eq_of_degreeCast
    (a := (⟨3, δ i⟩ : GradedForm) * ⟨2*r, twoFormProduct r (B ∘ i.succAbove)⟩)
    (b := (⟨2*(r+1)+1, degreeCastForm (show 3+2*r = 2*(r+1)+1 by omega)
      (wedge (δ i) (twoFormProduct r (B ∘ i.succAbove)))⟩ : GradedForm))
    (show 3+2*r = 2*(r+1)+1 by omega) rfl
  exact GradedForm.mk_injective (hp.trans hc)

end GaussBonnetChern.Chern
