import GaussBonnetChern.ChernAngularAlgebra
import GaussBonnetChern.ExteriorSmoothLinear
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.List.FinRange

/-! # Identities for the actual ordered Chern products

The products remain the existing iterated normalized wedge products. Their
factor linearity and permutation identities are proved from that multiplication.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators

namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

/-- The actual one-form product, multilinear in its independent form factors. -/
def oneFormFactorsMultilinear (r : ℕ) :
    MultilinearMap ℝ (fun _ : Fin r ↦ Form 𝓘(ℝ, E) P 1) (Form 𝓘(ℝ, E) P r) :=
  oneFormProductMultilinear (LinearMap.id : Form 𝓘(ℝ, E) P 1 →ₗ[ℝ] Form 𝓘(ℝ, E) P 1) r

@[simp] theorem oneFormFactorsMultilinear_apply (r : ℕ)
    (θ : Fin r → Form 𝓘(ℝ, E) P 1) :
    oneFormFactorsMultilinear r θ = oneFormProduct r θ := by
  exact oneFormProductMultilinear_apply LinearMap.id r θ

/-- Independent two-form factor slots, distinct from the two frame-vector
slots used to define each curvature two-form. -/
def twoFormFactorsMultilinear : (r : ℕ) →
    MultilinearMap ℝ (fun _ : Fin r ↦ Form 𝓘(ℝ, E) P 2) (Form 𝓘(ℝ, E) P (2*r))
  | 0 => MultilinearMap.constOfIsEmpty ℝ _ (ofFunction (fun _ ↦ 1))
  | r+1 => (formCastLinear (show 2*r+2 = 2*(r+1) by omega)).compMultilinearMap
      (multilinearBlock (wedgeLinear (2*r) 2) (twoFormFactorsMultilinear r)
        (MultilinearMap.ofSubsingleton ℝ (Form 𝓘(ℝ, E) P 2) _ (0 : Fin 1) LinearMap.id))

@[simp] theorem twoFormFactorsMultilinear_apply (r : ℕ)
    (B : Fin r → Form 𝓘(ℝ, E) P 2) :
    twoFormFactorsMultilinear r B = twoFormProduct r B := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [twoFormFactorsMultilinear, LinearMap.compMultilinearMap_apply,
      multilinearBlock_apply, MultilinearMap.ofSubsingleton, wedgeLinear_apply,
      formCastLinear_apply, twoFormProduct, ih, LinearMap.id_apply]
    congr 2

theorem oneFormProduct_update_add (r : ℕ) (θ : Fin r → Form 𝓘(ℝ, E) P 1)
    (i : Fin r) (α β : Form 𝓘(ℝ, E) P 1) :
    oneFormProduct r (Function.update θ i (α + β)) =
      oneFormProduct r (Function.update θ i α) + oneFormProduct r (Function.update θ i β) := by
  simpa only [oneFormFactorsMultilinear_apply] using
    (oneFormFactorsMultilinear (E := E) (P := P) r).map_update_add θ i α β

theorem oneFormProduct_update_smul (r : ℕ) (θ : Fin r → Form 𝓘(ℝ, E) P 1)
    (i : Fin r) (c : ℝ) (α : Form 𝓘(ℝ, E) P 1) :
    oneFormProduct r (Function.update θ i (c • α)) =
      c • oneFormProduct r (Function.update θ i α) := by
  simpa only [oneFormFactorsMultilinear_apply] using
    (oneFormFactorsMultilinear (E := E) (P := P) r).map_update_smul θ i c α

theorem oneFormProduct_update_self_smul (r : ℕ) (θ : Fin r → Form 𝓘(ℝ, E) P 1)
    (i : Fin r) (c : ℝ) :
    oneFormProduct r (Function.update θ i (c • θ i)) = c • oneFormProduct r θ := by
  rw [oneFormProduct_update_smul, Function.update_eq_self]

theorem twoFormProduct_update_add (r : ℕ) (B : Fin r → Form 𝓘(ℝ, E) P 2)
    (i : Fin r) (α β : Form 𝓘(ℝ, E) P 2) :
    twoFormProduct r (Function.update B i (α + β)) =
      twoFormProduct r (Function.update B i α) + twoFormProduct r (Function.update B i β) := by
  simpa only [twoFormFactorsMultilinear_apply] using
    (twoFormFactorsMultilinear (E := E) (P := P) r).map_update_add B i α β

theorem twoFormProduct_update_smul (r : ℕ) (B : Fin r → Form 𝓘(ℝ, E) P 2)
    (i : Fin r) (c : ℝ) (α : Form 𝓘(ℝ, E) P 2) :
    twoFormProduct r (Function.update B i (c • α)) =
      c • twoFormProduct r (Function.update B i α) := by
  simpa only [twoFormFactorsMultilinear_apply] using
    (twoFormFactorsMultilinear (E := E) (P := P) r).map_update_smul B i c α

theorem twoFormProduct_update_self_smul (r : ℕ) (B : Fin r → Form 𝓘(ℝ, E) P 2)
    (i : Fin r) (c : ℝ) :
    twoFormProduct r (Function.update B i (c • B i)) = c • twoFormProduct r B := by
  rw [twoFormProduct_update_smul, Function.update_eq_self]

section GradedMonoid

/-- An actual homogeneous form together with its degree. -/
structure GradedForm where
  degree : ℕ
  toForm : Form 𝓘(ℝ, E) P degree

namespace GradedForm

theorem eq_of_degreeCast {a b : GradedForm (E := E) (P := P)} (h : a.degree = b.degree)
    (hform : degreeCastForm h a.toForm = b.toForm) : a = b := by
  rcases a with ⟨r, α⟩
  rcases b with ⟨s, β⟩
  dsimp at h
  subst s
  change α = β at hform
  subst β
  rfl

instance : One (GradedForm (E := E) (P := P)) :=
  ⟨⟨0, ofFunction (fun _ ↦ 1)⟩⟩

instance : Mul (GradedForm (E := E) (P := P)) :=
  ⟨fun a b ↦ ⟨a.degree + b.degree, wedge a.toForm b.toForm⟩⟩

instance : Monoid (GradedForm (E := E) (P := P)) where
  one_mul a := by
    apply eq_of_degreeCast (a := 1 * a) (b := a) (Nat.zero_add a.degree)
    exact wedge_one_left a.toForm
  mul_one a := by
    apply eq_of_degreeCast (a := a * 1) (b := a) (Nat.add_zero a.degree)
    exact wedge_one_right a.toForm
  mul_assoc a b c := by
    apply eq_of_degreeCast (a := (a * b) * c) (b := a * (b * c))
      (Nat.add_assoc a.degree b.degree c.degree)
    exact wedge_assoc a.toForm b.toForm c.toForm

theorem mk_injective {r : ℕ} :
    Function.Injective (fun α : Form 𝓘(ℝ, E) P r ↦ (⟨r, α⟩ : GradedForm)) := by
  intro α β h
  exact eq_of_heq (GradedForm.mk.inj h).2

/-- Homogeneous two-forms commute in the actual graded wedge monoid. -/
theorem commute_twoForms (α β : Form 𝓘(ℝ, E) P 2) :
    Commute (⟨2, α⟩ : GradedForm) ⟨2, β⟩ := by
  change (⟨2, α⟩ : GradedForm) * (⟨2, β⟩ : GradedForm) =
    (⟨2, β⟩ : GradedForm) * (⟨2, α⟩ : GradedForm)
  apply eq_of_degreeCast (a := (⟨2, α⟩ : GradedForm) * (⟨2, β⟩ : GradedForm))
    (b := (⟨2, β⟩ : GradedForm) * (⟨2, α⟩ : GradedForm)) rfl
  change wedge α β = wedge β α
  funext x
  ext v
  have h := wedgeFiber_graded_comm (α x) (β x) v
  have hv : (fun i ↦ v (finCongr (Nat.add_comm 2 2) i)) = v := by
    funext i
    apply congrArg v
    apply Fin.ext
    rfl
  rw [hv] at h
  norm_num at h
  simpa only [wedge] using h.symm

end GradedForm

theorem graded_oneFormProduct (r : ℕ) (θ : Fin r → Form 𝓘(ℝ, E) P 1) :
    (List.ofFn (fun i ↦ (⟨1, θ i⟩ : GradedForm))).prod = ⟨r, oneFormProduct r θ⟩ := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.ofFn_succ', List.prod_concat, ih]
    rfl

theorem graded_twoFormProduct (r : ℕ) (B : Fin r → Form 𝓘(ℝ, E) P 2) :
    (List.ofFn (fun i ↦ (⟨2, B i⟩ : GradedForm))).prod = ⟨2*r, twoFormProduct r B⟩ := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.ofFn_succ', List.prod_concat, ih]
    apply GradedForm.eq_of_degreeCast (show 2*r+2 = 2*(r+1) by omega)
    rfl

/-- The ordered product of two-forms is invariant under every factor
permutation, in all degrees including the empty product. -/
theorem twoFormProduct_perm (r : ℕ) (B : Fin r → Form 𝓘(ℝ, E) P 2)
    (σ : Equiv.Perm (Fin r)) :
    twoFormProduct r (B ∘ σ) = twoFormProduct r B := by
  have hp := σ.ofFn_comp_perm (fun i ↦ (⟨2, B i⟩ : GradedForm))
  have hc : (List.ofFn ((fun i ↦ (⟨2, B i⟩ : GradedForm)) ∘ σ)).Pairwise Commute := by
    rw [List.pairwise_ofFn]
    intro i j _
    exact GradedForm.commute_twoForms _ _
  have h := hp.prod_eq' hc
  simp only [Function.comp_def] at h
  rw [graded_twoFormProduct, graded_twoFormProduct] at h
  exact GradedForm.mk_injective h

end GradedMonoid

section Smoothness
variable [IsManifold 𝓘(ℝ, E) ∞ P]

theorem isSmooth_oneFormProduct (r : ℕ) (θ : Fin r → Form 𝓘(ℝ, E) P 1)
    (hθ : ∀ i, IsSmooth (θ i)) : IsSmooth (oneFormProduct r θ) := by
  induction r with
  | zero => exact isSmooth_ofFunction_const 1
  | succ r ih => exact (ih _ (fun i ↦ hθ i.castSucc)).wedge (hθ (Fin.last r))

theorem isSmooth_twoFormProduct (r : ℕ) (B : Fin r → Form 𝓘(ℝ, E) P 2)
    (hB : ∀ i, IsSmooth (B i)) : IsSmooth (twoFormProduct r B) := by
  induction r with
  | zero => exact isSmooth_ofFunction_const 1
  | succ r ih =>
    exact IsSmooth.degreeCast _ ((ih _ (fun i ↦ hB i.castSucc)).wedge (hB (Fin.last r)))

end Smoothness
end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

private theorem wedge_neg_left_product {r s : ℕ}
    (α : Form 𝓘(ℝ, E) P r) (β : Form 𝓘(ℝ, E) P s) :
    wedge (-α) β = -wedge α β := by
  change wedgeLinear r s (-α) β = _
  rw [map_neg]
  rfl

private theorem wedge_neg_right_product {r s : ℕ}
    (α : Form 𝓘(ℝ, E) P r) (β : Form 𝓘(ℝ, E) P s) :
    wedge α (-β) = -wedge α β :=
  (wedgeLinear r s α).map_neg β

theorem wedge_oneForms_skew (α β : Form 𝓘(ℝ, E) P 1) :
    wedge β α = -wedge α β := by
  funext x
  ext v
  have h := wedgeFiber_graded_comm (α x) (β x) v
  have hv : (fun i ↦ v (finCongr (Nat.add_comm 1 1) i)) = v := by
    funext i
    apply congrArg v
    apply Fin.ext
    rfl
  rw [hv] at h
  simpa only [wedge, Nat.mul_one, pow_one, neg_mul, one_mul,
    ContinuousAlternatingMap.neg_apply, Pi.neg_apply] using h

theorem wedge_oneForm_tail_swap {r : ℕ} (α : Form 𝓘(ℝ, E) P r)
    (β γ : Form 𝓘(ℝ, E) P 1) :
    wedge (wedge α β) γ = -wedge (wedge α γ) β := by
  have h₁ : wedge (wedge α β) γ = wedge α (wedge β γ) := wedge_assoc α β γ
  have h₂ : wedge (wedge α γ) β = wedge α (wedge γ β) := wedge_assoc α γ β
  rw [h₁, h₂, wedge_oneForms_skew γ β, wedge_neg_right_product]

private theorem swap_castSucc_apply {n : ℕ} (i j k : Fin n) :
    Equiv.swap i.castSucc j.castSucc k.castSucc = (Equiv.swap i j k).castSucc := by
  by_cases hi : k = i
  · subst k; simp
  by_cases hj : k = j
  · subst k; simp
  rw [Equiv.swap_apply_of_ne_of_ne (fun h ↦ hi (Fin.castSucc_injective _ h))
    (fun h ↦ hj (Fin.castSucc_injective _ h)), Equiv.swap_apply_of_ne_of_ne hi hj]

private theorem swap_castSucc_last {n : ℕ} (i j : Fin n) :
    Equiv.swap i.castSucc j.castSucc (Fin.last n) = Fin.last n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hv := congrArg Fin.val h
    have := i.isLt
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    have := j.isLt
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega

/-- An adjacent transposition of one-form factors contributes exactly one
minus sign. The proof uses only the actual wedge product and its associativity. -/
theorem oneFormProduct_adjacent (n : ℕ)
    (θ : Fin (n+1) → Form 𝓘(ℝ, E) P 1) (i : Fin n) :
    oneFormProduct (n+1) (θ ∘ Equiv.swap i.castSucc i.succ) =
      -oneFormProduct (n+1) θ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · let a : Fin (n+2) := (Fin.last n).castSucc
      let b : Fin (n+2) := (Fin.last n).succ
      have hp : (fun j : Fin n ↦ θ (Equiv.swap a b j.castSucc.castSucc)) =
          (fun j : Fin n ↦ θ j.castSucc.castSucc) := by
        funext j
        apply congrArg θ
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [a, Fin.val_castSucc, Fin.val_last] at hv
          omega
        · intro h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [b, Fin.val_castSucc, Fin.val_succ, Fin.val_last] at hv
          omega
      change wedge (wedge (oneFormProduct n
        (fun j ↦ θ (Equiv.swap a b j.castSucc.castSucc)))
        (θ (Equiv.swap a b a))) (θ (Equiv.swap a b b)) =
        -wedge (wedge (oneFormProduct n (fun j ↦ θ j.castSucc.castSucc)) (θ a)) (θ b)
      rw [hp, Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact wedge_oneForm_tail_swap _ _ _
    · change wedge (oneFormProduct (n+1) (fun k ↦ θ
        (Equiv.swap j.castSucc.castSucc j.castSucc.succ k.castSucc)))
        (θ (Equiv.swap j.castSucc.castSucc j.castSucc.succ (Fin.last (n+1)))) =
        -wedge (oneFormProduct (n+1) (fun k ↦ θ k.castSucc)) (θ (Fin.last (n+1)))
      rw [← Fin.castSucc_succ]
      simp_rw [swap_castSucc_apply, swap_castSucc_last]
      have hj := ih (fun k ↦ θ k.castSucc) j
      change oneFormProduct (n+1) (fun k ↦ θ ((Equiv.swap j.castSucc j.succ) k).castSucc) =
        -oneFormProduct (n+1) (fun k ↦ θ k.castSucc) at hj
      rw [hj, wedge_neg_left_product]

end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

private def oneFormProductSignPerms (r : ℕ) : Submonoid (Equiv.Perm (Fin r)) where
  carrier := {σ | ∀ θ : Fin r → Form 𝓘(ℝ, E) P 1,
    oneFormProduct r (θ ∘ σ) = permutationSignReal σ • oneFormProduct r θ}
  one_mem' := by
    intro θ
    simp [permutationSignReal]
  mul_mem' := by
    intro σ τ hσ hτ θ
    change oneFormProduct r ((θ ∘ σ) ∘ τ) = _
    rw [hτ, hσ, permutationSignReal_mul]
    funext x
    ext v
    simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring

/-- Every permutation of independent one-form factors acts by its actual
permutation sign. This follows from adjacent factor swaps generating the
finite symmetric group, with no assumed alternating-product structure. -/
theorem oneFormProduct_perm (r : ℕ) (θ : Fin r → Form 𝓘(ℝ, E) P 1)
    (σ : Equiv.Perm (Fin r)) :
    oneFormProduct r (θ ∘ σ) = permutationSignReal σ • oneFormProduct r θ := by
  cases r with
  | zero =>
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst σ
    simp [permutationSignReal]
  | succ n =>
    have hgen : Set.range (fun i : Fin n ↦ Equiv.swap i.castSucc i.succ) ⊆
        oneFormProductSignPerms (E := E) (P := P) (n+1) := by
      rintro τ ⟨i, rfl⟩
      intro α
      rw [oneFormProduct_adjacent]
      have hne : i.castSucc ≠ i.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        omega
      have hs : permutationSignReal (Equiv.swap i.castSucc i.succ) = -1 := by
        simp [permutationSignReal, Equiv.Perm.sign_swap hne]
      rw [hs]
      funext x
      ext v
      change -(oneFormProduct (n+1) α x v) = (-1 : ℝ) * oneFormProduct (n+1) α x v
      ring
    have hclosure := Submonoid.closure_le.mpr hgen
    rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hclosure
    exact hclosure (show σ ∈ (⊤ : Submonoid (Equiv.Perm (Fin (n+1)))) by trivial) θ

end GaussBonnetChern.Chern
