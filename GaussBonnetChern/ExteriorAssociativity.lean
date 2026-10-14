import GaussBonnetChern.ExteriorLeibniz

/-! # Associativity of the actual normalized exterior product

The proof reduces both bracketings to a single signed sum over all permutations
of the three argument blocks. All factorial cancellations are over `ℝ`.
-/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators
namespace GaussBonnetChern.DifferentialForm
set_option backward.isDefEq.respectTransparency false

private def leftBlockPerm (r s : ℕ) (τ : Equiv.Perm (Fin r)) :
    Equiv.Perm (Fin (r + s)) :=
  (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)).permCongr
    (Equiv.sumCongr τ (Equiv.refl _))

private def rightBlockPerm (r s : ℕ) (τ : Equiv.Perm (Fin s)) :
    Equiv.Perm (Fin (r + s)) :=
  (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)).permCongr
    (Equiv.sumCongr (Equiv.refl _) τ)

private theorem leftBlockPerm_sign (r s : ℕ) (τ : Equiv.Perm (Fin r)) :
    permutationSignReal (leftBlockPerm r s τ) = permutationSignReal τ := by
  simp [leftBlockPerm, permutationSignReal]

private theorem rightBlockPerm_sign (r s : ℕ) (τ : Equiv.Perm (Fin s)) :
    permutationSignReal (rightBlockPerm r s τ) = permutationSignReal τ := by
  simp [rightBlockPerm, permutationSignReal]

private theorem signedSum_absorb {N r : ℕ}
    (e : Equiv.Perm (Fin r) → Equiv.Perm (Fin N))
    (he : ∀ τ, permutationSignReal (e τ) = permutationSignReal τ)
    (H : Equiv.Perm (Fin N) → ℝ) :
    (∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin r),
      permutationSignReal σ * permutationSignReal τ * H (σ * e τ)) =
      (r.factorial : ℝ) * ∑ σ : Equiv.Perm (Fin N), permutationSignReal σ * H σ := by
  rw [Finset.sum_comm]
  have hτ (τ : Equiv.Perm (Fin r)) :
      (∑ σ : Equiv.Perm (Fin N),
        permutationSignReal σ * permutationSignReal τ * H (σ * e τ)) =
      ∑ σ : Equiv.Perm (Fin N), permutationSignReal σ * H σ := by
    simp_rw [← he τ, ← permutationSignReal_mul]
    exact Equiv.sum_comp (Equiv.mulRight (e τ)) (fun σ ↦ permutationSignReal σ * H σ)
  simp_rw [hτ]
  simp [Fintype.card_perm]

private theorem signedSum_left {E : Type*} (r s : ℕ)
    (h : (Fin r → E) → ℝ) (g : (Fin s → E) → ℝ) (v : Fin (r + s) → E) :
    (∑ σ : Equiv.Perm (Fin (r + s)), permutationSignReal σ *
      ((∑ τ : Equiv.Perm (Fin r), permutationSignReal τ *
        h (fun i ↦ v (σ (Fin.castAdd s (τ i))))) *
        g (fun i ↦ v (σ (Fin.natAdd r i))))) =
      (r.factorial : ℝ) * ∑ σ : Equiv.Perm (Fin (r + s)), permutationSignReal σ *
        (h (fun i ↦ v (σ (Fin.castAdd s i))) * g (fun i ↦ v (σ (Fin.natAdd r i)))) := by
  let H : Equiv.Perm (Fin (r + s)) → ℝ := fun σ ↦
    h (fun i ↦ v (σ (Fin.castAdd s i))) * g (fun i ↦ v (σ (Fin.natAdd r i)))
  have ha := signedSum_absorb (leftBlockPerm r s) (leftBlockPerm_sign r s) H
  convert ha using 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  simp [H, leftBlockPerm, Equiv.Perm.mul_apply, mul_assoc]

private theorem signedSum_right {E : Type*} (r s : ℕ)
    (h : (Fin r → E) → ℝ) (g : (Fin s → E) → ℝ) (v : Fin (r + s) → E) :
    (∑ σ : Equiv.Perm (Fin (r + s)), permutationSignReal σ *
      (h (fun i ↦ v (σ (Fin.castAdd s i))) *
        (∑ τ : Equiv.Perm (Fin s), permutationSignReal τ *
          g (fun i ↦ v (σ (Fin.natAdd r (τ i))))))) =
      (s.factorial : ℝ) * ∑ σ : Equiv.Perm (Fin (r + s)), permutationSignReal σ *
        (h (fun i ↦ v (σ (Fin.castAdd s i))) * g (fun i ↦ v (σ (Fin.natAdd r i)))) := by
  let H : Equiv.Perm (Fin (r + s)) → ℝ := fun σ ↦
    h (fun i ↦ v (σ (Fin.castAdd s i))) * g (fun i ↦ v (σ (Fin.natAdd r i)))
  have ha := signedSum_absorb (rightBlockPerm r s) (rightBlockPerm_sign r s) H
  convert ha using 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  simp [H, rightBlockPerm, Equiv.Perm.mul_apply]
  ring

section FiberAssociativity
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {k l m : ℕ}

private theorem left_expansion
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l))
    (c : ContinuousAlternatingMap ℝ E ℝ (Fin m)) (v : Fin ((k + l) + m) → E) :
    wedgeFiber (wedgeFiber a b) c v =
      ((k.factorial : ℝ) * (l.factorial : ℝ) * (m.factorial : ℝ))⁻¹ *
      ∑ σ : Equiv.Perm (Fin ((k + l) + m)), permutationSignReal σ *
        ((a (fun i ↦ v (σ (Fin.castAdd m (Fin.castAdd l i)))) *
          b (fun i ↦ v (σ (Fin.castAdd m (Fin.natAdd k i))))) *
          c (fun i ↦ v (σ (Fin.natAdd (k + l) i)))) := by
  let h : (Fin (k + l) → E) → ℝ := fun w ↦
    a (fun i ↦ w (Fin.castAdd l i)) * b (fun i ↦ w (Fin.natAdd k i))
  rw [wedgeFiber_apply_realSign]
  simp_rw [wedgeFiber_apply_realSign]
  have hs : (∑ σ : Equiv.Perm (Fin ((k + l) + m)), permutationSignReal σ *
      ((((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹ *
        ∑ τ : Equiv.Perm (Fin (k + l)), permutationSignReal τ *
          h (fun i ↦ v (σ (Fin.castAdd m (τ i))))) *
          c (fun i ↦ v (σ (Fin.natAdd (k + l) i))))) =
      ((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹ *
        ∑ σ : Equiv.Perm (Fin ((k + l) + m)), permutationSignReal σ *
          ((∑ τ : Equiv.Perm (Fin (k + l)), permutationSignReal τ *
            h (fun i ↦ v (σ (Fin.castAdd m (τ i))))) *
              c (fun i ↦ v (σ (Fin.natAdd (k + l) i)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  change ((↑(k + l).factorial : ℝ) * ↑m.factorial)⁻¹ * _ = _
  change ((↑(k + l).factorial : ℝ) * ↑m.factorial)⁻¹ *
    (∑ σ : Equiv.Perm (Fin ((k + l) + m)), permutationSignReal σ *
      ((((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹ *
        ∑ τ : Equiv.Perm (Fin (k + l)), permutationSignReal τ *
          h (fun i ↦ v (σ (Fin.castAdd m (τ i))))) *
          c (fun i ↦ v (σ (Fin.natAdd (k + l) i))))) = _
  rw [hs, signedSum_left (k + l) m h (fun w ↦ c w) v]
  dsimp only [h]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hl : (l.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr l.factorial_ne_zero
  have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hkl : ((k + l).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (k + l).factorial_ne_zero
  field_simp

private theorem right_expansion
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l))
    (c : ContinuousAlternatingMap ℝ E ℝ (Fin m)) (v : Fin (k + (l + m)) → E) :
    wedgeFiber a (wedgeFiber b c) v =
      ((k.factorial : ℝ) * (l.factorial : ℝ) * (m.factorial : ℝ))⁻¹ *
      ∑ σ : Equiv.Perm (Fin (k + (l + m))), permutationSignReal σ *
        (a (fun i ↦ v (σ (Fin.castAdd (l + m) i))) *
          (b (fun i ↦ v (σ (Fin.natAdd k (Fin.castAdd m i)))) *
            c (fun i ↦ v (σ (Fin.natAdd k (Fin.natAdd l i)))))) := by
  let g : (Fin (l + m) → E) → ℝ := fun w ↦
    b (fun i ↦ w (Fin.castAdd m i)) * c (fun i ↦ w (Fin.natAdd l i))
  rw [wedgeFiber_apply_realSign]
  simp_rw [wedgeFiber_apply_realSign]
  have hs : (∑ σ : Equiv.Perm (Fin (k + (l + m))), permutationSignReal σ *
      (a (fun i ↦ v (σ (Fin.castAdd (l + m) i))) *
        (((l.factorial : ℝ) * (m.factorial : ℝ))⁻¹ *
          ∑ τ : Equiv.Perm (Fin (l + m)), permutationSignReal τ *
            g (fun i ↦ v (σ (Fin.natAdd k (τ i))))))) =
      ((l.factorial : ℝ) * (m.factorial : ℝ))⁻¹ *
        ∑ σ : Equiv.Perm (Fin (k + (l + m))), permutationSignReal σ *
          (a (fun i ↦ v (σ (Fin.castAdd (l + m) i))) *
            (∑ τ : Equiv.Perm (Fin (l + m)), permutationSignReal τ *
              g (fun i ↦ v (σ (Fin.natAdd k (τ i)))))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  change ((↑k.factorial : ℝ) * ↑(l + m).factorial)⁻¹ *
    (∑ σ : Equiv.Perm (Fin (k + (l + m))), permutationSignReal σ *
      (a (fun i ↦ v (σ (Fin.castAdd (l + m) i))) *
        (((l.factorial : ℝ) * (m.factorial : ℝ))⁻¹ *
          ∑ τ : Equiv.Perm (Fin (l + m)), permutationSignReal τ *
            g (fun i ↦ v (σ (Fin.natAdd k (τ i))))))) = _
  rw [hs, signedSum_right k (l + m) (fun w ↦ a w) g v]
  dsimp only [g]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hl : (l.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr l.factorial_ne_zero
  have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hlm : ((l + m).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (l + m).factorial_ne_zero
  field_simp

/-- Associativity in arbitrary symbolic degrees, with the canonical degree cast. -/
theorem wedgeFiber_assoc_apply
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l))
    (c : ContinuousAlternatingMap ℝ E ℝ (Fin m)) (v : Fin (k + (l + m)) → E) :
    wedgeFiber (wedgeFiber a b) c (v ∘ finCongr (Nat.add_assoc k l m)) =
      wedgeFiber a (wedgeFiber b c) v := by
  rw [left_expansion, right_expansion]
  congr 1
  let e : Fin ((k + l) + m) ≃ Fin (k + (l + m)) := finCongr (Nat.add_assoc k l m)
  let H : Equiv.Perm (Fin (k + (l + m))) → ℝ := fun σ ↦ permutationSignReal σ *
    (a (fun i ↦ v (σ (Fin.castAdd (l + m) i))) *
      (b (fun i ↦ v (σ (Fin.natAdd k (Fin.castAdd m i)))) *
        c (fun i ↦ v (σ (Fin.natAdd k (Fin.natAdd l i))))))
  calc
    _ = ∑ σ : Equiv.Perm (Fin ((k + l) + m)), H (e.permCongr σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      simp only [H, permutationSignReal_permCongr, Function.comp_apply]
      have h₁ : (fun i : Fin k ↦ v (e (σ (Fin.castAdd m (Fin.castAdd l i))))) =
          (fun i : Fin k ↦ v (e.permCongr σ (Fin.castAdd (l + m) i))) := by
        funext i
        rw [Equiv.permCongr_apply]
        apply congrArg v
        apply congrArg e
        apply congrArg σ
        apply Fin.ext
        simp [e]
      have h₂ : (fun i : Fin l ↦ v (e (σ (Fin.castAdd m (Fin.natAdd k i))))) =
          (fun i : Fin l ↦ v (e.permCongr σ (Fin.natAdd k (Fin.castAdd m i)))) := by
        funext i
        rw [Equiv.permCongr_apply]
        apply congrArg v
        apply congrArg e
        apply congrArg σ
        apply Fin.ext
        simp [e]
      have h₃ : (fun i : Fin m ↦ v (e (σ (Fin.natAdd (k + l) i)))) =
          (fun i : Fin m ↦ v (e.permCongr σ (Fin.natAdd k (Fin.natAdd l i)))) := by
        funext i
        rw [Equiv.permCongr_apply]
        apply congrArg v
        apply congrArg e
        apply congrArg σ
        apply Fin.ext
        simp [e, Nat.add_assoc]
      change permutationSignReal σ *
        ((a (fun i ↦ v (e (σ (Fin.castAdd m (Fin.castAdd l i))))) *
          b (fun i ↦ v (e (σ (Fin.castAdd m (Fin.natAdd k i)))))) *
          c (fun i ↦ v (e (σ (Fin.natAdd (k + l) i))))) = _
      rw [h₁, h₂, h₃]
      ring
    _ = _ := Equiv.sum_comp e.permCongr H

/-- A zero-form on the right acts by ordinary scalar multiplication. -/
theorem wedgeFiber_const_right
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k)) (t : ℝ) (v : Fin (k + 0) → E) :
    wedgeFiber a (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) t) v = t * a v := by
  rw [wedgeFiber_apply_realSign]
  have hp (σ : Equiv.Perm (Fin k)) :
      a (fun i ↦ v (σ i)) = permutationSignReal σ * a v := by
    simpa [permutationSignReal, Units.smul_def, zsmul_eq_mul, Function.comp_def]
      using a.toAlternatingMap.map_perm v σ
  have hs (σ : Equiv.Perm (Fin k)) :
      permutationSignReal σ * (a (fun i ↦ v (σ i)) * t) = a v * t := by
    rw [hp]
    calc
      _ = (permutationSignReal σ * permutationSignReal σ) * (a v * t) := by ring
      _ = _ := by rw [permutationSignReal_sq, one_mul]
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one,
    ContinuousAlternatingMap.constOfIsEmpty_apply]
  change (k.factorial : ℝ)⁻¹ *
    (∑ σ : Equiv.Perm (Fin k), permutationSignReal σ * (a (fun i ↦ v (σ i)) * t)) = t * a v
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp

/-- A zero-form on the left acts by ordinary scalar multiplication. -/
theorem wedgeFiber_const_left
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k)) (t : ℝ) (v : Fin (0 + k) → E) :
    wedgeFiber (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) t) a v =
      t * a (v ∘ finCongr (Nat.zero_add k).symm) := by
  have h := wedgeFiber_graded_comm a
    (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) t)
    (v ∘ finCongr (Nat.add_comm k 0))
  have hv : (fun i : Fin (0 + k) ↦
      (v ∘ finCongr (Nat.add_comm k 0)) (finCongr (Nat.add_comm 0 k) i)) = v := by
    funext i
    simp
  rw [hv, wedgeFiber_const_right] at h
  simp only [Nat.mul_zero, pow_zero, one_mul] at h
  refine h.trans ?_
  apply congrArg (fun w : Fin k → E ↦ t * a w)
  funext i
  apply congrArg v
  apply Fin.ext
  rfl

end FiberAssociativity

section ManifoldAssociativity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {k l m : ℕ}

/-- Degree transport evaluation uses only the charted-space structure. -/
@[simp] theorem degreeCastForm_apply_intrinsic {r s : ℕ} (h : r = s)
    (α : Form 𝓘(ℝ, E) M r) (x : M) (v : Fin s → TangentSpace 𝓘(ℝ, E) x) :
    degreeCastForm h α x v = α x (v ∘ finCongr h) := by
  subst s
  rfl
/-- Genuine manifold forms inherit fiber associativity, including degree zero. -/
theorem wedge_assoc (α : Form 𝓘(ℝ, E) M k) (β : Form 𝓘(ℝ, E) M l)
    (γ : Form 𝓘(ℝ, E) M m) :
    degreeCastForm (Nat.add_assoc k l m) (wedge (wedge α β) γ) =
      wedge α (wedge β γ) := by
  funext x
  ext v
  rw [degreeCastForm_apply_intrinsic]
  exact wedgeFiber_assoc_apply (α x) (β x) (γ x) v

/-- Composing order-preserving degree transports inserts no additional action. -/
@[simp] theorem degreeCastForm_trans {r s t : ℕ} (h : r = s) (h' : s = t)
    (α : Form 𝓘(ℝ, E) M r) :
    degreeCastForm h' (degreeCastForm h α) = degreeCastForm (h.trans h') α := by
  subst s t
  rfl

/-- Degree transport commutes with exterior multiplication in the left slot. -/
theorem degreeCastForm_wedge_left {r s t : ℕ} (h : r = s)
    (α : Form 𝓘(ℝ, E) M r) (β : Form 𝓘(ℝ, E) M t) :
    wedge (degreeCastForm h α) β =
      degreeCastForm (congrArg (fun q ↦ q + t) h) (wedge α β) := by
  subst s
  rfl

/-- Degree transport commutes with exterior multiplication in the right slot. -/
theorem degreeCastForm_wedge_right {r s t : ℕ} (h : s = t)
    (α : Form 𝓘(ℝ, E) M r) (β : Form 𝓘(ℝ, E) M s) :
    wedge α (degreeCastForm h β) =
      degreeCastForm (congrArg (fun q ↦ r + q) h) (wedge α β) := by
  subst t
  rfl

/-- Multiplication by a function is the exterior product with its zero-form. -/
theorem wedge_ofFunction_right (α : Form 𝓘(ℝ, E) M k) (f : M → ℝ) :
    wedge α (ofFunction f) = fun x ↦ f x • α x := by
  funext x
  ext v
  exact wedgeFiber_const_right (α x) (f x) v

/-- The constant one zero-form is a right identity for actual exterior product. -/
@[simp] theorem wedge_one_right (α : Form 𝓘(ℝ, E) M k) :
    wedge α (ofFunction (fun _ ↦ 1)) = α := by
  rw [wedge_ofFunction_right]
  simp

/-- The constant one zero-form is a left identity after the canonical degree cast. -/
@[simp] theorem wedge_one_left (α : Form 𝓘(ℝ, E) M k) :
    degreeCastForm (Nat.zero_add k) (wedge (ofFunction (fun _ ↦ 1)) α) = α := by
  funext x
  ext v
  rw [degreeCastForm_apply_intrinsic]
  change wedgeFiber (ContinuousAlternatingMap.constOfIsEmpty ℝ _ (Fin 0) 1)
    (α x) (v ∘ finCongr (Nat.zero_add k)) = α x v
  rw [wedgeFiber_const_left, one_mul]
  congr 1

end ManifoldAssociativity

end GaussBonnetChern.DifferentialForm
