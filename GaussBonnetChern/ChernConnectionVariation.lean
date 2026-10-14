import GaussBonnetChern.ChernAngularAlgebra

noncomputable section
open scoped Manifold BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

theorem wedge_degreeCast_comm {p q : ℕ}
    (a : Form 𝓘(ℝ,E) P p) (b : Form 𝓘(ℝ,E) P q) :
    degreeCastForm (Nat.add_comm p q) (wedge a b) = (-1 : ℝ)^(p*q) • wedge b a := by
  funext x
  ext v
  rw [degreeCastForm_apply_intrinsic]
  simpa only [wedge, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    Nat.mul_comm, Function.comp_def] using wedgeFiber_graded_comm (b x) (a x) v

theorem wedge_assoc_cast_back {p q s : ℕ}
    (a : Form 𝓘(ℝ,E) P p) (b : Form 𝓘(ℝ,E) P q) (c : Form 𝓘(ℝ,E) P s) :
    degreeCastForm (Nat.add_assoc p q s).symm (wedge a (wedge b c)) = wedge (wedge a b) c := by
  rw [← wedge_assoc a b c, degreeCastForm_trans]
  rfl

/-- Move the connection one-form through a genuine form of degree `p`.
This supplies exactly the Koszul sign needed to match the real Leibniz rule. -/
theorem wedge_one_move_across {p q : ℕ}
    (a : Form 𝓘(ℝ,E) P p) (γ : Form 𝓘(ℝ,E) P 1) (b : Form 𝓘(ℝ,E) P q) :
    degreeCastForm (show p+(1+q)=(1+p)+q by omega) (wedge a (wedge γ b)) =
      (-1 : ℝ)^p • wedge (wedge γ a) b := by
  rw [← wedge_assoc a γ b, degreeCastForm_trans]
  have hc : degreeCastForm (show (p+1)+q=(1+p)+q by omega) (wedge (wedge a γ) b) =
      wedge (degreeCastForm (Nat.add_comm p 1) (wedge a γ)) b :=
    (degreeCastForm_wedge_left (Nat.add_comm p 1) (wedge a γ) b).symm
  rw [hc, wedge_degreeCast_comm, Nat.mul_one]
  exact congrArg (fun L ↦ L b) ((wedgeLinear (1+p) q).map_smul ((-1 : ℝ)^p) (wedge γ a))

/-- Explicit connection action on an actual form-valued frame expression.
It is defined by a finite sum of genuine wedge products, not by an assumed
derivation law or a placeholder differential operator. -/
def connectionVariation {W : Type*} {d r p : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F : (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin r → W) :
    Form 𝓘(ℝ,E) P (1+p) :=
  ∑ i : Fin r, ∑ j : Fin d, wedge (Γ j (w i)) (F (Function.update w i (b j)))

/-- The actual connection variation respects equality of the actual frame expression. -/
theorem connectionVariation_congr {W : Type*} {d r p : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F G : (Fin r → W) → Form 𝓘(ℝ,E) P p) (h : ∀ w, F w = G w) (w : Fin r → W) :
    connectionVariation b Γ F w = connectionVariation b Γ G w := by
  simp only [connectionVariation, h]

theorem connectionVariation_empty {W : Type*} {d p : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F : (Fin 0 → W) → Form 𝓘(ℝ,E) P p) (w : Fin 0 → W) :
    connectionVariation b Γ F w = 0 := by
  simp only [connectionVariation, Fin.sum_univ_zero]

theorem connectionVariation_degreeCast {W : Type*} {d r p q : ℕ} (h : p = q)
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F : (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin r → W) :
    connectionVariation b Γ (fun z ↦ degreeCastForm h (F z)) w =
      degreeCastForm (congrArg (fun t ↦ 1+t) h) (connectionVariation b Γ F w) := by
  subst q
  rfl

theorem connectionVariation_domDegreeCast {W : Type*} {d r s p : ℕ} (h : r = s)
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F : (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin s → W) :
    connectionVariation b Γ (fun z ↦ F (z ∘ finCongr h)) w =
      connectionVariation b Γ F (w ∘ finCongr h) := by
  subst s
  rfl

/-- Connection action on a scalar frame coordinate, represented as an actual zero-form. -/
theorem connectionVariation_scalar {W : Type*} {d : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1) (U : W → P → ℝ) (w : Fin 1 → W) :
    connectionVariation b Γ (fun z : Fin 1 → W ↦ ofFunction (U (z 0))) w =
      ∑ j : Fin d, functionSmulLinear 1 (U (b j)) (Γ j (w 0)) := by
  simp only [connectionVariation, Fin.sum_univ_one, Function.update_self]
  apply Finset.sum_congr rfl
  intro j _
  rw [wedge_ofFunction_right]
  rfl

/-- Connection action on a one-form frame component. -/
theorem connectionVariation_one {W : Type*} {d : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (Θ : W → Form 𝓘(ℝ,E) P 1) (w : Fin 1 → W) :
    connectionVariation b Γ (fun z : Fin 1 → W ↦ Θ (z 0)) w =
      ∑ j : Fin d, wedge (Γ j (w 0)) (Θ (b j)) := by
  simp only [connectionVariation, Fin.sum_univ_one, Function.update_self]

/-- Both genuine frame slots of a curvature two-form contribute. No symmetry
or structure equation for `B` is assumed in this finite evaluation identity. -/
theorem connectionVariation_pair {W : Type*} {d : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (B : W → W → Form 𝓘(ℝ,E) P 2) (w : Fin 2 → W) :
    connectionVariation b Γ (fun z : Fin 2 → W ↦ B (z 0) (z 1)) w =
      (∑ j : Fin d, wedge (Γ j (w 0)) (B (b j) (w 1))) +
        ∑ j : Fin d, wedge (Γ j (w 1)) (B (w 0) (b j)) := by
  simp [connectionVariation, Fin.sum_univ_two]

theorem update_restrict_left {W : Type*} {r s : ℕ} (w : Fin (r+s) → W)
    (i : Fin r) (u : W) :
    (fun j : Fin r ↦ Function.update w (Fin.castAdd s i) u (Fin.castAdd s j)) =
      Function.update (fun j : Fin r ↦ w (Fin.castAdd s j)) i u := by
  funext j
  by_cases hj : j = i
  · subst j; simp
  · have hji : Fin.castAdd s j ≠ Fin.castAdd s i := by
      intro h
      have hv : j.val = i.val := congrArg (fun a : Fin (r+s) ↦ a.val) h
      exact hj (Fin.ext hv)
    simp only [Function.update_of_ne hj, Function.update_of_ne hji]

theorem update_left_restrict_right {W : Type*} {r s : ℕ} (w : Fin (r+s) → W)
    (i : Fin r) (u : W) :
    (fun j : Fin s ↦ Function.update w (Fin.castAdd s i) u (Fin.natAdd r j)) =
      (fun j : Fin s ↦ w (Fin.natAdd r j)) := by
  funext j
  apply Function.update_of_ne
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
  have := i.isLt
  omega

theorem update_restrict_right {W : Type*} {r s : ℕ} (w : Fin (r+s) → W)
    (i : Fin s) (u : W) :
    (fun j : Fin s ↦ Function.update w (Fin.natAdd r i) u (Fin.natAdd r j)) =
      Function.update (fun j : Fin s ↦ w (Fin.natAdd r j)) i u := by
  funext j
  by_cases hj : j = i
  · subst j; simp
  · have hji : Fin.natAdd r j ≠ Fin.natAdd r i := by
      intro h
      apply hj
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      omega
    simp only [Function.update_of_ne hj, Function.update_of_ne hji]

theorem update_right_restrict_left {W : Type*} {r s : ℕ} (w : Fin (r+s) → W)
    (i : Fin s) (u : W) :
    (fun j : Fin r ↦ Function.update w (Fin.natAdd r i) u (Fin.castAdd s j)) =
      (fun j : Fin r ↦ w (Fin.castAdd s j)) := by
  funext j
  apply Function.update_of_ne
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
  have := j.isLt
  omega

/-- The finite connection action satisfies the graded product rule for the
actual normalized wedge. The proof partitions the actual frame slots; it does
not introduce or assume a new differential operator law. -/
theorem connectionVariation_block_wedge {W : Type*} {d r s p q : ℕ}
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F : (Fin r → W) → Form 𝓘(ℝ,E) P p)
    (G : (Fin s → W) → Form 𝓘(ℝ,E) P q) (w : Fin (r+s) → W) :
    degreeCastForm (Nat.add_assoc 1 p q).symm
      (connectionVariation b Γ
        (fun z ↦ wedge (F (fun i ↦ z (Fin.castAdd s i))) (G (fun j ↦ z (Fin.natAdd r j)))) w) =
      wedge (connectionVariation b Γ F (fun i ↦ w (Fin.castAdd s i)))
        (G (fun j ↦ w (Fin.natAdd r j))) +
      (-1 : ℝ)^p • degreeCastForm (show p+(1+q)=(1+p)+q by omega)
        (wedge (F (fun i ↦ w (Fin.castAdd s i)))
          (connectionVariation b Γ G (fun j ↦ w (Fin.natAdd r j)))) := by
  let w₁ : Fin r → W := fun i ↦ w (Fin.castAdd s i)
  let w₂ : Fin s → W := fun i ↦ w (Fin.natAdd r i)
  let L := formCastLinear (E := E) (P := P) (Nat.add_assoc 1 p q).symm
  let R := formCastLinear (E := E) (P := P) (show p+(1+q)=(1+p)+q by omega)
  have hleft (i : Fin r) (j : Fin d) :
      L (wedge (Γ j (w₁ i)) (wedge (F (Function.update w₁ i (b j))) (G w₂))) =
        wedge (wedge (Γ j (w₁ i)) (F (Function.update w₁ i (b j)))) (G w₂) :=
    by
      simpa only [L, formCastLinear_apply] using wedge_assoc_cast_back
        (Γ j (w₁ i)) (F (Function.update w₁ i (b j))) (G w₂)
  have hright (i : Fin s) (j : Fin d) :
      L (wedge (Γ j (w₂ i)) (wedge (F w₁) (G (Function.update w₂ i (b j))))) =
        (-1 : ℝ)^p • R (wedge (F w₁) (wedge (Γ j (w₂ i)) (G (Function.update w₂ i (b j))))) := by
    simp only [L, R, formCastLinear_apply]
    rw [wedge_assoc_cast_back, wedge_one_move_across, smul_smul]
    have hs : (-1 : ℝ)^p * (-1 : ℝ)^p = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    rw [hs, one_smul]
  rw [← formCastLinear_apply (Nat.add_assoc 1 p q).symm,
    ← formCastLinear_apply (show p+(1+q)=(1+p)+q by omega)]
  unfold connectionVariation
  change L (∑ i : Fin (r+s), ∑ j : Fin d, wedge (Γ j (w i))
      (wedge (F (fun a ↦ Function.update w i (b j) (Fin.castAdd s a)))
        (G (fun a ↦ Function.update w i (b j) (Fin.natAdd r a))))) =
    wedge (∑ i : Fin r, ∑ j : Fin d, wedge (Γ j (w₁ i)) (F (Function.update w₁ i (b j)))) (G w₂) +
      (-1 : ℝ)^p • R (wedge (F w₁)
        (∑ i : Fin s, ∑ j : Fin d, wedge (Γ j (w₂ i)) (G (Function.update w₂ i (b j)))))
  rw [← Equiv.sum_comp (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r+s)), Fintype.sum_sum_type, map_add]
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    update_restrict_left, update_left_restrict_right, update_restrict_right,
    update_right_restrict_left]
  simp_rw [map_sum]
  change (∑ i : Fin r, ∑ j : Fin d,
      L (wedge (Γ j (w₁ i)) (wedge (F (Function.update w₁ i (b j))) (G w₂)))) +
    (∑ i : Fin s, ∑ j : Fin d,
      L (wedge (Γ j (w₂ i)) (wedge (F w₁) (G (Function.update w₂ i (b j)))))) = _
  simp_rw [hleft, hright]
  congr 1
  · change (∑ i : Fin r, ∑ j : Fin d,
      ((wedgeLinear (1+p) q).flip (G w₂))
        (wedge (Γ j (w₁ i)) (F (Function.update w₁ i (b j))))) =
      ((wedgeLinear (1+p) q).flip (G w₂))
        (∑ i : Fin r, ∑ j : Fin d, wedge (Γ j (w₁ i)) (F (Function.update w₁ i (b j))))
    simp only [map_sum]
  · change (∑ i : Fin s, ∑ j : Fin d, (-1 : ℝ)^p •
      (R.comp (wedgeLinear p (1+q) (F w₁)))
        (wedge (Γ j (w₂ i)) (G (Function.update w₂ i (b j))))) =
      (-1 : ℝ)^p • (R.comp (wedgeLinear p (1+q) (F w₁)))
        (∑ i : Fin s, ∑ j : Fin d, wedge (Γ j (w₂ i)) (G (Function.update w₂ i (b j))))
    simp only [map_sum, Finset.smul_sum]

end GaussBonnetChern.Chern

