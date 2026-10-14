import GaussBonnetChern.ChernConnectionVariation
import GaussBonnetChern.ChernConnectionAlternation
import GaussBonnetChern.ExteriorSmoothLinear
import GaussBonnetChern.ScalarDifferential

/-! # The actual exterior derivative with its explicit frame correction

`covariantExterior` is defined as the project's genuine exterior derivative
minus the finite connection variation. Its product and finite-sum rules below
are derived from actual wedge identities and actual differentiability results.
No derivation law, smoothness of this output, or Chern recurrence is assumed.
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
  [IsManifold 𝓘(ℝ,E) ∞ P] {W : Type*}

private theorem covariantCast_add {p q : ℕ} (h : p = q)
    (a b : Form 𝓘(ℝ,E) P p) :
    degreeCastForm h (a+b) = degreeCastForm h a + degreeCastForm h b := by
  subst q
  rfl

private theorem covariantCast_sub {p q : ℕ} (h : p = q)
    (a b : Form 𝓘(ℝ,E) P p) :
    degreeCastForm h (a-b) = degreeCastForm h a - degreeCastForm h b := by
  subst q
  rfl

private theorem covariantCast_smul {p q : ℕ} (h : p = q)
    (t : ℝ) (a : Form 𝓘(ℝ,E) P p) :
    degreeCastForm h (t • a) = t • degreeCastForm h a := by
  subst q
  rfl

private theorem covariantCast_sum {p q : ℕ} {ι : Type*} (h : p = q)
    (s : Finset ι) (a : ι → Form 𝓘(ℝ,E) P p) :
    degreeCastForm h (∑ i ∈ s, a i) = ∑ i ∈ s, degreeCastForm h (a i) := by
  subst q
  rfl

private theorem covariantCast_zero {p q : ℕ} (h : p = q) :
    degreeCastForm (E := E) (M := P) h (0 : Form 𝓘(ℝ,E) P p) = 0 := by
  subst q
  rfl

theorem connectionVariation_add {d r p : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F G : (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin r → W) :
    connectionVariation b Γ (F+G) w = connectionVariation b Γ F w + connectionVariation b Γ G w := by
  simp only [connectionVariation, Pi.add_apply, ← wedgeLinear_apply, map_add,
    Finset.sum_add_distrib]

theorem connectionVariation_smul {d r p : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (t : ℝ) (F : (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin r → W) :
    connectionVariation b Γ (t • F) w = t • connectionVariation b Γ F w := by
  simp only [connectionVariation, Pi.smul_apply, ← wedgeLinear_apply, map_smul,
    Finset.smul_sum]

theorem connectionVariation_sum {d r p : ℕ} {ι : Type*} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1) (s : Finset ι)
    (F : ι → (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin r → W) :
    connectionVariation b Γ (∑ i ∈ s, F i) w = ∑ i ∈ s, connectionVariation b Γ (F i) w := by
  classical
  simp only [connectionVariation, Finset.sum_apply, ← wedgeLinear_apply, map_sum]
  calc
    _ = ∑ i : Fin r, ∑ c ∈ s, ∑ j : Fin d,
        (wedgeLinear 1 p (Γ j (w i))) (F c (Function.update w i (b j))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The corrected derivative is explicitly the genuine `d` minus actual
connection-wedge insertions in the frame slots. -/
def covariantExterior {d r p : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F : (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin r → W) : Form 𝓘(ℝ,E) P (p+1) :=
  exteriorDerivative (F w) - degreeCastForm (Nat.add_comm 1 p) (connectionVariation b Γ F w)

theorem covariantExterior_congr {d r p : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F G : (Fin r → W) → Form 𝓘(ℝ,E) P p) (h : ∀ w, F w = G w) (w : Fin r → W) :
    covariantExterior b Γ F w = covariantExterior b Γ G w := by
  rw [show F = G from funext h]

theorem covariantExterior_degreeCast {d r p q : ℕ} (h : p = q) (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F : (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin r → W) :
    covariantExterior b Γ (fun z ↦ degreeCastForm h (F z)) w =
      degreeCastForm (congrArg (fun t ↦ t+1) h) (covariantExterior b Γ F w) := by
  subst q
  rfl

theorem covariantExterior_domDegreeCast {d r s p : ℕ} (h : r = s) (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F : (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin s → W) :
    covariantExterior b Γ (fun z ↦ F (z ∘ finCongr h)) w =
      covariantExterior b Γ F (w ∘ finCongr h) := by
  subst s
  rfl

/-- The actual empty product has zero corrected derivative. -/
theorem covariantExterior_unit {d : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1) (w : Fin 0 → W) :
    covariantExterior b Γ (fun _ : Fin 0 → W ↦ ofFunction (fun _ : P ↦ (1 : ℝ))) w = 0 := by
  rw [covariantExterior, connectionVariation_empty, covariantCast_zero,
    exteriorDerivative_ofFunction_const, sub_self]

/-- The genuine scalar Cartan identity gives the primitive corrected rule.
The supplied identity is an equality of actual exterior derivatives. -/
theorem covariantExterior_scalar_of_Cartan {d : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (U : W → P → ℝ) (Θ : W → Form 𝓘(ℝ,E) P 1)
    (hU : ∀ v, exteriorDerivative (ofFunction (U v)) =
      Θ v + ∑ j : Fin d, functionSmulLinear 1 (U (b j)) (Γ j v))
    (w : Fin 1 → W) :
    covariantExterior b Γ (fun z : Fin 1 → W ↦ ofFunction (U (z 0))) w = Θ (w 0) := by
  rw [covariantExterior, connectionVariation_scalar]
  change exteriorDerivative (ofFunction (U (w 0))) -
    (∑ j : Fin d, functionSmulLinear 1 (U (b j)) (Γ j (w 0))) = Θ (w 0)
  rw [hU, add_sub_cancel_right]

/-- The genuine direction Cartan identity leaves precisely its curvature term. -/
theorem covariantExterior_one_of_Cartan {d : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (Θ : W → Form 𝓘(ℝ,E) P 1) (Δ : W → Form 𝓘(ℝ,E) P 2)
    (hΘ : ∀ v, exteriorDerivative (Θ v) =
      Δ v + ∑ j : Fin d, wedge (Γ j v) (Θ (b j))) (w : Fin 1 → W) :
    covariantExterior b Γ (fun z : Fin 1 → W ↦ Θ (z 0)) w = Δ (w 0) := by
  rw [covariantExterior, connectionVariation_one]
  change exteriorDerivative (Θ (w 0)) -
    (∑ j : Fin d, wedge (Γ j (w 0)) (Θ (b j))) = Δ (w 0)
  rw [hΘ, add_sub_cancel_right]

/-- The actual Bianchi identity makes the primitive corrected curvature
derivative zero. Both frame-slot contributions are retained explicitly. -/
theorem covariantExterior_pair_of_Bianchi {d : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (B : W → W → Form 𝓘(ℝ,E) P 2)
    (hB : ∀ v z, exteriorDerivative (B v z) =
      (∑ j : Fin d, wedge (Γ j v) (B (b j) z)) +
        ∑ j : Fin d, wedge (Γ j z) (B v (b j))) (w : Fin 2 → W) :
    covariantExterior b Γ (fun z : Fin 2 → W ↦ B (z 0) (z 1)) w = 0 := by
  rw [covariantExterior, connectionVariation_pair]
  change exteriorDerivative (B (w 0) (w 1)) -
    ((∑ j : Fin d, wedge (Γ j (w 0)) (B (b j) (w 1))) +
      ∑ j : Fin d, wedge (Γ j (w 1)) (B (w 0) (b j))) = 0
  rw [hB, sub_self]

theorem covariantExterior_add {d r p : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F G : (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin r → W)
    (hF : IsSmooth (F w)) (hG : IsSmooth (G w)) :
    covariantExterior b Γ (F+G) w = covariantExterior b Γ F w + covariantExterior b Γ G w := by
  simp only [covariantExterior, Pi.add_apply,
    exteriorDerivative_add _ _ hF hG, connectionVariation_add, covariantCast_add]
  abel

theorem covariantExterior_smul {d r p : ℕ} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (t : ℝ) (F : (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin r → W) :
    covariantExterior b Γ (t • F) w = t • covariantExterior b Γ F w := by
  simp only [covariantExterior, Pi.smul_apply, exteriorDerivative_smul,
    connectionVariation_smul, covariantCast_smul, smul_sub]

/-- Local finite linearity requires only differentiability of the genuine
coordinate representatives at the specified point. -/
theorem covariantExterior_sum_at {d r p : ℕ} {ι : Type*} (b : Fin d → W)
    (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1) (s : Finset ι)
    (F : ι → (Fin r → W) → Form 𝓘(ℝ,E) P p) (w : Fin r → W) (x : P)
    (hF : ∀ i ∈ s, DifferentiableAt ℝ
      (chartRepresentation (chartAt E x) (F i w)) (chartAt E x x)) :
    covariantExterior b Γ (∑ i ∈ s, F i) w x = ∑ i ∈ s, covariantExterior b Γ (F i) w x := by
  simp only [covariantExterior, Finset.sum_apply, Pi.sub_apply]
  rw [exteriorDerivative_sum_at s (fun i ↦ F i w) x hF,
    connectionVariation_sum, covariantCast_sum]
  simp only [Pi.sub_apply, Finset.sum_apply, Finset.sum_sub_distrib]

/-- The connection product rule with exactly the output degrees used by
the true exterior derivative. Every transport is the canonical degree cast. -/
theorem connectionVariation_block_wedge_derivative_degree {d r s p q : ℕ}
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F : (Fin r → W) → Form 𝓘(ℝ,E) P p)
    (G : (Fin s → W) → Form 𝓘(ℝ,E) P q) (w : Fin (r+s) → W) :
    degreeCastForm (Nat.add_comm 1 (p+q))
      (connectionVariation b Γ
        (fun z ↦ wedge (F (fun i ↦ z (Fin.castAdd s i))) (G (fun j ↦ z (Fin.natAdd r j)))) w) =
      degreeCastForm (show (p+1)+q=p+q+1 by omega)
        (wedge (degreeCastForm (Nat.add_comm 1 p)
          (connectionVariation b Γ F (fun i ↦ w (Fin.castAdd s i))))
            (G (fun j ↦ w (Fin.natAdd r j)))) +
      (-1 : ℝ)^p • degreeCastForm (show p+(q+1)=p+q+1 by omega)
        (wedge (F (fun i ↦ w (Fin.castAdd s i)))
          (degreeCastForm (Nat.add_comm 1 q)
            (connectionVariation b Γ G (fun j ↦ w (Fin.natAdd r j))))) := by
  have h := congrArg (degreeCastForm (show (1+p)+q=p+q+1 by omega))
    (connectionVariation_block_wedge b Γ F G w)
  simpa only [covariantCast_add, covariantCast_smul, degreeCastForm_trans,
    degreeCastForm_wedge_left, degreeCastForm_wedge_right] using h

private theorem covariant_wedge_sub_left {p q : ℕ}
    (a a' : Form 𝓘(ℝ,E) P p) (b : Form 𝓘(ℝ,E) P q) :
    wedge (a-a') b = wedge a b - wedge a' b :=
  ((wedgeLinear p q).flip b).map_sub a a'

private theorem covariant_wedge_sub_right {p q : ℕ}
    (a : Form 𝓘(ℝ,E) P p) (b b' : Form 𝓘(ℝ,E) P q) :
    wedge a (b-b') = wedge a b - wedge a b' := (wedgeLinear p q a).map_sub b b'

/-- Derived graded Leibniz rule for the actual corrected derivative.
Smoothness is required only for the actual factors at the supplied frame tuple. -/
theorem covariantExterior_block_wedge {d r s p q : ℕ}
    (b : Fin d → W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (F : (Fin r → W) → Form 𝓘(ℝ,E) P p)
    (G : (Fin s → W) → Form 𝓘(ℝ,E) P q) (w : Fin (r+s) → W)
    (hF : IsSmooth (F (fun i ↦ w (Fin.castAdd s i))))
    (hG : IsSmooth (G (fun j ↦ w (Fin.natAdd r j)))) :
    covariantExterior b Γ
      (fun z ↦ wedge (F (fun i ↦ z (Fin.castAdd s i))) (G (fun j ↦ z (Fin.natAdd r j)))) w =
      degreeCastForm (show (p+1)+q=p+q+1 by omega)
        (wedge (covariantExterior b Γ F (fun i ↦ w (Fin.castAdd s i)))
          (G (fun j ↦ w (Fin.natAdd r j)))) +
      (-1 : ℝ)^p • degreeCastForm (show p+(q+1)=p+q+1 by omega)
        (wedge (F (fun i ↦ w (Fin.castAdd s i)))
          (covariantExterior b Γ G (fun j ↦ w (Fin.natAdd r j)))) := by
  unfold covariantExterior
  rw [exteriorDerivative_wedge _ _ hF hG,
    connectionVariation_block_wedge_derivative_degree b Γ F G w]
  rw [covariant_wedge_sub_left, covariant_wedge_sub_right]
  simp only [covariantCast_sub, smul_sub]
  abel

section TopFrameAlternation
variable [AddCommGroup W] [Module ℝ W]

/-- After full frame alternation the explicit connection correction vanishes
for a skew frame connection. Thus the genuine `d` equals the alternation of
the genuine corrected derivative. Smoothness is imposed on the actual finite
family being differentiated, not postulated as an operator property. -/
theorem exteriorDerivative_alternatization_eq_covariantExterior {d q : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin d ↦ W) (Form 𝓘(ℝ,E) P q))
    (b : Basis (Fin d) ℝ W) (Γ : Fin d → W → Form 𝓘(ℝ,E) P 1)
    (hΓ : ∀ i j, Γ i (b j) = -Γ j (b i))
    (hF : ∀ σ : Equiv.Perm (Fin d), IsSmooth (F (b ∘ σ))) :
    exteriorDerivative (F.alternatization b) =
      ∑ σ : Equiv.Perm (Fin d), permutationSignReal σ • covariantExterior b Γ F (b ∘ σ) := by
  have hz : (∑ σ : Equiv.Perm (Fin d), permutationSignReal σ •
      connectionVariation b Γ F (b ∘ σ)) = 0 := by
    simpa only [frameConnectionInsertionSum, connectionVariation, Function.comp_apply]
      using frameConnectionInsertionSum_zero_of_skew F b (fun i j ↦ Γ i (b j)) hΓ
  rw [chernAlternatization_apply_realSign,
    exteriorDerivative_sum Finset.univ _ (fun σ _ ↦ (hF σ).const_smul _)]
  simp only [exteriorDerivative_smul, covariantExterior, smul_sub, Finset.sum_sub_distrib]
  simp_rw [← covariantCast_smul]
  rw [← covariantCast_sum, hz, covariantCast_zero, sub_zero]

end TopFrameAlternation

end GaussBonnetChern.Chern
