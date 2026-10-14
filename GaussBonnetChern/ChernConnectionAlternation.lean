import GaussBonnetChern.ChernAngularAlgebra

/-! # Cancellation of the actual connection terms in Chern's alternation

The connection correction is an explicit finite sum of genuine exterior products
with one frame argument replaced. Reindexing the replaced slot through the frame
permutation turns it into the connection trace wedged with the top alternating
polynomial. Repeated basis arguments eliminate every off-diagonal term.

Identifying the connection terms in the differentiated `Φ_k` with this expression
is a separate algebraic step. No differential or recurrence identity is assumed.
-/

noncomputable section
open scoped Manifold BigOperators
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section RealAlternation
variable {d : ℕ} {W V : Type*} [AddCommGroup W] [Module ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- The actual alternatization formula expressed with real permutation signs. -/
theorem chernAlternatization_apply_realSign
    (F : MultilinearMap ℝ (fun _ : Fin d ↦ W) V) (w : Fin d → W) :
    F.alternatization w =
      ∑ σ : Equiv.Perm (Fin d), permutationSignReal σ • F (w ∘ σ) := by
  rw [MultilinearMap.alternatization_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [MultilinearMap.domDomCongr_apply, Units.smul_def]
  change (Equiv.Perm.sign σ : ℤ) • F (w ∘ σ) =
    ((Equiv.Perm.sign σ : ℤ) : ℝ) • F (w ∘ σ)
  exact (Int.cast_smul_eq_zsmul ℝ _ _).symm

end RealAlternation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W] {d q : ℕ}

/-- Concrete connection contribution before frame alternation. The one-form
is on the left and one original frame input is replaced by a basis vector. -/
def frameConnectionInsertionSum
    (F : MultilinearMap ℝ (fun _ : Fin d ↦ W) (Form 𝓘(ℝ,E) P q))
    (b : Basis (Fin d) ℝ W) (Γ : Fin d → Fin d → Form 𝓘(ℝ,E) P 1) :
    Form 𝓘(ℝ,E) P (1+q) :=
  ∑ σ : Equiv.Perm (Fin d), permutationSignReal σ •
    ∑ i : Fin d, ∑ j : Fin d,
      wedge (Γ j (σ i)) (F (Function.update (b ∘ σ) i (b j)))

/-- The concrete connection-wedge expression commutes with full frame
alternation after the replaced slot is reindexed by the frame permutation. -/
theorem frameConnectionInsertionSum_eq
    (F : MultilinearMap ℝ (fun _ : Fin d ↦ W) (Form 𝓘(ℝ,E) P q))
    (b : Basis (Fin d) ℝ W) (Γ : Fin d → Fin d → Form 𝓘(ℝ,E) P 1) :
    frameConnectionInsertionSum F b Γ =
      ∑ a : Fin d, ∑ j : Fin d, wedge (Γ j a) (F.alternatization (Function.update b a (b j))) := by
  have hi (σ : Equiv.Perm (Fin d)) :
      (∑ i : Fin d, ∑ j : Fin d,
        wedge (Γ j (σ i)) (F (Function.update (b ∘ σ) i (b j)))) =
      ∑ a : Fin d, ∑ j : Fin d,
        wedge (Γ j a) (F ((Function.update b a (b j)) ∘ σ)) := by
    rw [← Equiv.sum_comp σ
      (fun a ↦ ∑ j : Fin d, wedge (Γ j a) (F ((Function.update b a (b j)) ∘ σ)))]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hu : (Function.update b (σ i) (b j)) ∘ σ =
        Function.update (b ∘ σ) i (b j) := by
      rw [Function.update_comp_equiv, Equiv.symm_apply_apply]
    exact congrArg (fun w ↦ wedge (Γ j (σ i)) (F w)) hu.symm
  unfold frameConnectionInsertionSum
  simp_rw [hi, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [chernAlternatization_apply_realSign]
  change (∑ σ : Equiv.Perm (Fin d), permutationSignReal σ •
    (wedgeLinear 1 q (Γ j a)) (F ((Function.update b a (b j)) ∘ σ))) =
    (wedgeLinear 1 q (Γ j a)) (∑ σ : Equiv.Perm (Fin d), permutationSignReal σ •
      F ((Function.update b a (b j)) ∘ σ))
  rw [map_sum]
  simp_rw [map_smul]

/-- The precise form-valued infinitesimal determinant law. This is valid
for every connection matrix, before imposing trace zero or metric skew. -/
theorem frameConnectionInsertionSum_eq_trace
    (F : MultilinearMap ℝ (fun _ : Fin d ↦ W) (Form 𝓘(ℝ,E) P q))
    (b : Basis (Fin d) ℝ W) (Γ : Fin d → Fin d → Form 𝓘(ℝ,E) P 1) :
    frameConnectionInsertionSum F b Γ = wedge (∑ i, Γ i i) (F.alternatization b) := by
  rw [frameConnectionInsertionSum_eq]
  have ha (a : Fin d) :
      (∑ j : Fin d, wedge (Γ j a) (F.alternatization (Function.update b a (b j)))) =
      wedge (Γ a a) (F.alternatization b) := by
    rw [Finset.sum_eq_single a]
    · rw [Function.update_eq_self]
    · intro j _ hja
      rw [F.alternatization.map_update_self b hja.symm]
      exact (wedgeLinear 1 q (Γ j a)).map_zero
    · simp
  simp_rw [ha]
  exact (map_sum ((wedgeLinear 1 q).flip (F.alternatization b)) (fun i ↦ Γ i i) Finset.univ).symm

/-- Trace-zero matrices contribute exactly zero to the actual alternated form. -/
theorem frameConnectionInsertionSum_zero_of_trace
    (F : MultilinearMap ℝ (fun _ : Fin d ↦ W) (Form 𝓘(ℝ,E) P q))
    (b : Basis (Fin d) ℝ W) (Γ : Fin d → Fin d → Form 𝓘(ℝ,E) P 1)
    (hΓ : ∑ i, Γ i i = 0) : frameConnectionInsertionSum F b Γ = 0 := by
  rw [frameConnectionInsertionSum_eq_trace, hΓ]
  change (wedgeLinear 1 q) 0 _ = 0
  rw [map_zero]
  rfl

theorem frameConnectionInsertionSum_zero
    (F : MultilinearMap ℝ (fun _ : Fin d ↦ W) (Form 𝓘(ℝ,E) P q))
    (b : Basis (Fin d) ℝ W) (Γ : Fin d → Fin d → Form 𝓘(ℝ,E) P 1)
    (hΓ : ∀ i, Γ i i = 0) : frameConnectionInsertionSum F b Γ = 0 := by
  apply frameConnectionInsertionSum_zero_of_trace F b Γ
  simp only [hΓ, Finset.sum_const_zero]

/-- Metric skew symmetry supplies the required trace-zero identity. -/
theorem frameConnectionInsertionSum_zero_of_skew
    (F : MultilinearMap ℝ (fun _ : Fin d ↦ W) (Form 𝓘(ℝ,E) P q))
    (b : Basis (Fin d) ℝ W) (Γ : Fin d → Fin d → Form 𝓘(ℝ,E) P 1)
    (hΓ : ∀ i j, Γ i j = -Γ j i) : frameConnectionInsertionSum F b Γ = 0 := by
  apply frameConnectionInsertionSum_zero F b Γ
  intro i
  funext x
  ext v
  have h := congrArg (fun α : Form 𝓘(ℝ,E) P 1 ↦ α x v) (hΓ i i)
  simp only [Pi.neg_apply, ContinuousAlternatingMap.neg_apply] at h
  change Γ i i x v = 0
  linarith

/-- Exact cancellation for the original Chern polynomial, with actual
scalar/one-form/two-form frame data and actual exterior multiplication. -/
theorem angularFrameConnectionInsertionSum_zero (n : ℕ) (k : Fin n)
    (U : W →ₗ[ℝ] P → ℝ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (b : Basis (Fin (2*n)) ℝ W) (Γ : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (hΓ : ∀ i j, Γ i j = -Γ j i) :
    frameConnectionInsertionSum (angularMultilinear n k U Θ B) b Γ = 0 :=
  frameConnectionInsertionSum_zero_of_skew _ b Γ hΓ

end GaussBonnetChern.Chern
