import GaussBonnetChern.Pfaffian
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import GaussBonnetChern.ExteriorLeibniz
import GaussBonnetChern.UnitTangentSphere

/-! # The numerical coefficients in Chern's angular form

These are the coefficients for the project's curvature convention
`B_ab = ⟪R(-,-) e_b,e_a⟫`. Chern's 1944 matrix `Ω_ij`, defined using
`de_i = ω_ij e_j`, is the negative of this matrix. Thus all the coefficients
below are positive: the sign `(-1)^k` in Chern's equation (24) is absorbed
by the `k` curvature factors. The resulting differential is **minus** the
Euler form and the fiber orientation has positive normalization.

The finite-sum theorem in this file is only the algebraic elimination of a
specified recurrence. It does not assert that geometric forms satisfy that
recurrence. That remaining geometric identity is not an axiom here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators

namespace GaussBonnetChern
namespace Chern

/-- Coefficient of the term with `k` curvature factors in ambient dimension
`2*n`. For the angular form, `k < n`; the endpoint `k = n` conveniently
records the Euler/Pfaffian coefficient after telescoping. -/
def angularCoefficient (n k : ℕ) : ℝ :=
  1 / (Real.pi ^ n * (Nat.doubleFactorial (2*n - 2*k - 1) : ℝ) *
    (k.factorial : ℝ) * 2 ^ (n+k))

/-- The coefficient in the local derivative recurrence in our convention. -/
def recurrenceCoefficient (n k : ℕ) : ℝ :=
  (2 * (n : ℝ) - 2 * k - 1) / (2 * (k+1))

theorem angularCoefficient_pos (n k : ℕ) : 0 < angularCoefficient n k := by
  unfold angularCoefficient
  positivity

private theorem doubleFactorial_odd_step (m : ℕ) :
    Nat.doubleFactorial (2*m+1) = (2*m+1) * Nat.doubleFactorial (2*m-1) := by
  cases m with
  | zero => norm_num
  | succ m =>
    have h₁ : 2 * (m+1) + 1 = (2*m+1)+2 := by omega
    have h₂ : 2 * (m+1) - 1 = 2*m+1 := by omega
    rw [h₁, h₂, Nat.doubleFactorial_add_two]

theorem angularCoefficient_succ {n k : ℕ} (hk : k < n) :
    angularCoefficient n (k+1) =
      angularCoefficient n k * recurrenceCoefficient n k := by
  have h₁ : 2*n - 2*k - 1 = 2*(n-k-1)+1 := by omega
  have h₂ : 2*n - 2*(k+1) - 1 = 2*(n-k-1)-1 := by omega
  have hdf : Nat.doubleFactorial (2*n-2*k-1) =
      (2*n-2*k-1) * Nat.doubleFactorial (2*n-2*(k+1)-1) := by
    rw [h₁, h₂, doubleFactorial_odd_step]
  have hcast : ((2*n-2*k-1 : ℕ) : ℝ) = 2*(n:ℝ)-2*k-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hodd : (2*(n:ℝ)-2*k-1) ≠ 0 := by
    have h : (k:ℝ) + 1 ≤ n := by exact_mod_cast hk
    linarith
  have hodd' : -1 + (n:ℝ)*2 - (k:ℝ)*2 ≠ 0 := by
    intro hz
    apply hodd
    linarith
  have hp : Real.pi ^ n ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (k.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hd : (Nat.doubleFactorial (2*n-2*(k+1)-1):ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  have hkp : (k:ℝ)+1 ≠ 0 := by positivity
  unfold angularCoefficient recurrenceCoefficient
  rw [hdf, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul, hcast,
    Nat.cast_add, Nat.cast_one, show n + (k+1) = (n+k)+1 by omega, pow_succ]
  field_simp [hodd, hodd', hp, hf, hd, hkp]
  <;> ring_nf
  <;> nlinarith only [inv_mul_cancel₀ hodd']

/-- Endpoint coefficient agrees exactly with the Pfaffian normalization of
an alternating curvature matrix: `1/(2^n n! (2π)^n)`. -/
theorem angularCoefficient_top (n : ℕ) :
    angularCoefficient n n =
      1 / ((2:ℝ)^n * (n.factorial:ℝ) * (2*Real.pi)^n) := by
  simp only [angularCoefficient, Nat.sub_self, Nat.zero_sub,
    Nat.doubleFactorial, Nat.cast_one, mul_one, pow_add, mul_pow]
  congr 1
  ring

/-- The coefficient of the purely vertical term has precisely the reciprocal
sphere normalization, including the factorial from full alternation. -/
theorem angularCoefficient_fiber_normalization (n : ℕ) (hn : 0 < n) :
    angularCoefficient n 0 * ((2*n-1).factorial : ℝ) *
      (2 * Real.pi ^ n / ((n-1).factorial : ℝ)) = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hodd : 2*(m+1)-1 = 2*m+1 := by omega
  simp only [angularCoefficient, mul_zero, Nat.sub_zero, hodd,
    Nat.factorial_zero, Nat.cast_one, mul_one, Nat.add_zero, Nat.succ_sub_one,
    Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hd : (Nat.doubleFactorial (2*m+1):ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  have hf : (m.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp
  <;> ring

/-- Numerical normalization against the actual polar sphere measure. The
remaining geometric obligation is to identify the restriction of `Φ₀` with
`(2*n-1)!` times the oriented sphere volume form and its integral. -/
theorem angularCoefficient_mul_sphereMeasure (n : ℕ) (hn : 0 < n) :
    angularCoefficient n 0 * ((2*n-1).factorial : ℝ) *
      (MeasureTheory.volume : MeasureTheory.Measure (Model n)).toSphere.real Set.univ = 1 := by
  rw [sphereMeasure_mass n hn]
  exact angularCoefficient_fiber_normalization n hn

/-- Exact telescoping for Chern's derivative recurrence. `Y 0 = 0` corresponds
to Chern's convention `Ψ₋₁ = 0`. The hypotheses describe local inputs, and
do not stand in for a proof that the actual curvature forms satisfy them. -/
theorem recurrence_telescope {V : Type*} [AddCommGroup V] [Module ℝ V]
    (n : ℕ) (Y : ℕ → V) (hY : Y 0 = 0) :
    (∑ k ∈ Finset.range n, angularCoefficient n k •
      (Y k - recurrenceCoefficient n k • Y (k+1))) =
      -(angularCoefficient n n • Y n) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range n) :
      angularCoefficient n k • (Y k - recurrenceCoefficient n k • Y (k+1)) =
      angularCoefficient n k • Y k - angularCoefficient n (k+1) • Y (k+1) := by
    rw [smul_sub, smul_smul, angularCoefficient_succ (Finset.mem_range.mp hk)]
  simp_rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_range_sub']
  simp [hY]

/-- Apply the finite recurrence to a genuine linear differential operator.
All the recurrence obligations remain explicit; this is not the geometric
transgression theorem. -/
theorem differential_angularSum {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (D : V →ₗ[ℝ] W) (n : ℕ) (Φ : ℕ → V) (Y : ℕ → W)
    (hY : Y 0 = 0)
    (hrec : ∀ k < n, D (Φ k) = Y k - recurrenceCoefficient n k • Y (k+1)) :
    D (∑ k ∈ Finset.range n, angularCoefficient n k • Φ k) =
      -(angularCoefficient n n • Y n) := by
  simp only [map_sum, map_smul]
  calc
    _ = ∑ k ∈ Finset.range n, angularCoefficient n k •
        (Y k - recurrenceCoefficient n k • Y (k+1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hrec k (Finset.mem_range.mp hk)]
    _ = _ := recurrence_telescope n Y hY

section ActualForms
open DifferentialForm
open scoped Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

/-- Ordered exterior product of genuine one-forms. The empty product is the
constant one zero-form; no exterior-algebra multiplication is assumed. -/
def oneFormProduct : (r : ℕ) → (Fin r → Form 𝓘(ℝ,E) P 1) → Form 𝓘(ℝ,E) P r
  | 0, _ => ofFunction (fun _ ↦ 1)
  | r+1, θ => wedge (oneFormProduct r (fun i ↦ θ i.castSucc)) (θ (Fin.last r))

/-- Ordered exterior product of genuine two-forms, with explicit degree
transport after each multiplication. -/
def twoFormProduct : (k : ℕ) → (Fin k → Form 𝓘(ℝ,E) P 2) → Form 𝓘(ℝ,E) P (2*k)
  | 0, _ => ofFunction (fun _ ↦ 1)
  | k+1, Ω => degreeCastForm (show 2*k+2 = 2*(k+1) by omega)
      (wedge (twoFormProduct k (fun i ↦ Ω i.castSucc)) (Ω (Fin.last k)))

/-- Index of a one-form factor after the leading unit coordinate. -/
def directionIndex {n : ℕ} (k : Fin n) (i : Fin (2*n-2*k.val-1)) : Fin (2*n) :=
  ⟨i.val+1, by have := i.isLt; have := k.isLt; omega⟩

/-- First frame index of a curvature factor in Chern's `Φ_k`. -/
def curvatureIndexFirst {n : ℕ} (k : Fin n) (j : Fin k.val) : Fin (2*n) :=
  ⟨2*n-2*k.val+2*j.val, by have := j.isLt; have := k.isLt; omega⟩

/-- Second frame index of a curvature factor in Chern's `Φ_k`. -/
def curvatureIndexSecond {n : ℕ} (k : Fin n) (j : Fin k.val) : Fin (2*n) :=
  ⟨2*n-2*k.val+2*j.val+1, by have := j.isLt; have := k.isLt; omega⟩

/-- Chern's unnormalized alternating polynomial `Φ_k`, interpreted in the
actual scalar differential forms and actual exterior product. The supplied
`u`, `θ`, and `Ω` are local coefficient/form data, not proof assumptions. -/
def angularTerm (n : ℕ) (k : Fin n)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (Ω : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2) :
    Form 𝓘(ℝ,E) P (2*n-1) :=
  ∑ σ : Equiv.Perm (Fin (2*n)), (↑(Equiv.Perm.sign σ) : ℝ) •
    (fun x ↦ u (σ ⟨0, by have := k.isLt; omega⟩) x •
      degreeCastForm (show (2*n-2*k.val-1)+2*k.val = 2*n-1 by
        have := k.isLt; omega)
        (wedge
          (oneFormProduct (2*n-2*k.val-1) (fun i ↦ θ (σ (directionIndex k i))))
          (twoFormProduct k.val (fun j ↦ Ω (σ (curvatureIndexFirst k j))
            (σ (curvatureIndexSecond k j))))) x)

/-- The actual local angular-form polynomial, with the positive coefficient
convention dictated by the project's genuine curvature matrix. Proving the
connection structure equations and gluing is separate from this definition. -/
def angularForm (n : ℕ)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (Ω : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2) :
    Form 𝓘(ℝ,E) P (2*n-1) :=
  ∑ k : Fin n, angularCoefficient n k.val • angularTerm n k u θ Ω

private theorem wedge_zero_right {r s : ℕ} (α : Form 𝓘(ℝ,E) P r) :
    wedge α (0 : Form 𝓘(ℝ,E) P s) = 0 := by
  funext x
  ext v
  simp [wedge, wedgeFiber_apply]

private theorem degreeCastForm_zero {r s : ℕ} (h : r = s) :
    degreeCastForm (M := P) (E := E) h (0 : Form 𝓘(ℝ,E) P r) = 0 := by
  subst s
  rfl

/-- Every positive-curvature-degree product vanishes when its curvature
forms vanish. This proves the algebraic part of the fiber restriction. -/
theorem twoFormProduct_zero (k : ℕ) (hk : 0 < k) :
    twoFormProduct (E := E) (P := P) k (fun _ ↦ 0) = 0 := by
  cases k with
  | zero => omega
  | succ k => simp only [twoFormProduct, wedge_zero_right, degreeCastForm_zero]

theorem angularTerm_zero_curvature (n : ℕ) (k : Fin n) (hk : 0 < k.val)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1) :
    angularTerm n k u θ (fun _ _ ↦ 0) = 0 := by
  simp only [angularTerm, twoFormProduct_zero k.val hk, wedge_zero_right,
    degreeCastForm_zero]
  apply Finset.sum_eq_zero
  intro σ _
  simp only [Pi.zero_apply, smul_zero]
  change (↑(Equiv.Perm.sign σ) : ℝ) • (0 : Form 𝓘(ℝ,E) P (2*n-1)) = 0
  exact smul_zero _

/-- With vanishing curvature (in particular after a fiber pullback, once
that pullback is established), exactly the zero-curvature term remains. -/
theorem angularForm_zero_curvature (n : ℕ) (hn : 0 < n)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1) :
    angularForm n u θ (fun _ _ ↦ 0) = angularCoefficient n 0 •
      angularTerm n ⟨0, hn⟩ u θ (fun _ _ ↦ 0) := by
  classical
  let F : Fin n → Form 𝓘(ℝ,E) P (2*n-1) := fun k ↦
    angularCoefficient n k.val • angularTerm n k u θ (fun _ _ ↦ 0)
  change (∑ k : Fin n, F k) = F ⟨0, hn⟩
  apply Finset.sum_eq_single (f := F) ⟨0, hn⟩
  · intro k _ hk
    have hk0 : 0 < k.val := by
      by_contra hc
      have : k = (⟨0, hn⟩ : Fin n) := Fin.ext (show k.val = 0 by omega)
      exact hk this
    change angularCoefficient n k.val • angularTerm n k u θ (fun _ _ ↦ 0) = 0
    rw [angularTerm_zero_curvature n k hk0, smul_zero]
  · simp

end ActualForms

end Chern
end GaussBonnetChern
