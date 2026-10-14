import GaussBonnetChern.Pfaffian

/-! # Pfaffian algebra in arbitrary positive even dimension

This module supplies actual polynomial identities used by the Euler form.
The parameter `n` is symbolic throughout. The skew-symmetry of a curvature
matrix will be supplied later by the geometric curvature lemmas.
-/

noncomputable section

namespace GaussBonnetChern

open scoped BigOperators

/-- Full alternating pair sum, before division by the Pfaffian denominator. -/
def pfaffianSum {A : Type*} [CommRing A] (n : ℕ)
    (B : Matrix (Fin (2 * n)) (Fin (2 * n)) A) : A :=
  ∑ σ : Equiv.Perm (Fin (2 * n)),
    (↑(Equiv.Perm.sign σ) : A) *
      ∏ k : Fin n, B (σ (pairFirst k)) (σ (pairSecond k))

/-- The normalized real Pfaffian, from the standard permutation polynomial. -/
def pfaffian (n : ℕ) (B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : ℝ :=
  pfaffianSum n B / (2 ^ n * (Nat.factorial n : ℝ))

theorem pfaffianSum_mul {A : Type*} [CommRing A] (n : ℕ) (c : A)
    (B : Matrix (Fin (2 * n)) (Fin (2 * n)) A) :
    pfaffianSum n (fun i j ↦ c * B i j) = c ^ n * pfaffianSum n B := by
  classical
  simp only [pfaffianSum, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem pfaffian_mul (n : ℕ) (c : ℝ)
    (B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) :
    pfaffian n (fun i j ↦ c * B i j) = c ^ n * pfaffian n B := by
  simp only [pfaffian]
  rw [pfaffianSum_mul]
  ring

/-- Scaling every curvature component multiplies the double contraction by
`c^n`; this is the homogeneity needed for the `(2π)^n` normalization. -/
theorem curvatureContraction_mul {A : Type*} [CommRing A] (n : ℕ) (c : A)
    (B : Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → A) :
    curvatureContraction n (fun a b i j ↦ c * B a b i j) =
      c ^ n * curvatureContraction n B := by
  classical
  simp only [curvatureContraction, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem eulerScalar_mul (n : ℕ) (c : ℝ)
    (B : Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → ℝ) :
    eulerScalar n (fun a b i j ↦ c * B a b i j) = c ^ n * eulerScalar n B := by
  rw [eulerScalar, curvatureContraction_mul, eulerScalar]
  ring

/-- Sign squared is one, including after casting into any commutative ring. -/
theorem cast_sign_mul_self {A : Type*} [CommRing A] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    (↑(Equiv.Perm.sign σ) : A) * (↑(Equiv.Perm.sign σ) : A) = 1 := by
  have h := congrArg (fun u : ℤˣ ↦ ((u : ℤ) : A))
    (Int.units_mul_self (Equiv.Perm.sign σ))
  simpa only [Units.val_mul, Units.val_one, Int.cast_mul, Int.cast_one] using h

/-- Relabeling the two matrix indices changes the Pfaffian by the sign of the
relabeling. This is an initial part of the full congruence transformation law. -/
theorem pfaffianSum_reindex {A : Type*} [CommRing A] (n : ℕ)
    (ρ : Equiv.Perm (Fin (2 * n)))
    (B : Matrix (Fin (2 * n)) (Fin (2 * n)) A) :
    pfaffianSum n (fun i j ↦ B (ρ i) (ρ j)) =
      (↑(Equiv.Perm.sign ρ) : A) * pfaffianSum n B := by
  classical
  let f := fun σ : Equiv.Perm (Fin (2 * n)) ↦
    (↑(Equiv.Perm.sign σ) : A) * ∏ k : Fin n, B (σ (pairFirst k)) (σ (pairSecond k))
  calc
    pfaffianSum n (fun i j ↦ B (ρ i) (ρ j)) =
        ∑ σ, (↑(Equiv.Perm.sign ρ) : A) * f (ρ * σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      dsimp [f]
      simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
      rw [← mul_assoc, ← mul_assoc, cast_sign_mul_self, one_mul]
    _ = (↑(Equiv.Perm.sign ρ) : A) * ∑ σ, f (ρ * σ) := by rw [Finset.mul_sum]
    _ = (↑(Equiv.Perm.sign ρ) : A) * ∑ σ, f σ := by
      congr 1
      exact Fintype.sum_equiv (Equiv.mulLeft ρ) (fun σ ↦ f (ρ * σ)) f (fun _ ↦ rfl)
    _ = (↑(Equiv.Perm.sign ρ) : A) * pfaffianSum n B := rfl

theorem pfaffian_reindex (n : ℕ) (ρ : Equiv.Perm (Fin (2 * n)))
    (B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) :
    pfaffian n (fun i j ↦ B (ρ i) (ρ j)) =
      (↑(Equiv.Perm.sign ρ) : ℝ) * pfaffian n B := by
  simp only [pfaffian]
  rw [pfaffianSum_reindex]
  ring

end GaussBonnetChern
