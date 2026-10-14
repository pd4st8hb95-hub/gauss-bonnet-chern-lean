import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! # Explicit Pfaffian normalization

`curvatureContraction` is the double alternating sum of the curvature components.
The first factor `2^n * n!` is the Pfaffian normalization, and the second `2^n`
is the normalization of the wedge product of `n` two-forms. Division by `(2π)^n`
then gives the Euler scalar. The curvature convention used later is
`R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`, with
`B a b i j = ⟪R(e_i,e_j)e_b, e_a⟫`.
-/

namespace GaussBonnetChern

/-- The first index of the `k`th pair in `Fin (2*n)`. -/
def pairFirst {n : ℕ} (k : Fin n) : Fin (2 * n) := ⟨2 * k.val, by omega⟩

/-- The second index of the `k`th pair in `Fin (2*n)`. -/
def pairSecond {n : ℕ} (k : Fin n) : Fin (2 * n) := ⟨2 * k.val + 1, by omega⟩

/-- The unnormalized double alternating curvature contraction. -/
def curvatureContraction {A : Type*} [CommRing A] (n : ℕ)
    (B : Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → A) : A :=
  ∑ σ : Equiv.Perm (Fin (2 * n)), ∑ τ : Equiv.Perm (Fin (2 * n)),
    (↑(Equiv.Perm.sign σ) : A) * (↑(Equiv.Perm.sign τ) : A) *
      ∏ k : Fin n, B (σ (pairFirst k)) (σ (pairSecond k))
        (τ (pairFirst k)) (τ (pairSecond k))

/-- The scalar multiplying the positive Riemannian volume density. -/
noncomputable def eulerScalar (n : ℕ)
    (B : Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → ℝ) : ℝ :=
  curvatureContraction n B / (4 ^ n * (Nat.factorial n : ℝ) * (2 * Real.pi) ^ n)

end GaussBonnetChern
