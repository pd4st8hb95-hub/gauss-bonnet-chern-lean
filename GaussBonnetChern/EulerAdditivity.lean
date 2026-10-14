import GaussBonnetChern.RelativeHomology
import Mathlib.Tactic.LinearCombination

/-! # Euler additivity for an actual topological pair

The result in this file has explicit finite-dimensionality and common vanishing
bound hypotheses on the three singular homologies. Establishing those hypotheses
for the manifold sublevel pairs remains part of the future Morse-theory work.
They are not additional hypotheses on the Gauss--Bonnet--Chern statement.

The proof replaces each homological `finsum` by a supported finite sum and then
uses the relative long exact sequence. No value of an infinite-support `finsum`
or infinite-dimensional `finrank` is used to obtain additivity.
-/

noncomputable section

universe u

namespace GaussBonnetChern

open CategoryTheory
open scoped BigOperators

/-- Euler characteristic computed from actual relative singular homology. -/
def relativeEulerCharacteristic (X : Type u) [TopologicalSpace X] (A : Set X) : ℤ :=
  (relativeSingularChains X A).homologyEulerChar

/-- Vanishing above `N` places the homological rank support inside `range (N+1)`.
This support statement alone does not assert finite-dimensionality. -/
theorem homology_finrankSupport_subset_range
    (C : ChainComplex (ModuleCat.{u} ℝ) ℕ) (N : ℕ)
    (hvanish : ∀ k, N < k → Subsingleton (C.homology k)) :
    GradedObject.finrankSupport (fun k ↦ C.homology k) ⊆ Finset.range (N + 1) := by
  intro k hk
  change Module.finrank ℝ (C.homology k) ≠ 0 at hk
  apply Finset.mem_range.mpr
  by_contra hn
  have hNk : N < k := by omega
  let := hvanish k hNk
  exact hk (Module.finrank_eq_zero_of_subsingleton ℝ (C.homology k))

/-- The homological Euler characteristic is a finite alternating rank sum when
the homology vanishes above a specified degree. -/
theorem homologyEulerChar_eq_sum_range_of_vanishing
    (C : ChainComplex (ModuleCat.{u} ℝ) ℕ) (N : ℕ)
    (hvanish : ∀ k, N < k → Subsingleton (C.homology k)) :
    C.homologyEulerChar =
      ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (Module.finrank ℝ (C.homology k) : ℤ) := by
  simpa [ComplexShape.χ, ComplexShape.eulerCharSignsDownNat] using
    C.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset (Finset.range (N + 1))
      (homology_finrankSupport_subset_range C N hvanish)

/-- Finite alternating summation of the relative rank-balance identities.
The final connecting-map term is kept until a vanishing bound eliminates it. -/
private theorem alternating_sum_rank_balance
    (a x r d : ℕ → ℤ)
    (hzero : x 0 + d 0 = a 0 + r 0)
    (hsucc : ∀ k, x (k + 1) + d (k + 1) + d k = a (k + 1) + r (k + 1))
    (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * x k) + (-1 : ℤ) ^ N * d N =
      (∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * a k) +
        ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * r k := by
  induction N with
  | zero => simpa using hzero
  | succ N ih =>
      simp only [Finset.sum_range_succ, pow_succ] at ih ⊢
      have hs := hsucc N
      linear_combination ih - (-1 : ℤ) ^ N * hs

variable (X : Type u) [TopologicalSpace X] (A : Set X)

/-- A common vanishing bound eliminates the last connecting-map rank. -/
theorem relativeConnecting_finrank_range_eq_zero (N : ℕ)
    (hvanish : ∀ k, N < k → Subsingleton (relativeSingularHomology X A k)) :
    Module.finrank ℝ (LinearMap.range (relativeSingularHomologyConnecting X A N).hom) = 0 := by
  let := hvanish (N + 1) (Nat.lt_succ_self N)
  have hz : (relativeSingularHomologyConnecting X A N).hom = 0 := by
    ext z
    have hz : z = 0 := Subsingleton.elim _ _
    rw [hz, map_zero]
    rfl
  simp [hz]

/-- Additivity of the independently defined singular-homological Euler
characteristic for `(X,A)`, under explicit finite-dimensionality and common
vanishing-bound hypotheses. These hypotheses must be proved for later
geometric applications; this theorem does not assert them for manifolds. -/
theorem topologicalEulerCharacteristic_additive (N : ℕ)
    [∀ k, FiniteDimensional ℝ (singularHomology X k)]
    [∀ k, FiniteDimensional ℝ (singularHomology A k)]
    [∀ k, FiniteDimensional ℝ (relativeSingularHomology X A k)]
    (hX : ∀ k, N < k → Subsingleton (singularHomology X k))
    (hA : ∀ k, N < k → Subsingleton (singularHomology A k))
    (hR : ∀ k, N < k → Subsingleton (relativeSingularHomology X A k)) :
    topologicalEulerCharacteristic X =
      topologicalEulerCharacteristic A + relativeEulerCharacteristic X A := by
  rw [topologicalEulerCharacteristic, topologicalEulerCharacteristic,
    relativeEulerCharacteristic,
    homologyEulerChar_eq_sum_range_of_vanishing (singularChains X) N hX,
    homologyEulerChar_eq_sum_range_of_vanishing (singularChains A) N hA,
    homologyEulerChar_eq_sum_range_of_vanishing (relativeSingularChains X A) N hR]
  have hzero :
      (Module.finrank ℝ (singularHomology X 0) : ℤ) +
          (Module.finrank ℝ (LinearMap.range (relativeSingularHomologyConnecting X A 0).hom) : ℤ) =
        (Module.finrank ℝ (singularHomology A 0) : ℤ) +
          (Module.finrank ℝ (relativeSingularHomology X A 0) : ℤ) := by
    simpa only [Nat.cast_add] using congrArg (fun t : ℕ ↦ (t : ℤ))
      (relativeSingularHomology_finrank_balance_zero X A)
  have hsucc : ∀ k,
      (Module.finrank ℝ (singularHomology X (k + 1)) : ℤ) +
          (Module.finrank ℝ
            (LinearMap.range (relativeSingularHomologyConnecting X A (k + 1)).hom) : ℤ) +
          (Module.finrank ℝ (LinearMap.range (relativeSingularHomologyConnecting X A k).hom) : ℤ) =
        (Module.finrank ℝ (singularHomology A (k + 1)) : ℤ) +
          (Module.finrank ℝ (relativeSingularHomology X A (k + 1)) : ℤ) := by
    intro k
    simpa only [Nat.cast_add] using congrArg (fun t : ℕ ↦ (t : ℤ))
      (relativeSingularHomology_finrank_balance X A k)
  have hsum := alternating_sum_rank_balance
    (fun k ↦ (Module.finrank ℝ (singularHomology A k) : ℤ))
    (fun k ↦ (Module.finrank ℝ (singularHomology X k) : ℤ))
    (fun k ↦ (Module.finrank ℝ (relativeSingularHomology X A k) : ℤ))
    (fun k ↦ (Module.finrank ℝ
      (LinearMap.range (relativeSingularHomologyConnecting X A k).hom) : ℤ)) hzero hsucc N
  simpa only [relativeConnecting_finrank_range_eq_zero X A N hR,
    Nat.cast_zero, mul_zero, add_zero] using hsum

end GaussBonnetChern
