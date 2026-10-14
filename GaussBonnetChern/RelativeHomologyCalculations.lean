import GaussBonnetChern.BasicHomology

/-! # Relative homology calculations for contractible ambient spaces

The degree-one group is handled as the kernel of the augmentation on H₀ of
the subspace. This keeps the two-point boundary case and the empty boundary
case separate from positive-degree dimension shifting.
-/

noncomputable section

universe u

namespace GaussBonnetChern

open CategoryTheory CategoryTheory.Limits

variable (X : Type u) [TopologicalSpace X] (A : Set X)

theorem relativeSingularHomologyConnectingZero_mono [ContractibleSpace X] :
    Mono (relativeSingularHomologyConnecting X A 0) :=
  (relativeSingularHomology_exact_at_relative X A 0).mono_g
    ((singularHomology_isZero_of_contractible X 1 (by decide)).eq_zero_of_src _)

/-- Finite-dimensionality of H₁(X,A) follows from an actual injection into
the finite-dimensional H₀(A), without any assumption that A is connected. -/
theorem relativeSingularHomologyOne_finiteDimensional [ContractibleSpace X]
    [FiniteDimensional ℝ (singularHomology A 0)] :
    FiniteDimensional ℝ (relativeSingularHomology X A 1) := by
  letI := relativeSingularHomologyConnectingZero_mono X A
  exact FiniteDimensional.of_injective (relativeSingularHomologyConnecting X A 0).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- For a nonempty subspace of a contractible space, H₁(X,A) has dimension
one less than H₀(A). The equality is in naturals and retains the degree-zero
augmentation rather than assigning H₁(X,A) the unreduced H₀(A). -/
theorem relativeSingularHomologyOne_finrank [ContractibleSpace X]
    (hne : A.Nonempty) [FiniteDimensional ℝ (singularHomology A 0)] :
    Module.finrank ℝ (relativeSingularHomology X A 1) + 1 =
      Module.finrank ℝ (singularHomology A 0) := by
  letI := singularHomologyZero_finiteDimensional X
  letI := relativeSingularHomologyOne_finiteDimensional X A
  letI := relativeSingularHomologyConnectingZero_mono X A
  letI := ModuleCat.subsingleton_of_isZero
    (relativeSingularHomologyZero_isZero_of_contractible X A hne)
  have hr := relativeSingularHomology_finrank_balance_zero X A
  have hi := (ModuleCat.mono_iff_injective (relativeSingularHomologyConnecting X A 0)).mp
    inferInstance
  rw [singularHomologyZero_finrank X,
    LinearMap.finrank_range_of_inj hi,
    Module.finrank_eq_zero_of_subsingleton ℝ (relativeSingularHomology X A 0),
    add_zero] at hr
  simpa only [Nat.zero_add, add_comm] using hr

/-- Relative homology against an empty subspace is actual absolute homology. -/
theorem singularHomologyToRelative_isIso_of_isEmpty [IsEmpty A] (k : ℕ) :
    IsIso (singularHomologyToRelative X A k) := by
  letI : Mono (singularHomologyToRelative X A k) :=
    (relativeSingularHomology_exact_at_space X A k).mono_g
      ((singularHomology_isZero_of_isEmpty A k).eq_zero_of_src _)
  haveI : Epi (singularHomologyToRelative X A k) := by
    cases k with
    | zero => infer_instance
    | succ k =>
        exact (relativeSingularHomology_exact_at_relative X A k).epi_f
          ((singularHomology_isZero_of_isEmpty A k).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

def singularHomologyIsoRelativeOfIsEmpty [IsEmpty A] (k : ℕ) :
    singularHomology X k ≅ relativeSingularHomology X A k := by
  letI := singularHomologyToRelative_isIso_of_isEmpty X A k
  exact asIso (singularHomologyToRelative X A k)

/-- A nonempty pair with contractible ambient space has finite homology
whenever the subspace does, including degrees zero and one. -/
theorem relativeSingularHomology_finiteDimensional_all_of_contractible
    [ContractibleSpace X] (hne : A.Nonempty)
    [∀ k, FiniteDimensional ℝ (singularHomology A k)] (k : ℕ) :
    FiniteDimensional ℝ (relativeSingularHomology X A k) := by
  rcases k with _ | _ | k
  · letI := ModuleCat.subsingleton_of_isZero
      (relativeSingularHomologyZero_isZero_of_contractible X A hne)
    infer_instance
  · exact relativeSingularHomologyOne_finiteDimensional X A
  · exact relativeSingularHomology_finiteDimensional_of_contractible X A (k + 1) (by omega)

/-- An actual vanishing bound shifts by one in a contractible pair. -/
theorem relativeSingularHomology_isZero_above_of_contractible
    [ContractibleSpace X] (N : ℕ)
    (hA : ∀ k, N < k → IsZero (singularHomology A k))
    (k : ℕ) (hk : N + 1 < k) : IsZero (relativeSingularHomology X A k) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  exact (hA l (by omega)).of_iso
    (relativeSingularHomologyIsoOfContractible X A l (by omega))

end GaussBonnetChern
