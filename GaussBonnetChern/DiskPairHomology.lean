import GaussBonnetChern.SphereHomology

/-! # The actual closed disk and its sphere boundary

The pair is a genuine subset inclusion in the closed unit ball. Dimension zero
has empty boundary; positive dimensions use the fully computed sphere groups.
-/

noncomputable section
universe u

namespace GaussBonnetChern

open CategoryTheory CategoryTheory.Limits Module Metric

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sphere boundary, regarded as an actual subset of the closed unit disk. -/
def unitDiskBoundarySubset : Set (Metric.closedBall (0 : E) 1) :=
  Subtype.val ⁻¹' Metric.sphere (0 : E) 1

/-- The subset boundary and the usual sphere have identical points and topology. -/
def unitDiskBoundaryHomeomorphSphere :
    unitDiskBoundarySubset E ≃ₜ Metric.sphere (0 : E) 1 where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, Metric.sphere_subset_closedBall x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem unitDisk_contractible : ContractibleSpace (Metric.closedBall (0 : E) 1) :=
  (convex_closedBall (0 : E) 1).contractibleSpace ⟨0, by simp⟩

variable [FiniteDimensional ℝ E]

theorem unitDiskBoundary_isEmpty_of_finrank_zero (hE : finrank ℝ E = 0) :
    IsEmpty (unitDiskBoundarySubset E) := by
  letI : Subsingleton E := Module.finrank_zero_iff.mp hE
  refine ⟨fun x ↦ ?_⟩
  have h := x.property
  change x.val.val ∈ Metric.sphere (0 : E) 1 at h
  have hx : x.val.val = 0 := Subsingleton.elim _ _
  simpa [hx] using h

/-- The real relative homology of a closed `n`-disk and its sphere boundary is
one-dimensional in degree `n` and zero in all other degrees. Finiteness is
proved explicitly; the `n = 0` empty-boundary case is included. -/
theorem unitDiskPair_homology_finite_and_finrank (n : ℕ) (hE : finrank ℝ E = n) (k : ℕ) :
    FiniteDimensional ℝ (relativeSingularHomology
      (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) k) ∧
    finrank ℝ (relativeSingularHomology
      (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) k) =
      if k = n then 1 else 0 := by
  letI := unitDisk_contractible E
  cases n with
  | zero =>
      letI := unitDiskBoundary_isEmpty_of_finrank_zero E hE
      let e := singularHomologyIsoRelativeOfIsEmpty
        (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) k
      letI := singularHomology_finiteDimensional_of_contractible
        (Metric.closedBall (0 : E) 1) k
      refine ⟨e.toLinearEquiv.finiteDimensional, ?_⟩
      rw [← e.toLinearEquiv.finrank_eq]
      exact singularHomology_finrank_of_contractible _ k
  | succ n =>
      letI : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
      have hs := unitSphere_homology_finite_and_finrank n E hE
      let e := fun k ↦ singularHomologyIsoOfHomeomorph (unitDiskBoundaryHomeomorphSphere E) k
      letI : ∀ k, FiniteDimensional ℝ (singularHomology (unitDiskBoundarySubset E) k) := by
        intro k
        letI := (hs k).1
        exact (e k).toLinearEquiv.symm.finiteDimensional
      obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).mpr (by norm_num)
      have hne : (unitDiskBoundarySubset E).Nonempty :=
        Set.nonempty_coe_sort.mp ⟨(unitDiskBoundaryHomeomorphSphere E).symm ⟨v, hv⟩⟩
      refine ⟨relativeSingularHomology_finiteDimensional_all_of_contractible
        (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) hne k, ?_⟩
      rcases k with _ | _ | k
      · letI := ModuleCat.subsingleton_of_isZero
          (relativeSingularHomologyZero_isZero_of_contractible
            (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) hne)
        simp [Module.finrank_zero_of_subsingleton]
      · have hr := relativeSingularHomologyOne_finrank
          (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) hne
        rw [(e 0).toLinearEquiv.finrank_eq, (hs 0).2] at hr
        by_cases hn : n = 0
        · subst n
          norm_num at hr ⊢
          omega
        · simp [hn] at hr
          have hneq : 1 ≠ n + 1 := by omega
          simp [hneq, hn]
          omega
      · let d := relativeSingularHomologyIsoOfContractible
          (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) (k + 1) (by omega)
        have hr := d.toLinearEquiv.finrank_eq.trans
          ((e (k + 1)).toLinearEquiv.finrank_eq.trans (hs (k + 1)).2)
        simpa only [Nat.succ_eq_add_one, show k + 1 ≠ 0 by omega, if_false,
          show (k + 1 + 1 = n + 1) ↔ (k + 1 = n) by omega] using hr

/-- The relative groups vanish away from the disk dimension as actual modules. -/
theorem unitDiskPair_homology_isZero (n : ℕ) (hE : finrank ℝ E = n)
    (k : ℕ) (hk : k ≠ n) :
    IsZero (relativeSingularHomology
      (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) k) := by
  have h := unitDiskPair_homology_finite_and_finrank E n hE k
  letI := h.1
  letI : Subsingleton (relativeSingularHomology
      (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) k) :=
    Module.finrank_zero_iff.mp (by simpa [hk] using h.2)
  exact ModuleCat.isZero_of_subsingleton _

/-- The actual relative Euler characteristic of `(Dⁿ,Sⁿ⁻¹)` is `(-1)^n`,
including `(D⁰,∅)`, after finite-dimensionality and support have been proved. -/
theorem unitDiskPair_relativeEulerCharacteristic (n : ℕ) (hE : finrank ℝ E = n) :
    relativeEulerCharacteristic
      (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) = (-1 : ℤ) ^ n := by
  rw [relativeEulerCharacteristic,
    homologyEulerChar_eq_sum_range_of_vanishing
      (relativeSingularChains (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E)) n
      (fun k hk ↦ ModuleCat.subsingleton_of_isZero
        (unitDiskPair_homology_isZero E n hE k (by omega)))]
  have hterm (k : ℕ) :
      (-1 : ℤ) ^ k * (finrank ℝ (relativeSingularHomology
        (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) k) : ℤ) =
        if k = n then (-1 : ℤ) ^ n else 0 := by
    rw [(unitDiskPair_homology_finite_and_finrank E n hE k).2]
    by_cases hkn : k = n
    · subst k
      simp
    · simp [hkn]
  simp_rw [hterm]
  simp

end GaussBonnetChern
