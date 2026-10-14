import GaussBonnetChern.HomotopyInvariance
import GaussBonnetChern.EulerAdditivity
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex

/-! # Actual singular homology of empty and contractible spaces

We prove genuine zero-object statements, isomorphisms, and finite dimensionality
before evaluating `finrank` or the Euler characteristic. The coefficient object
remains `ULift.{u} ℝ`, precisely as in the frozen target.
-/

noncomputable section

universe u

namespace GaussBonnetChern

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap

variable (X : Type u) [TopologicalSpace X]

/-- In a path-connected space the actual augmentation induces the degree-zero
homology isomorphism to the real coefficient module. -/
def singularHomologyZeroIsoOfPathConnected [PathConnectedSpace X] :
    singularHomology X 0 ≅ realHomologyCoefficients.{u} := by
  letI : PathConnectedSpace (TopCat.of X) := ‹PathConnectedSpace X›
  change (TopCat.toSSet.obj (TopCat.of X)).homology realHomologyCoefficients.{u} 0 ≅
    realHomologyCoefficients.{u}
  exact asIso ((TopCat.toSSet.obj (TopCat.of X)).homology₀ε realHomologyCoefficients.{u})

theorem singularHomologyZero_finiteDimensional [PathConnectedSpace X] :
    FiniteDimensional ℝ (singularHomology X 0) :=
  (singularHomologyZeroIsoOfPathConnected X).toLinearEquiv.symm.finiteDimensional

theorem singularHomologyZero_finrank [PathConnectedSpace X] :
    Module.finrank ℝ (singularHomology X 0) = 1 := by
  rw [(singularHomologyZeroIsoOfPathConnected X).toLinearEquiv.finrank_eq]
  change Module.finrank ℝ (ULift.{u} ℝ) = 1
  simp

/-- Higher singular homology of a totally disconnected space vanishes. -/
theorem singularHomology_isZero_of_totallyDisconnected [TotallyDisconnectedSpace X]
    (k : ℕ) (hk : k ≠ 0) : IsZero (singularHomology X k) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{u} ℝ) k realHomologyCoefficients (TopCat.of X) hk

/-- Every degree of singular homology of an empty space is the zero object. -/
theorem singularHomology_isZero_of_isEmpty [IsEmpty X] (k : ℕ) :
    IsZero (singularHomology X k) := by
  by_cases hk : k = 0
  · subst k
    let e := AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
      (ModuleCat.{u} ℝ) realHomologyCoefficients (TopCat.of X)
    apply IsZero.of_iso (Y := ∐ fun _ : TopCat.of X ↦ realHomologyCoefficients.{u}) _ e
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Sigma.hom_ext
    intro x
    exact isEmptyElim x
  · exact singularHomology_isZero_of_totallyDisconnected X k hk

/-- Empty-space homology is finite dimensional in every degree. -/
theorem singularHomology_finiteDimensional_of_isEmpty [IsEmpty X] (k : ℕ) :
    FiniteDimensional ℝ (singularHomology X k) := by
  letI := ModuleCat.subsingleton_of_isZero (singularHomology_isZero_of_isEmpty X k)
  infer_instance

theorem singularHomology_finrank_of_isEmpty [IsEmpty X] (k : ℕ) :
    Module.finrank ℝ (singularHomology X k) = 0 := by
  letI := ModuleCat.subsingleton_of_isZero (singularHomology_isZero_of_isEmpty X k)
  exact Module.finrank_zero_of_subsingleton

/-- A contractible space is compared with a point in the same universe,
so no coefficient-universe change is hidden in the homology isomorphism. -/
def contractibleSingularHomologyIsoPoint [ContractibleSpace X] (k : ℕ) :
    singularHomology X k ≅ singularHomology (ULift.{u} Unit) k :=
  singularHomologyIsoOfHomotopyEquiv
    (Classical.choice (ContractibleSpace.hequiv X (ULift.{u} Unit))) k

/-- Higher homology of a contractible space is genuinely zero. -/
theorem singularHomology_isZero_of_contractible [ContractibleSpace X]
    (k : ℕ) (hk : k ≠ 0) : IsZero (singularHomology X k) :=
  (singularHomology_isZero_of_totallyDisconnected (ULift.{u} Unit) k hk).of_iso
    (contractibleSingularHomologyIsoPoint X k)

/-- All homology groups of a contractible space are finite dimensional. -/
theorem singularHomology_finiteDimensional_of_contractible [ContractibleSpace X] (k : ℕ) :
    FiniteDimensional ℝ (singularHomology X k) := by
  by_cases hk : k = 0
  · subst k
    exact singularHomologyZero_finiteDimensional X
  · letI := ModuleCat.subsingleton_of_isZero (singularHomology_isZero_of_contractible X k hk)
    infer_instance

theorem singularHomology_finrank_of_contractible [ContractibleSpace X] (k : ℕ) :
    Module.finrank ℝ (singularHomology X k) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst k
    exact singularHomologyZero_finrank X
  · letI := ModuleCat.subsingleton_of_isZero (singularHomology_isZero_of_contractible X k hk)
    exact Module.finrank_zero_of_subsingleton

/-- The empty-space Euler characteristic is computed only after actual
vanishing and finite-dimensionality have been proved above. -/
theorem topologicalEulerCharacteristic_of_isEmpty [IsEmpty X] :
    topologicalEulerCharacteristic X = 0 := by
  simp [topologicalEulerCharacteristic, HomologicalComplex.homologyEulerChar,
    GradedObject.eulerChar, singularHomology_finrank_of_isEmpty X]

/-- The contractible-space Euler characteristic uses the actual rank-one
degree-zero group and actual higher vanishing, hence a finite-support sum. -/
theorem topologicalEulerCharacteristic_of_contractible [ContractibleSpace X] :
    topologicalEulerCharacteristic X = 1 := by
  rw [topologicalEulerCharacteristic,
    homologyEulerChar_eq_sum_range_of_vanishing (singularChains X) 0
      (fun k hk ↦ ModuleCat.subsingleton_of_isZero
        (singularHomology_isZero_of_contractible X k (by omega)))]
  simp [singularHomologyZero_finrank X]

/-- In a contractible ambient space, the connecting homomorphism is an
isomorphism in every positive target degree. Degree zero is deliberately
excluded: it requires reduced homology and the augmentation. -/
theorem relativeSingularHomologyConnecting_isIso_of_contractible
    [ContractibleSpace X] (A : Set X) (k : ℕ) (hk : k ≠ 0) :
    IsIso (relativeSingularHomologyConnecting X A k) := by
  letI : Mono (relativeSingularHomologyConnecting X A k) :=
    (relativeSingularHomology_exact_at_relative X A k).mono_g
      ((singularHomology_isZero_of_contractible X (k + 1) (by omega)).eq_zero_of_src _)
  letI : Epi (relativeSingularHomologyConnecting X A k) :=
    (relativeSingularHomology_exact_at_subspace X A k).epi_f
      ((singularHomology_isZero_of_contractible X k hk).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- The actual relative homology dimension shift supplied by the LES. -/
def relativeSingularHomologyIsoOfContractible [ContractibleSpace X]
    (A : Set X) (k : ℕ) (hk : k ≠ 0) :
    relativeSingularHomology X A (k + 1) ≅ singularHomology A k := by
  letI := relativeSingularHomologyConnecting_isIso_of_contractible X A k hk
  exact asIso (relativeSingularHomologyConnecting X A k)

/-- Finiteness of the boundary group implies finiteness of the relative group
through this genuine connecting-map isomorphism. -/
theorem relativeSingularHomology_finiteDimensional_of_contractible
    [ContractibleSpace X] (A : Set X) (k : ℕ) (hk : k ≠ 0)
    [FiniteDimensional ℝ (singularHomology A k)] :
    FiniteDimensional ℝ (relativeSingularHomology X A (k + 1)) :=
  (relativeSingularHomologyIsoOfContractible X A k hk).toLinearEquiv.symm.finiteDimensional

section Convex

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Nonempty convex domains have the full contractible-space homology
calculation, not just a formal Euler value. -/
theorem convex_singularHomology (s : Set E) (hs : Convex ℝ s) (hne : s.Nonempty) :
    (∀ k, FiniteDimensional ℝ (singularHomology s k)) ∧
    (∀ k, k ≠ 0 → IsZero (singularHomology s k)) ∧
    Module.finrank ℝ (singularHomology s 0) = 1 := by
  letI := hs.contractibleSpace hne
  exact ⟨singularHomology_finiteDimensional_of_contractible s,
    singularHomology_isZero_of_contractible s, singularHomologyZero_finrank s⟩

/-- The actual closed disk is contractible for every nonnegative radius,
including the radius-zero point. -/
theorem closedBall_singularHomology (x : E) (r : ℝ) (hr : 0 ≤ r) :
    (∀ k, FiniteDimensional ℝ (singularHomology (Metric.closedBall x r) k)) ∧
    (∀ k, k ≠ 0 → IsZero (singularHomology (Metric.closedBall x r) k)) ∧
    Module.finrank ℝ (singularHomology (Metric.closedBall x r) 0) = 1 :=
  convex_singularHomology _ (convex_closedBall x r) ⟨x, by simpa using hr⟩

/-- The actual open ball calculation requires a positive radius, so the
empty radius-zero case cannot be silently assigned rank one. -/
theorem ball_singularHomology (x : E) (r : ℝ) (hr : 0 < r) :
    (∀ k, FiniteDimensional ℝ (singularHomology (Metric.ball x r) k)) ∧
    (∀ k, k ≠ 0 → IsZero (singularHomology (Metric.ball x r) k)) ∧
    Module.finrank ℝ (singularHomology (Metric.ball x r) 0) = 1 :=
  convex_singularHomology _ (convex_ball x r) ⟨x, by simpa using hr⟩

end Convex

theorem continuousMaps_homotopic_of_contractible
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace Y]
    (f g : C(X, Y)) : f.Homotopic g := by
  obtain ⟨p, H⟩ := id_nullhomotopic Y
  have hf : f.Homotopic (ContinuousMap.const X p) := by
    simpa using H.comp (ContinuousMap.Homotopic.refl f)
  have hg : g.Homotopic (ContinuousMap.const X p) := by
    simpa using H.comp (ContinuousMap.Homotopic.refl g)
  exact hf.trans hg.symm

variable (X : Type u) [TopologicalSpace X] (A : Set X)

theorem singularHomologyInclusion_eq_map (k : ℕ) :
    singularHomologyInclusion X A k = singularHomologyMap (subspaceInclusion X A).hom k := rfl

theorem singularHomologyInclusion_epi_of_contractible [ContractibleSpace X]
    (hne : A.Nonempty) (k : ℕ) : Epi (singularHomologyInclusion X A k) := by
  obtain ⟨a, ha⟩ := hne
  let c : C(X, A) := ContinuousMap.const X ⟨a, ha⟩
  have h : singularHomologyMap c k ≫ singularHomologyInclusion X A k = 𝟙 _ := by
    rw [singularHomologyInclusion_eq_map, ← singularHomologyMap_comp,
      singularHomologyMap_eq_of_homotopic
        (continuousMaps_homotopic_of_contractible _ (ContinuousMap.id X)),
      singularHomologyMap_id]
  exact epi_of_epi_fac h

theorem relativeSingularHomologyZero_isZero_of_contractible [ContractibleSpace X]
    (hne : A.Nonempty) : IsZero (relativeSingularHomology X A 0) := by
  letI := singularHomologyInclusion_epi_of_contractible X A hne 0
  have hz : singularHomologyToRelative X A 0 = 0 := by
    apply (cancel_epi (singularHomologyInclusion X A 0)).mp
    simpa using singularHomologyInclusion_comp_toRelative X A 0
  letI : Epi (0 : singularHomology X 0 ⟶ relativeSingularHomology X A 0) :=
    hz ▸ inferInstanceAs (Epi (singularHomologyToRelative X A 0))
  exact IsZero.of_epi_zero (singularHomology X 0) (relativeSingularHomology X A 0)

theorem singularHomologyInclusionZero_isIso_of_contractible [ContractibleSpace X]
    [PathConnectedSpace A] : IsIso (singularHomologyInclusion X A 0) := by
  letI := singularHomologyZero_finiteDimensional X
  letI := singularHomologyZero_finiteDimensional A
  letI := singularHomologyInclusion_epi_of_contractible X A
    (Set.nonempty_coe_sort.mp inferInstance) 0
  rw [ConcreteCategory.isIso_iff_bijective]
  have hs := (ModuleCat.epi_iff_surjective (singularHomologyInclusion X A 0)).mp inferInstance
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [singularHomologyZero_finrank A, singularHomologyZero_finrank X])).mpr hs, hs⟩

theorem relativeSingularHomologyOne_isZero_of_contractible [ContractibleSpace X]
    [PathConnectedSpace A] : IsZero (relativeSingularHomology X A 1) := by
  letI := singularHomologyInclusionZero_isIso_of_contractible X A
  letI : Mono (relativeSingularHomologyConnecting X A 0) :=
    (relativeSingularHomology_exact_at_relative X A 0).mono_g
      ((singularHomology_isZero_of_contractible X 1 (by decide)).eq_zero_of_src _)
  have hz : relativeSingularHomologyConnecting X A 0 = 0 := by
    apply (cancel_mono (singularHomologyInclusion X A 0)).mp
    simpa using relativeSingularHomologyConnecting_comp_inclusion X A 0
  letI : Mono (0 : relativeSingularHomology X A 1 ⟶ singularHomology A 0) :=
    hz ▸ inferInstanceAs (Mono (relativeSingularHomologyConnecting X A 0))
  exact IsZero.of_mono_zero (relativeSingularHomology X A 1) (singularHomology A 0)


def singularHomologyZeroIsoFinsupp [TotallyDisconnectedSpace X] :
    singularHomology X 0 ≅ ModuleCat.of ℝ (X →₀ ULift.{u} ℝ) :=
  AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
    (ModuleCat.{u} ℝ) realHomologyCoefficients (TopCat.of X) ≪≫
  (coproductIsCoproduct (fun _ : X ↦ realHomologyCoefficients.{u})).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℝ (ULift.{u} ℝ) X)

theorem singularHomology_finiteDimensional_of_finite_totallyDisconnected
    [Finite X] [TotallyDisconnectedSpace X] (k : ℕ) :
    FiniteDimensional ℝ (singularHomology X k) := by
  by_cases hk : k = 0
  · subst k
    exact (singularHomologyZeroIsoFinsupp X).toLinearEquiv.symm.finiteDimensional
  · letI := ModuleCat.subsingleton_of_isZero
      (singularHomology_isZero_of_totallyDisconnected X k hk)
    infer_instance

theorem singularHomologyZero_finrank_of_finite_totallyDisconnected
    [Fintype X] [TotallyDisconnectedSpace X] :
    Module.finrank ℝ (singularHomology X 0) = Fintype.card X := by
  rw [(singularHomologyZeroIsoFinsupp X).toLinearEquiv.finrank_eq]
  change Module.finrank ℝ (X →₀ ULift.{u} ℝ) = _
  simp [Module.finrank_finsupp]

theorem topologicalEulerCharacteristic_of_finite_totallyDisconnected
    [Fintype X] [TotallyDisconnectedSpace X] :
    topologicalEulerCharacteristic X = Fintype.card X := by
  rw [topologicalEulerCharacteristic,
    homologyEulerChar_eq_sum_range_of_vanishing (singularChains X) 0
      (fun k hk ↦ ModuleCat.subsingleton_of_isZero
        (singularHomology_isZero_of_totallyDisconnected X k (by omega)))]
  simp [singularHomologyZero_finrank_of_finite_totallyDisconnected X]


end GaussBonnetChern

