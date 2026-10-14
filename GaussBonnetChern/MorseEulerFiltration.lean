import GaussBonnetChern.HandleHomology
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Order.Compact

/-! # Finite singular-homology filtrations and critical-value bookkeeping

Every stage is an actual subspace, and each transition consumes an actual
relative singular-homology comparison. These comparisons are geometric
obligations; this file does not postulate a Morse attachment theorem.
Repeated critical values are grouped into their full finite fibers.
-/

noncomputable section
universe u
namespace GaussBonnetChern
open CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators

/-- Finite-dimensional actual homology with a genuine common zero bound. -/
structure FiniteSingularHomologyBound (X : Type u) [TopologicalSpace X] (N : ℕ) : Prop where
  finite : ∀ k, FiniteDimensional ℝ (singularHomology X k)
  vanishing : ∀ k, N < k → IsZero (singularHomology X k)

theorem FiniteSingularHomologyBound.of_homeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {N : ℕ}
    (h : FiniteSingularHomologyBound Y N) (e : X ≃ₜ Y) :
    FiniteSingularHomologyBound X N := by
  refine ⟨fun k ↦ ?_, fun k hk ↦ (h.vanishing k hk).of_iso
    (singularHomologyIsoOfHomeomorph e k)⟩
  letI := h.finite k
  exact (singularHomologyIsoOfHomeomorph e k).toLinearEquiv.symm.finiteDimensional

theorem topologicalEulerCharacteristic_eq_of_homeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    topologicalEulerCharacteristic X = topologicalEulerCharacteristic Y := by
  unfold topologicalEulerCharacteristic HomologicalComplex.homologyEulerChar GradedObject.eulerChar
  apply finsum_congr
  intro k
  rw [(singularHomologyIsoOfHomeomorph e k).toLinearEquiv.finrank_eq]

/-- The lower stage as a subset of the next stage. -/
def nestedPairSubset {M : Type u} (A B : Set M) : Set B := {x | x.val ∈ A}

def nestedPairSubsetHomeomorph {M : Type u} [TopologicalSpace M]
    {A B : Set M} (h : A ⊆ B) : nestedPairSubset A B ≃ₜ A where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

section Step
variable {M : Type u} [TopologicalSpace M] {ι : Type u} [Fintype ι]
  (E : ι → Type u) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

theorem finiteNestedPair_step {A B : Set M} (hAB : A ⊆ B)
    (e : ∀ k, relativeSingularHomology B (nestedPairSubset A B) k ≅ diskHandleHomology E k)
    (N : ℕ) (hN : ∀ i, finrank ℝ (E i) ≤ N)
    (hA : FiniteSingularHomologyBound A N) :
    FiniteSingularHomologyBound B N ∧
      topologicalEulerCharacteristic B =
        topologicalEulerCharacteristic A + ∑ i, (-1 : ℤ) ^ finrank ℝ (E i) := by
  have hS := hA.of_homeomorph (nestedPairSubsetHomeomorph hAB)
  letI := hS.finite
  obtain ⟨hf, hz, he⟩ := finiteHomology_step_of_relative_comparison E B
    (nestedPairSubset A B) e N hN hS.vanishing
  refine ⟨⟨hf, hz⟩, ?_⟩
  rw [he, topologicalEulerCharacteristic_eq_of_homeomorph (nestedPairSubsetHomeomorph hAB)]
end Step

section Filtration
variable {M : Type u} [TopologicalSpace M]
  (ι : ℕ → Type u) [∀ j, Fintype (ι j)]
  (E : ∀ j, ι j → Type u)
  [∀ j i, NormedAddCommGroup (E j i)] [∀ j i, InnerProductSpace ℝ (E j i)]
  [∀ j i, FiniteDimensional ℝ (E j i)]

/-- A finite filtration from the empty subspace to the whole space, with
proved relative comparisons, propagates genuine finite homology and telescopes
the independently defined Euler characteristic. -/
theorem finiteFiltration_homology_and_euler
    (S : ℕ → Set M) (r N : ℕ) (hstart : S 0 = ∅) (hend : S r = Set.univ)
    (hmono : ∀ j, j < r → S j ⊆ S (j + 1))
    (hN : ∀ j, j < r → ∀ i, finrank ℝ (E j i) ≤ N)
    (e : ∀ j, j < r → ∀ k,
      relativeSingularHomology (S (j + 1)) (nestedPairSubset (S j) (S (j + 1))) k ≅
        diskHandleHomology (E j) k) :
    FiniteSingularHomologyBound M N ∧
      topologicalEulerCharacteristic M =
        ∑ j ∈ Finset.range r, ∑ i, (-1 : ℤ) ^ finrank ℝ (E j i) := by
  have hstage : ∀ j, j ≤ r → FiniteSingularHomologyBound (S j) N ∧
      topologicalEulerCharacteristic (S j) =
        ∑ l ∈ Finset.range j, ∑ i, (-1 : ℤ) ^ finrank ℝ (E l i) := by
    intro j
    induction j with
    | zero =>
        intro hj
        letI : IsEmpty (S 0) := ⟨fun x ↦ by
          exact Set.notMem_empty x.val
            ((congrArg (fun s : Set M ↦ x.val ∈ s) hstart).mp x.property)⟩
        exact ⟨⟨singularHomology_finiteDimensional_of_isEmpty _,
          fun k _ ↦ singularHomology_isZero_of_isEmpty _ k⟩,
          by simp [topologicalEulerCharacteristic_of_isEmpty]⟩
    | succ j ih =>
        intro hj
        have hjr : j < r := by omega
        obtain ⟨hf, he⟩ := ih (by omega)
        obtain ⟨hf', he'⟩ := finiteNestedPair_step (E j) (hmono j hjr)
          (e j hjr) N (hN j hjr) hf
        refine ⟨hf', ?_⟩
        rw [he', he, Finset.sum_range_succ]
  obtain ⟨hf, he⟩ := hstage r le_rfl
  let a : S r ≃ₜ M := {
    toFun := Subtype.val
    invFun := fun x ↦ ⟨x, by rw [hend]; trivial⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by fun_prop }
  exact ⟨hf.of_homeomorph a.symm,
    (topologicalEulerCharacteristic_eq_of_homeomorph a).symm.trans he⟩
end Filtration

section CriticalValues
variable {M : Type u} (f : M → ℝ) {C : Set M} (hC : C.Finite)

/-- Values of the actual finite critical-point set supplied by a Morse theorem.
The image finset intentionally merges repeated values without dropping points. -/
def finiteCriticalValues : Finset ℝ := by
  classical
  exact hC.toFinset.image f

@[simp]
theorem mem_finiteCriticalValues (c : ℝ) :
    c ∈ finiteCriticalValues f hC ↔ ∃ p ∈ C, f p = c := by
  classical
  simp [finiteCriticalValues]

/-- Increasing enumeration of the distinct critical values. -/
def orderedCriticalValues : Fin (finiteCriticalValues f hC).card ↪o ℝ :=
  (finiteCriticalValues f hC).orderEmbOfFin rfl

theorem orderedCriticalValues_range :
    Set.range (orderedCriticalValues f hC) = f '' C := by
  rw [orderedCriticalValues, Finset.range_orderEmbOfFin]
  ext c
  simp [mem_finiteCriticalValues]

/-- Grouping all point contributions by their actual common value loses no
multiplicity, including the empty critical set. -/
theorem criticalValue_fiber_sum (w : M → ℤ) :
    (∑ c ∈ finiteCriticalValues f hC, ∑ p ∈ hC.toFinset with f p = c, w p) =
      ∑ p ∈ hC.toFinset, w p := by
  classical
  exact Finset.sum_fiberwise_of_maps_to
    (fun p hp ↦ Finset.mem_image.mpr ⟨p, hp, rfl⟩) w

include hC in
/-- A finite set of critical values isolates the entire fiber at one value;
it does not select just one critical point in that fiber. -/
theorem exists_isolating_critical_value_band (c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ C, f p ∈ Set.Icc (c - ε) (c + ε) → f p = c := by
  classical
  let S : Set ℝ := (finiteCriticalValues f hC : Set ℝ) \ {c}
  have hS : IsClosed S := ((finiteCriticalValues f hC).finite_toSet.sdiff (t := {c})).isClosed
  have hc : c ∈ Sᶜ := by simp [S]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hS.isOpen_compl.mem_nhds hc)
  refine ⟨r / 2, by positivity, ?_⟩
  intro p hp hpc
  by_contra hne
  have hdist : dist (f p) c < r := by
    rw [Real.dist_eq]
    have ha : |f p - c| ≤ r / 2 := abs_le.mpr ⟨by linarith [hpc.1], by linarith [hpc.2]⟩
    linarith
  exact hball hdist ⟨(mem_finiteCriticalValues f hC (f p)).mpr ⟨p, hp, rfl⟩, hne⟩
end CriticalValues

/-- Compactness supplies actual initial empty and final full sublevels;
nonemptiness or connectedness is not assumed. -/
theorem exists_empty_full_sublevels {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {f : M → ℝ} (hf : Continuous f) :
    ∃ a b : ℝ, a < b ∧ {x : M | f x ≤ a} = ∅ ∧ {x : M | f x ≤ b} = Set.univ := by
  obtain ⟨a, ha⟩ := (isCompact_range hf).bddBelow
  obtain ⟨b, hb⟩ := (isCompact_range hf).bddAbove
  refine ⟨min a b - 1, max a b + 1, ?_, ?_, ?_⟩
  · have : min a b ≤ max a b := min_le_max
    linarith
  · ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    have hx := ha (Set.mem_range_self x)
    have := min_le_left a b
    linarith
  · ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hx := hb (Set.mem_range_self x)
    have := le_max_right a b
    linarith

end GaussBonnetChern
