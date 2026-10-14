import GaussBonnetChern.SingularDisjointUnion
import GaussBonnetChern.DiskPairHomology
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Finite collections of handles and finite-homology propagation

The summands are the actual relative singular homology groups of closed disks
and their sphere boundaries. The index set is any finite type, so handles with
the same critical value are retained simultaneously. Geometric comparison of
a manifold sublevel pair with these summands is a separate construction.
-/

noncomputable section
universe u

namespace GaussBonnetChern

open CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators DirectSum

/-- An exact sequence with finite-dimensional outer terms has a
finite-dimensional middle term. Surjectivity onto the original third term
is not required: the proof restricts to the actual image of its incoming map. -/
theorem moduleShortComplex_finiteDimensional_middle
    (S : ShortComplex (ModuleCat.{u} ℝ)) (hS : S.Exact)
    [FiniteDimensional ℝ S.X₁] [FiniteDimensional ℝ S.X₃] :
    FiniteDimensional ℝ S.X₂ := by
  apply Module.Finite.of_exact (f := S.f.hom) (g := S.g.hom.rangeRestrict)
  · rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact hS.moduleCat_range_eq_ker.symm
  · exact S.g.hom.surjective_rangeRestrict

/-- Actual absolute singular-homology finiteness propagates through the LES
from a subspace and the relative group. -/
theorem singularHomology_finiteDimensional_of_subspace_relative
    (X : Type u) [TopologicalSpace X] (A : Set X) (k : ℕ)
    [FiniteDimensional ℝ (singularHomology A k)]
    [FiniteDimensional ℝ (relativeSingularHomology X A k)] :
    FiniteDimensional ℝ (singularHomology X k) :=
  moduleShortComplex_finiteDimensional_middle _
    (relativeSingularHomology_exact_at_space X A k)

/-- The same exact sequence propagates genuine vanishing of modules. -/
theorem singularHomology_isZero_of_subspace_relative
    (X : Type u) [TopologicalSpace X] (A : Set X) (k : ℕ)
    (hA : IsZero (singularHomology A k))
    (hR : IsZero (relativeSingularHomology X A k)) :
    IsZero (singularHomology X k) :=
  (relativeSingularHomology_exact_at_space X A k).isZero_X₂
    (hA.eq_zero_of_src _) (hR.eq_zero_of_tgt _)

section FiniteFamily

variable {ι : Type u} [Fintype ι] (E : ι → Type u)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

/-- The direct sum of the actual disk-boundary homology groups, allowing each
member of a simultaneous handle family to have a different dimension. -/
def diskHandleHomology (k : ℕ) : ModuleCat.{u} ℝ :=
  ModuleCat.of ℝ (⨁ i, relativeSingularHomology
    (Metric.closedBall (0 : E i) 1) (unitDiskBoundarySubset (E i)) k)

theorem diskHandleHomology_finiteDimensional (k : ℕ) :
    FiniteDimensional ℝ (diskHandleHomology E k) := by
  letI : ∀ i, FiniteDimensional ℝ (relativeSingularHomology
      (Metric.closedBall (0 : E i) 1) (unitDiskBoundarySubset (E i)) k) :=
    fun i ↦ (unitDiskPair_homology_finite_and_finrank (E i) (finrank ℝ (E i)) rfl k).1
  change FiniteDimensional ℝ (⨁ i, relativeSingularHomology
    (Metric.closedBall (0 : E i) 1) (unitDiskBoundarySubset (E i)) k)
  infer_instance

theorem diskHandleHomology_finrank (k : ℕ) :
    finrank ℝ (diskHandleHomology E k) = ∑ i, if k = finrank ℝ (E i) then 1 else 0 := by
  letI : ∀ i, FiniteDimensional ℝ (relativeSingularHomology
      (Metric.closedBall (0 : E i) 1) (unitDiskBoundarySubset (E i)) k) :=
    fun i ↦ (unitDiskPair_homology_finite_and_finrank (E i) (finrank ℝ (E i)) rfl k).1
  change finrank ℝ (⨁ i, relativeSingularHomology
    (Metric.closedBall (0 : E i) 1) (unitDiskBoundarySubset (E i)) k) = _
  rw [Module.finrank_directSum]
  apply Finset.sum_congr rfl
  intro i _
  exact (unitDiskPair_homology_finite_and_finrank (E i) (finrank ℝ (E i)) rfl k).2

theorem diskHandleHomology_isZero_above (N : ℕ) (hN : ∀ i, finrank ℝ (E i) ≤ N)
    (k : ℕ) (hk : N < k) : IsZero (diskHandleHomology E k) := by
  letI := diskHandleHomology_finiteDimensional E k
  letI : Subsingleton (diskHandleHomology E k) := Module.finrank_zero_iff.mp (by
    rw [diskHandleHomology_finrank]
    apply Finset.sum_eq_zero
    intro i _
    have hki : k ≠ finrank ℝ (E i) := by have := hN i; omega
    simp [hki])
  exact ModuleCat.isZero_of_subsingleton _

/-- The finite graded Euler sum for a simultaneous handle family. The actual
groups were proved finite dimensional and zero above the common bound first. -/
theorem diskHandleHomology_eulerChar (N : ℕ) (hN : ∀ i, finrank ℝ (E i) ≤ N) :
    GradedObject.eulerChar (ComplexShape.down ℕ) (diskHandleHomology E) =
      ∑ i, (-1 : ℤ) ^ finrank ℝ (E i) := by
  have hsupport : GradedObject.finrankSupport (diskHandleHomology E) ⊆
      Finset.range (N + 1) := by
    intro k hk
    change finrank ℝ (diskHandleHomology E k) ≠ 0 at hk
    apply Finset.mem_range.mpr
    by_contra h
    letI := ModuleCat.subsingleton_of_isZero (diskHandleHomology_isZero_above E N hN k (by omega))
    exact hk (Module.finrank_eq_zero_of_subsingleton _ _)
  rw [GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset _ _ _ hsupport]
  simp only [ComplexShape.χ, ComplexShape.eulerCharSignsDownNat,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  simp_rw [diskHandleHomology_finrank, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hi : finrank ℝ (E i) < N + 1 := by have := hN i; omega
  simp [mul_ite, hi, Finset.mem_range]

end FiniteFamily

end GaussBonnetChern


noncomputable section
namespace GaussBonnetChern
open CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators DirectSum

variable {ι : Type u} [Fintype ι] (E F : ι → Type u)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (E i)]

/-- Component comparisons combine through the actual disjoint-union relative
chain coproduct. The component spaces may be genuine modified Morse blocks. -/
def relativeFamilyHomologyIsoDiskSum (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
    (A : ∀ i, Set (X i)) (k : ℕ)
    (e : ∀ i, relativeSingularHomology (X i) (A i) k ≅
      relativeSingularHomology (Metric.closedBall (0 : E i) 1)
        (unitDiskBoundarySubset (E i)) k) :
    relativeSingularHomology (Σ i, X i) (sigmaPairSubset X A) k ≅
      diskHandleHomology E k := by
  classical
  exact relativeSingularHomologySigmaIso X A k ≪≫
    (ModuleCat.coprodIsoDirectSum (fun i ↦ relativeSingularHomology (X i) (A i) k)).symm ≪≫
    Sigma.mapIso e ≪≫
    ModuleCat.coprodIsoDirectSum (fun i ↦ relativeSingularHomology
      (Metric.closedBall (0 : E i) 1) (unitDiskBoundarySubset (E i)) k)

/-- The genuine finite disjoint union of model handles. -/
abbrev finiteModelHandles := Σ i, modelHandle (E i) (F i)

/-- Its actual attaching subset, with no restriction on empty families. -/
def finiteModelHandlesAttachingSubset : Set (finiteModelHandles E F) :=
  sigmaPairSubset (fun i ↦ modelHandle (E i) (F i))
    (fun i ↦ modelHandleAttachingSubset (E i) (F i))

/-- Actual relative homology of simultaneous handles is the direct sum of the
negative disk-boundary homologies. This is derived from actual singular-chain
coproducts and the positive-disk contractions. -/
def finiteModelHandlesHomologyIsoDiskSum (k : ℕ) :
    relativeSingularHomology (finiteModelHandles E F)
      (finiteModelHandlesAttachingSubset E F) k ≅ diskHandleHomology E k := by
  exact relativeFamilyHomologyIsoDiskSum E
      (fun i ↦ modelHandle (E i) (F i))
      (fun i ↦ modelHandleAttachingSubset (E i) (F i)) k
      (fun i ↦ modelHandleHomologyIsoDisk (E i) (F i) k)

theorem finiteModelHandles_homology_finiteDimensional (k : ℕ) :
    FiniteDimensional ℝ (relativeSingularHomology (finiteModelHandles E F)
      (finiteModelHandlesAttachingSubset E F) k) := by
  letI := diskHandleHomology_finiteDimensional E k
  exact (finiteModelHandlesHomologyIsoDiskSum E F k).toLinearEquiv.symm.finiteDimensional

theorem finiteModelHandles_homology_finrank (k : ℕ) :
    finrank ℝ (relativeSingularHomology (finiteModelHandles E F)
      (finiteModelHandlesAttachingSubset E F) k) =
        ∑ i, if k = finrank ℝ (E i) then 1 else 0 :=
  (finiteModelHandlesHomologyIsoDiskSum E F k).toLinearEquiv.finrank_eq.trans
    (diskHandleHomology_finrank E k)

theorem finiteModelHandles_homology_isZero_above (N : ℕ)
    (hN : ∀ i, finrank ℝ (E i) ≤ N) (k : ℕ) (hk : N < k) :
    IsZero (relativeSingularHomology (finiteModelHandles E F)
      (finiteModelHandlesAttachingSubset E F) k) :=
  (diskHandleHomology_isZero_above E N hN k hk).of_iso
    (finiteModelHandlesHomologyIsoDiskSum E F k)

theorem finiteModelHandles_relativeEulerCharacteristic (N : ℕ)
    (hN : ∀ i, finrank ℝ (E i) ≤ N) :
    relativeEulerCharacteristic (finiteModelHandles E F)
      (finiteModelHandlesAttachingSubset E F) = ∑ i, (-1 : ℤ) ^ finrank ℝ (E i) := by
  calc
    _ = GradedObject.eulerChar (ComplexShape.down ℕ) (diskHandleHomology E) := by
      unfold relativeEulerCharacteristic HomologicalComplex.homologyEulerChar GradedObject.eulerChar
      apply finsum_congr
      intro k
      rw [(finiteModelHandlesHomologyIsoDiskSum E F k).toLinearEquiv.finrank_eq]
    _ = _ := diskHandleHomology_eulerChar E N hN

/-- A finite sublevel step once its genuine relative-homology comparison has
been constructed. This lemma does not assume or prove geometric attachment. -/
theorem finiteHomology_step_of_relative_comparison
    (Y : Type u) [TopologicalSpace Y] (A : Set Y)
    (e : ∀ k, relativeSingularHomology Y A k ≅ diskHandleHomology E k)
    (N : ℕ) (hN : ∀ i, finrank ℝ (E i) ≤ N)
    [∀ k, FiniteDimensional ℝ (singularHomology A k)]
    (hA : ∀ k, N < k → IsZero (singularHomology A k)) :
    (∀ k, FiniteDimensional ℝ (singularHomology Y k)) ∧
      (∀ k, N < k → IsZero (singularHomology Y k)) ∧
      topologicalEulerCharacteristic Y =
        topologicalEulerCharacteristic A + ∑ i, (-1 : ℤ) ^ finrank ℝ (E i) := by
  letI hR (k : ℕ) : FiniteDimensional ℝ (relativeSingularHomology Y A k) := by
    letI := diskHandleHomology_finiteDimensional E k
    exact (e k).toLinearEquiv.symm.finiteDimensional
  letI hY (k : ℕ) : FiniteDimensional ℝ (singularHomology Y k) :=
    singularHomology_finiteDimensional_of_subspace_relative Y A k
  have hvR (k : ℕ) (hk : N < k) : IsZero (relativeSingularHomology Y A k) :=
    (diskHandleHomology_isZero_above E N hN k hk).of_iso (e k)
  have hvY (k : ℕ) (hk : N < k) : IsZero (singularHomology Y k) :=
    singularHomology_isZero_of_subspace_relative Y A k (hA k hk) (hvR k hk)
  refine ⟨hY, hvY, ?_⟩
  have he : relativeEulerCharacteristic Y A =
      ∑ i, (-1 : ℤ) ^ finrank ℝ (E i) := by
    calc
      _ = GradedObject.eulerChar (ComplexShape.down ℕ) (diskHandleHomology E) := by
        unfold relativeEulerCharacteristic HomologicalComplex.homologyEulerChar GradedObject.eulerChar
        apply finsum_congr
        intro k
        rw [(e k).toLinearEquiv.finrank_eq]
      _ = _ := diskHandleHomology_eulerChar E N hN
  rw [topologicalEulerCharacteristic_additive Y A N
    (fun k hk ↦ ModuleCat.subsingleton_of_isZero (hvY k hk))
    (fun k hk ↦ ModuleCat.subsingleton_of_isZero (hA k hk))
    (fun k hk ↦ ModuleCat.subsingleton_of_isZero (hvR k hk)), he]

end GaussBonnetChern

