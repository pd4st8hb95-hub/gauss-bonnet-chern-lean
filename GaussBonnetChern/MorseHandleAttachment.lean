import GaussBonnetChern.QuadraticHandleDeformation
import GaussBonnetChern.DiskPairHomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Actual pair maps for local handle comparisons

This file starts from genuine maps of topological pairs. Relative homology
invariance is derived from the short exact sequence of actual singular chain
complexes. The geometric attachment of manifold sublevel sets remains a
separate obligation until its deformation and excision maps are constructed.
-/

noncomputable section
universe u

namespace GaussBonnetChern

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ContinuousMap

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {A : Set X} {B : Set Y}

/-- Restriction of a continuous map which carries the specified subspace
into the target subspace. -/
def continuousMapOfPair (f : C(X, Y)) (hf : Set.MapsTo f A B) : C(A, B) :=
  ⟨fun x ↦ ⟨f x, hf x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The induced map of actual singular simplicial pairs. -/
def singularPairMap (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    singularPair X A ⟶ singularPair Y B :=
  SSetPair.homMk (TopCat.toSSet.map (TopCat.ofHom (continuousMapOfPair f hf)))
    (TopCat.toSSet.map (TopCat.ofHom f)) (by
      change TopCat.toSSet.map (TopCat.ofHom (continuousMapOfPair f hf)) ≫
          TopCat.toSSet.map (subspaceInclusion Y B) =
        TopCat.toSSet.map (subspaceInclusion X A) ≫ TopCat.toSSet.map (TopCat.ofHom f)
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      congr 1)

/-- The chain map on the actual relative singular chain complexes. -/
def relativeSingularChainsMap (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    relativeSingularChains X A ⟶ relativeSingularChains Y B :=
  SSetPair.chainComplexMap (singularPairMap f hf) realHomologyCoefficients

/-- A pair map supplies a commuting morphism of the short exact singular
chain sequences, including the actual quotient projection. -/
def singularPairChainSequenceMap {P Q : SSetPair.{u}} (φ : P ⟶ Q) :
    P.chainComplexShortComplex realHomologyCoefficients ⟶
      Q.chainComplexShortComplex realHomologyCoefficients where
  τ₁ := SSet.chainComplexMap φ.left realHomologyCoefficients
  τ₂ := SSet.chainComplexMap φ.right realHomologyCoefficients
  τ₃ := SSetPair.chainComplexMap φ realHomologyCoefficients
  comm₁₂ := by
    change SSet.chainComplexMap φ.left realHomologyCoefficients ≫
        SSet.chainComplexMap Q.hom realHomologyCoefficients =
      SSet.chainComplexMap P.hom realHomologyCoefficients ≫
        SSet.chainComplexMap φ.right realHomologyCoefficients
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    exact φ.w
  comm₂₃ := ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℝ)).app
    realHomologyCoefficients).naturality φ

/-- Both absolute maps being quasi-isomorphisms implies the actual relative
map is a quasi-isomorphism, by the long exact homology sequences. -/
theorem relativeSingularChainsMap_quasiIso
    (f : C(X, Y)) (hf : Set.MapsTo f A B)
    (hX : QuasiIso (singularChainsMap f))
    (hA : QuasiIso (singularChainsMap (continuousMapOfPair f hf))) :
    QuasiIso (relativeSingularChainsMap f hf) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (singularPairChainSequenceMap (singularPairMap f hf))
    ((singularPair X A).shortExact_chainComplexShortComplex realHomologyCoefficients)
    ((singularPair Y B).shortExact_chainComplexShortComplex realHomologyCoefficients) hA hX

/-- The forward singular chain map of an actual homotopy equivalence is a
quasi-isomorphism in every degree. -/
theorem singularChainsMap_quasiIso_of_homotopyEquiv (e : X ≃ₕ Y) :
    QuasiIso (singularChainsMap e.toFun) := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (singularHomologyIsoOfHomotopyEquiv e k).isIso_hom

/-- A pair map whose ambient and restricted maps are homotopy equivalences
induces the actual relative homology isomorphism. -/
def relativeSingularHomologyIsoOfHomotopyEquivs
    (e : X ≃ₕ Y) (hf : Set.MapsTo e.toFun A B) (a : A ≃ₕ B)
    (ha : a.toFun = continuousMapOfPair e.toFun hf) (k : ℕ) :
    relativeSingularHomology X A k ≅ relativeSingularHomology Y B k := by
  letI : QuasiIso (relativeSingularChainsMap e.toFun hf) :=
    relativeSingularChainsMap_quasiIso e.toFun hf
      (singularChainsMap_quasiIso_of_homotopyEquiv e)
      (by rw [← ha]; exact singularChainsMap_quasiIso_of_homotopyEquiv a)
  exact asIso (homologyMap (relativeSingularChainsMap e.toFun hf) k)

section ProductPair

variable (X K : Type u) [TopologicalSpace X] [TopologicalSpace K] (A : Set X)

/-- The attaching subset in a product pair: all positive directions remain
free while the negative coordinate lies on the specified attaching subspace. -/
def productPairSubset : Set (X × K) := Prod.fst ⁻¹' A

def productPairSubsetHomeomorph : productPairSubset X K A ≃ₜ A × K where
  toFun x := (⟨x.val.1, x.property⟩, x.val.2)
  invFun x := ⟨(x.1.val, x.2), x.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Projection of a product with a contractible factor gives a genuine
isomorphism of relative homology, including degree zero and empty A. -/
def productPairRelativeHomologyIso [ContractibleSpace K] (k : ℕ) :
    relativeSingularHomology (X × K) (productPairSubset X K A) k ≅
      relativeSingularHomology X A k := by
  let e : (X × K) ≃ₕ X := prodContractibleHomotopyEquiv
  have hf : Set.MapsTo e.toFun (productPairSubset X K A) A := fun _ h ↦ h
  let a : productPairSubset X K A ≃ₕ A :=
    (productPairSubsetHomeomorph X K A).toHomotopyEquiv.trans prodContractibleHomotopyEquiv
  exact relativeSingularHomologyIsoOfHomotopyEquivs e hf a rfl k

end ProductPair

section ModelHandle

variable (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The usual index-`dim E` handle, with both its negative and positive disks. -/
abbrev modelHandle := Metric.closedBall (0 : E) 1 × Metric.closedBall (0 : F) 1

/-- The attaching region `∂D(E) × D(F)` as an actual subset of the handle. -/
def modelHandleAttachingSubset : Set (modelHandle E F) :=
  productPairSubset (Metric.closedBall (0 : E) 1) (Metric.closedBall (0 : F) 1)
    (unitDiskBoundarySubset E)

/-- Homology of the actual model handle pair reduces to that of its negative
disk by contracting the positive disk, via genuine pair maps. -/
def modelHandleHomologyIsoDisk (k : ℕ) :
    relativeSingularHomology (modelHandle E F) (modelHandleAttachingSubset E F) k ≅
      relativeSingularHomology (Metric.closedBall (0 : E) 1) (unitDiskBoundarySubset E) k := by
  letI := unitDisk_contractible F
  exact productPairRelativeHomologyIso _ _ _ k

/-- All actual model-handle homology groups are finite dimensional, with the
single rank-one group in the negative-space dimension. -/
theorem modelHandle_homology_finite_and_finrank [FiniteDimensional ℝ E] (k : ℕ) :
    FiniteDimensional ℝ (relativeSingularHomology
      (modelHandle E F) (modelHandleAttachingSubset E F) k) ∧
    Module.finrank ℝ (relativeSingularHomology
      (modelHandle E F) (modelHandleAttachingSubset E F) k) =
        if k = Module.finrank ℝ E then 1 else 0 := by
  let e := modelHandleHomologyIsoDisk E F k
  have h := unitDiskPair_homology_finite_and_finrank E (Module.finrank ℝ E) rfl k
  letI := h.1
  exact ⟨e.toLinearEquiv.symm.finiteDimensional, e.toLinearEquiv.finrank_eq.trans h.2⟩

end ModelHandle

end GaussBonnetChern


noncomputable section
namespace GaussBonnetChern
open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap

variable {U V : Type u} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual modified quadratic Morse pair has negative disk-boundary
homology. All maps come from the explicitly constructed two homotopy
equivalences; the cutoff conditions remain visible model hypotheses. -/
def quadraticLowerPairHomologyIsoDisk (μ : ℝ → ℝ) (a r s : ℝ)
    (ha : 0 < a) (har : a ≤ r) (hμ : AntitoneOn μ (Set.Ici 0)) (hs : 0 ≤ s)
    (hcover : ∀ b ≥ 0, a ^ 2 ≤ b + μ b) (k : ℕ) :
    relativeSingularHomology
      (QuadraticHandle.lowerBlock (U := U) (V := V) μ (a ^ 2) r s)
      (QuadraticHandle.lowerAttaching μ (a ^ 2) r s) k ≅
        relativeSingularHomology (Metric.closedBall (0 : U) 1) (unitDiskBoundarySubset U) k := by
  let e := QuadraticHandle.lowerBlockHomotopyEquivUnitDisk (U := U) (V := V)
    μ a r s ha har hμ hs hcover
  have hb : Set.MapsTo e.toFun (QuadraticHandle.lowerAttaching μ (a ^ 2) r s)
      (unitDiskBoundarySubset U) :=
    QuadraticHandle.lowerBlockHomotopyEquivUnitDisk_boundary μ a r s ha har hμ hs hcover
  let b := (QuadraticHandle.lowerAttachingHomotopyEquivUnitSphere (U := U) (V := V)
      μ a r s ha har hμ hs hcover).trans (unitDiskBoundaryHomeomorphSphere U).symm.toHomotopyEquiv
  apply relativeSingularHomologyIsoOfHomotopyEquivs e hb b _ k
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact QuadraticHandle.lowerBlockHomotopyEquivUnitDisk_restrict μ a r s ha har hμ hs hcover x

end GaussBonnetChern

