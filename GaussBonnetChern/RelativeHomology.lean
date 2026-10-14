import GaussBonnetChern.Topology
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Relative singular homology with the project's real coefficients

A topological pair is an actual subset inclusion. Applying the singular-set
functor gives the monomorphism required by Mathlib's `SSetPair`; no preservation
of topological pushouts is asserted. The absolute terms below are definitionally
the homology of `GaussBonnetChern.singularChains`.

The long exact sequence is an algebraic consequence of this relative chain
complex. Excision, calculations for disk/sphere pairs, and the finiteness of
manifold homology remain separate proof obligations.
-/

noncomputable section

universe u

namespace GaussBonnetChern

open CategoryTheory

/-- The real coefficient object at the universe of the underlying space. -/
abbrev realHomologyCoefficients : ModuleCat.{u} ℝ :=
  ModuleCat.of ℝ (ULift.{u} ℝ)

variable (X : Type u) [TopologicalSpace X] (A : Set X)

/-- The continuous inclusion of a subspace, as a morphism of topological spaces. -/
def subspaceInclusion : TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

instance subspaceInclusion_mono : Mono (subspaceInclusion X A) :=
  (TopCat.mono_iff_injective _).2 Subtype.val_injective

/-- The singular simplicial pair of the actual inclusion `A ⊆ X`. -/
def singularPair : SSetPair.{u} :=
  SSetPair.of (TopCat.toSSet.map (subspaceInclusion X A))

/-- Real singular homology, using precisely the project's singular chains. -/
abbrev singularHomology (k : ℕ) : ModuleCat.{u} ℝ :=
  (singularChains X).homology k

/-- Relative singular chains of the topological pair `(X,A)`. -/
abbrev relativeSingularChains : ChainComplex (ModuleCat.{u} ℝ) ℕ :=
  (singularPair X A).chainComplex realHomologyCoefficients

/-- Relative real singular homology of `(X,A)`. -/
abbrev relativeSingularHomology (k : ℕ) : ModuleCat.{u} ℝ :=
  (relativeSingularChains X A).homology k

/-- The left absolute chain complex is the singular chain complex of `A`. -/
theorem singularPair_left_chainComplex :
    (singularPair X A).left.chainComplex realHomologyCoefficients = singularChains A :=
  rfl

/-- The right absolute chain complex is the singular chain complex of `X`. -/
theorem singularPair_right_chainComplex :
    (singularPair X A).right.chainComplex realHomologyCoefficients = singularChains X :=
  rfl

/-- The absolute homology at the left of the relative sequence is `H_k(A;ℝ)`. -/
def singularPairLeftHomologyIso (k : ℕ) :
    (singularPair X A).left.homology realHomologyCoefficients k ≅ singularHomology A k :=
  Iso.refl _

/-- The absolute homology at the right of the relative sequence is `H_k(X;ℝ)`. -/
def singularPairRightHomologyIso (k : ℕ) :
    (singularPair X A).right.homology realHomologyCoefficients k ≅ singularHomology X k :=
  Iso.refl _

/-- The homology map induced by the subspace inclusion. -/
abbrev singularHomologyInclusion (k : ℕ) :
    singularHomology A k ⟶ singularHomology X k :=
  SSet.homologyMap (singularPair X A).hom realHomologyCoefficients k

/-- The map from absolute to relative homology. -/
abbrev singularHomologyToRelative (k : ℕ) :
    singularHomology X k ⟶ relativeSingularHomology X A k :=
  (singularPair X A).homologyπ realHomologyCoefficients k

/-- The connecting map `H_(k+1)(X,A;ℝ) → H_k(A;ℝ)`. -/
abbrev relativeSingularHomologyConnecting (k : ℕ) :
    relativeSingularHomology X A (k + 1) ⟶ singularHomology A k :=
  (singularPair X A).homologyδ realHomologyCoefficients (k + 1) k rfl

theorem singularHomologyInclusion_comp_toRelative (k : ℕ) :
    singularHomologyInclusion X A k ≫ singularHomologyToRelative X A k = 0 :=
  (singularPair X A).homologyMap_hom_homologyπ realHomologyCoefficients k

theorem relativeSingularHomologyConnecting_comp_inclusion (k : ℕ) :
    relativeSingularHomologyConnecting X A k ≫ singularHomologyInclusion X A k = 0 :=
  (singularPair X A).homologyδ_comp realHomologyCoefficients (k + 1) k rfl

theorem singularHomologyToRelative_comp_connecting (k : ℕ) :
    singularHomologyToRelative X A (k + 1) ≫ relativeSingularHomologyConnecting X A k = 0 :=
  (singularPair X A).comp_homologyδ realHomologyCoefficients (k + 1) k rfl

/-- Exactness of `H_(k+1)(X,A) → H_k(A) → H_k(X)`. -/
theorem relativeSingularHomology_exact_at_subspace (k : ℕ) :
    (ShortComplex.mk _ _ (relativeSingularHomologyConnecting_comp_inclusion X A k)).Exact :=
  (singularPair X A).homology_exact₁ realHomologyCoefficients (k + 1) k rfl

/-- Exactness of `H_k(A) → H_k(X) → H_k(X,A)`. -/
theorem relativeSingularHomology_exact_at_space (k : ℕ) :
    (ShortComplex.mk _ _ (singularHomologyInclusion_comp_toRelative X A k)).Exact :=
  (singularPair X A).homology_exact₂ realHomologyCoefficients k

/-- Exactness of `H_(k+1)(X) → H_(k+1)(X,A) → H_k(A)`. -/
theorem relativeSingularHomology_exact_at_relative (k : ℕ) :
    (ShortComplex.mk _ _ (singularHomologyToRelative_comp_connecting X A k)).Exact :=
  (singularPair X A).homology_exact₃ realHomologyCoefficients (k + 1) k rfl

/-- The zero-degree relative sequence ends in `H_0(X,A) → 0`. -/
instance singularHomologyToRelative_zero_epi : Epi (singularHomologyToRelative X A 0) :=
  inferInstanceAs (Epi ((singularPair X A).homologyπ realHomologyCoefficients 0))

/-! The following rank identities have explicit finite-dimensionality hypotheses.
They are algebraic inputs to a future Euler-characteristic argument; they do not
establish those hypotheses or finite homological support for a manifold. -/

/-- Degreewise rank balance in the relative long exact sequence. The two
connecting-map ranks cancel in a bounded alternating sum. -/
theorem relativeSingularHomology_finrank_balance (k : ℕ)
    [FiniteDimensional ℝ (singularHomology A (k + 1))]
    [FiniteDimensional ℝ (singularHomology X (k + 1))]
    [FiniteDimensional ℝ (relativeSingularHomology X A (k + 1))] :
    Module.finrank ℝ (singularHomology X (k + 1)) +
        Module.finrank ℝ (LinearMap.range (relativeSingularHomologyConnecting X A (k + 1)).hom) +
        Module.finrank ℝ (LinearMap.range (relativeSingularHomologyConnecting X A k).hom) =
      Module.finrank ℝ (singularHomology A (k + 1)) +
        Module.finrank ℝ (relativeSingularHomology X A (k + 1)) := by
  have hi := (singularHomologyInclusion X A (k + 1)).hom.finrank_range_add_finrank_ker
  have hq := (singularHomologyToRelative X A (k + 1)).hom.finrank_range_add_finrank_ker
  have hd := (relativeSingularHomologyConnecting X A k).hom.finrank_range_add_finrank_ker
  have ei := (relativeSingularHomology_exact_at_subspace X A (k + 1)).moduleCat_range_eq_ker
  have eq := (relativeSingularHomology_exact_at_space X A (k + 1)).moduleCat_range_eq_ker
  have ed := (relativeSingularHomology_exact_at_relative X A k).moduleCat_range_eq_ker
  dsimp only at ei eq ed
  rw [← ei] at hi
  rw [← eq] at hq
  rw [← ed] at hd
  omega

/-- The degree-zero rank balance, using the actual terminal epimorphism of
the relative long exact sequence. -/
theorem relativeSingularHomology_finrank_balance_zero
    [FiniteDimensional ℝ (singularHomology A 0)]
    [FiniteDimensional ℝ (singularHomology X 0)] :
    Module.finrank ℝ (singularHomology X 0) +
        Module.finrank ℝ (LinearMap.range (relativeSingularHomologyConnecting X A 0).hom) =
      Module.finrank ℝ (singularHomology A 0) +
        Module.finrank ℝ (relativeSingularHomology X A 0) := by
  have hi := (singularHomologyInclusion X A 0).hom.finrank_range_add_finrank_ker
  have hq := (singularHomologyToRelative X A 0).hom.finrank_range_add_finrank_ker
  have ei := (relativeSingularHomology_exact_at_subspace X A 0).moduleCat_range_eq_ker
  have eq := (relativeSingularHomology_exact_at_space X A 0).moduleCat_range_eq_ker
  dsimp only at ei eq
  have hr : LinearMap.range (singularHomologyToRelative X A 0).hom = ⊤ :=
    (ModuleCat.epi_iff_range_eq_top _).mp inferInstance
  rw [← ei] at hi
  rw [← eq, hr, finrank_top] at hq
  omega

end GaussBonnetChern
