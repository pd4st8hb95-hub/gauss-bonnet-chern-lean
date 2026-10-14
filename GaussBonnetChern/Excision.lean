import GaussBonnetChern.SmallChains
import GaussBonnetChern.RelativeHomology
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Homological bridge toward actual-pair singular excision

The module criterion below is proved using the library's concrete kernel/quotient
homology data. Topological excision is not inferred from preservation of pushouts
by the singular-set functor.
-/

noncomputable section

universe u v

namespace GaussBonnetChern

open CategoryTheory Convexity
open scoped BigOperators Simplicial

/-- Concrete cycle-lifting and boundary-lifting certificates suffice for an
actual module short-complex map to induce a homology isomorphism. -/
theorem moduleShortComplex_quasiIso_of_cycle_lift
    {S₁ S₂ : ShortComplex (ModuleCat.{u} ℝ)} (φ : S₁ ⟶ S₂)
    (hsurj : ∀ z₂ : S₂.X₂, S₂.g z₂ = 0 →
      ∃ z₁ : S₁.X₂, S₁.g z₁ = 0 ∧ ∃ w₂ : S₂.X₁, S₂.f w₂ = φ.τ₂ z₁ - z₂)
    (hinj : ∀ z₁ : S₁.X₂, S₁.g z₁ = 0 →
      ∀ w₂ : S₂.X₁, S₂.f w₂ = φ.τ₂ z₁ → ∃ w₁ : S₁.X₁, S₁.f w₁ = z₁) :
    ShortComplex.QuasiIso φ := by
  let h₁ := S₁.moduleCatLeftHomologyData
  let h₂ := S₂.moduleCatLeftHomologyData
  let F := ShortComplex.leftHomologyMap' φ h₁ h₂
  let K : LinearMap.ker S₁.g.hom →ₗ[ℝ] LinearMap.ker S₂.g.hom :=
    (ShortComplex.cyclesMap' φ h₁ h₂).hom
  have hK (z : LinearMap.ker S₁.g.hom) : (K z).val = φ.τ₂ z.val := by
    have h := congrArg (fun f ↦ f z) (ShortComplex.cyclesMap'_i φ h₁ h₂)
    exact h
  have hF (z : LinearMap.ker S₁.g.hom) :
      F (Submodule.Quotient.mk z) = Submodule.Quotient.mk (K z) := by
    have h := congrArg (fun f ↦ f z) (ShortComplex.leftHomologyπ_naturality' φ h₁ h₂)
    exact h
  have hzero (q : h₁.H) (hq : F q = 0) : q = 0 := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective S₁.moduleCatToCycles.range q
    rw [hF] at hq
    obtain ⟨w₂, hw₂⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
    have hw₂' : S₂.f w₂ = φ.τ₂ z.val := by
      have h := congrArg Subtype.val hw₂
      change S₂.f w₂ = (K z).val at h
      rw [hK] at h
      exact h
    obtain ⟨w₁, hw₁⟩ := hinj z.val z.property w₂ hw₂'
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨w₁, Subtype.ext hw₁⟩
  rw [ShortComplex.quasiIso_iff_isIso_leftHomologyMap' φ h₁ h₂,
    ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hab, sub_self]
  · intro q
    obtain ⟨z₂, rfl⟩ := Submodule.Quotient.mk_surjective S₂.moduleCatToCycles.range q
    obtain ⟨z₁, hz₁, w₂, hw₂⟩ := hsurj z₂.val z₂.property
    let z : LinearMap.ker S₁.g.hom := ⟨z₁, hz₁⟩
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    rw [hF]
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨w₂, Subtype.ext ?_⟩
    change S₂.f w₂ = (K z).val - z₂.val
    rw [hK]
    exact hw₂

@[simp]
theorem smallSingularChainsInclusion_f_apply {X : Type u} [TopologicalSpace X]
    {ι : Type v} (U : ι → Set X) (n : ℕ) (z : (smallSingularChains U).X n) :
    (smallSingularChainsInclusion U).f n z = z.val := rfl

theorem smallSingularChains_d_val {X : Type u} [TopologicalSpace X]
    {ι : Type v} (U : ι → Set X) (i j : ℕ) (z : (smallSingularChains U).X i) :
    ((smallSingularChains U).d i j z).val = (singularChains X).d i j z.val := by
  have h := congrArg (fun f ↦ f z) ((smallSingularChainsInclusion U).comm i j)
  simpa only [ModuleCat.comp_apply, smallSingularChainsInclusion_f_apply] using h.symm

/-- Small-chain inclusion is a quasi-isomorphism for every open cover of the
actual space, proved from geometric subdivision and the actual cycle certificates. -/
theorem smallSingularChainsInclusion_quasiIso {X : Type u} [TopologicalSpace X]
    {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) : QuasiIso (smallSingularChainsInclusion U) := by
  constructor
  intro n
  apply (quasiIsoAt_iff' (smallSingularChainsInclusion U) (n + 1) n (n - 1)
    (by simp) (by cases n <;> simp)).mpr
  apply moduleShortComplex_quasiIso_of_cycle_lift
  · intro z₂ hz₂
    obtain ⟨z', hs, hz', w, hw⟩ := singularCycle_small_representative U hU hcover z₂ hz₂
    refine ⟨⟨z', hs⟩, ?_, w, hw⟩
    apply Subtype.ext
    exact (smallSingularChains_d_val U n (n - 1) ⟨z', hs⟩).trans hz'
  · intro z₁ hz₁ w₂ hw₂
    have hz : (singularChains X).d n (n - 1) z₁.val = 0 := by
      rw [← smallSingularChains_d_val U n (n - 1) z₁]
      exact congrArg Subtype.val hz₁
    obtain ⟨w', hs, hw'⟩ := smallCycle_small_boundary U hU hcover z₁.val z₁.property hz w₂ hw₂
    refine ⟨⟨w', hs⟩, ?_⟩
    apply Subtype.ext
    exact (smallSingularChains_d_val U (n + 1) n ⟨w', hs⟩).trans hw'

/-- The actual subspace `(X \ Z) ∩ A`, expressed as a subset of `X \ Z`. -/
def excisionSourceSubset (X : Type u) (A Z : Set X) : Set (Zᶜ : Set X) :=
  Subtype.val ⁻¹' A

def excisionLeftInclusion (X : Type u) [TopologicalSpace X] (A Z : Set X) :
    TopCat.of (excisionSourceSubset X A Z) ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

/-- The functorial map of actual singular pairs `(X \ Z,A \ Z) → (X,A)`. -/
def excisionPairMap (X : Type u) [TopologicalSpace X] (A Z : Set X) :
    singularPair (Zᶜ : Set X) (excisionSourceSubset X A Z) ⟶ singularPair X A :=
  SSetPair.homMk (TopCat.toSSet.map (excisionLeftInclusion X A Z))
    (TopCat.toSSet.map (subspaceInclusion X Zᶜ)) (by
      change TopCat.toSSet.map (excisionLeftInclusion X A Z) ≫
          TopCat.toSSet.map (subspaceInclusion X A) =
        TopCat.toSSet.map (subspaceInclusion (Zᶜ : Set X) (excisionSourceSubset X A Z)) ≫
          TopCat.toSSet.map (subspaceInclusion X Zᶜ)
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1)

def relativeExcisionChainMap (X : Type u) [TopologicalSpace X] (A Z : Set X) :
    relativeSingularChains (Zᶜ : Set X) (excisionSourceSubset X A Z) ⟶
      relativeSingularChains X A :=
  SSetPair.chainComplexMap (excisionPairMap X A Z) realHomologyCoefficients

def relativeExcisionHomologyMap (X : Type u) [TopologicalSpace X] (A Z : Set X) (n : ℕ) :
    relativeSingularHomology (Zᶜ : Set X) (excisionSourceSubset X A Z) n ⟶
      relativeSingularHomology X A n :=
  HomologicalComplex.homologyMap (relativeExcisionChainMap X A Z) n

def excisionOpenCover (X : Type u) [TopologicalSpace X] (A Z : Set X) (i : Bool) : Set X := match i with
  | false => interior A
  | true => (closure Z)ᶜ

theorem excisionOpenCover_open (X : Type u) [TopologicalSpace X] (A Z : Set X) (i : Bool) :
    IsOpen (excisionOpenCover X A Z i) := by
  cases i
  · exact isOpen_interior
  · exact isClosed_closure.isOpen_compl

theorem excisionOpenCover_covers (X : Type u) [TopologicalSpace X] (A Z : Set X)
    (hZ : closure Z ⊆ interior A) : ⋃ i, excisionOpenCover X A Z i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ closure Z
  · exact Set.mem_iUnion.mpr ⟨false, hZ hx⟩
  · exact Set.mem_iUnion.mpr ⟨true, hx⟩

def subspaceSingularChainMap (X : Type u) [TopologicalSpace X] (A : Set X) :
    singularChains A ⟶ singularChains X :=
  singularChainPostcompose (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))

theorem singularSimplexGenerator_mem_subspaceRange {X : Type u} [TopologicalSpace X]
    {n : ℕ} (A : Set X) (s : C(StdSimplex ℝ (Fin (n + 1)), X))
    (hs : Set.range s ⊆ A) (a : ULift.{u} ℝ) :
    singularSimplexGenerator s a ∈ LinearMap.range ((subspaceSingularChainMap X A).f n).hom := by
  let sA : C(StdSimplex ℝ (Fin (n + 1)), A) :=
    ⟨fun x ↦ ⟨s x, hs ⟨x, rfl⟩⟩, s.continuous.subtype_mk _⟩
  refine ⟨singularSimplexGenerator sA a, ?_⟩
  change (singularSimplexGenerator sA ≫
    (singularChainPostcompose (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).f n) a = _
  rw [singularSimplexGenerator_postcompose]
  rfl

/-- Excision-small chains split into the actual images of chains in `A` and
chains in `X \ Z`; this uses the geometric open cover, not a pushout claim. -/
theorem excisionSmallChains_le_sum (X : Type u) [TopologicalSpace X]
    (A Z : Set X) (n : ℕ) :
    smallChainSubmodule (excisionOpenCover X A Z) n ≤
      LinearMap.range ((subspaceSingularChainMap X A).f n).hom ⊔
        LinearMap.range ((subspaceSingularChainMap X Zᶜ).f n).hom := by
  apply Submodule.span_le.mpr
  rintro z ⟨s, a, ⟨i, hi⟩, rfl⟩
  cases i
  · apply Submodule.mem_sup_left
    exact singularSimplexGenerator_mem_subspaceRange A s (hi.trans interior_subset) a
  · apply Submodule.mem_sup_right
    apply singularSimplexGenerator_mem_subspaceRange Zᶜ s
    intro x hx hz
    exact hi hx (subset_closure hz)

/-- Every actual absolute chain has sufficiently subdivided decompositions in
the two actual subspace chain groups required by relative excision. -/
theorem singularChain_eventually_excision_decomposition (X : Type u) [TopologicalSpace X]
    (A Z : Set X) (hZ : closure Z ⊆ interior A) (n : ℕ) (z : (singularChains X).X n) :
    ∃ k : ℕ, ∀ l ≥ k, ∃ a : (singularChains A).X n, ∃ b : (singularChains (Zᶜ : Set X)).X n,
      (iteratedSubdivision X l).f n z =
        (subspaceSingularChainMap X A).f n a + (subspaceSingularChainMap X Zᶜ).f n b := by
  obtain ⟨k, hk⟩ := singularChain_eventually_small (excisionOpenCover X A Z)
    (excisionOpenCover_open X A Z) (excisionOpenCover_covers X A Z hZ) z
  refine ⟨k, fun l hl ↦ ?_⟩
  have hs := excisionSmallChains_le_sum X A Z n (hk l hl)
  obtain ⟨a', ha', b', hb', heq⟩ := Submodule.mem_sup.mp hs
  obtain ⟨a, rfl⟩ := ha'
  obtain ⟨b, rfl⟩ := hb'
  exact ⟨a, b, heq.symm⟩

def relativeSingularProjection (X : Type u) [TopologicalSpace X] (A : Set X) :
    singularChains X ⟶ relativeSingularChains X A :=
  (singularPair X A).chainComplexπ realHomologyCoefficients

theorem relativeSingularProjection_lift (X : Type u) [TopologicalSpace X] (A : Set X)
    (n : ℕ) (z : (relativeSingularChains X A).X n) :
    ∃ x : (singularChains X).X n, (relativeSingularProjection X A).f n x = z :=
  (ModuleCat.epi_iff_surjective (((singularPair X A).chainComplexπ realHomologyCoefficients).f n)).mp
    inferInstance z

theorem subspaceSingularChainMap_projection (X : Type u) [TopologicalSpace X] (A : Set X) :
    subspaceSingularChainMap X A ≫ relativeSingularProjection X A = 0 :=
  (singularPair X A).chainComplex_condition realHomologyCoefficients

theorem barycentricSubdivision_postcompose {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    barycentricSubdivision X ≫ singularChainPostcompose f =
      singularChainPostcompose f ≫ barycentricSubdivision Y := by
  ext n : 1
  exact barycentricSubdivisionDegree_postcompose f n

/-- Subdivision descends to the actual relative cokernel because it commutes
with the actual subspace inclusion. -/
def relativeBarycentricSubdivision (X : Type u) [TopologicalSpace X] (A : Set X) :
    relativeSingularChains X A ⟶ relativeSingularChains X A :=
  ((singularPair X A).isColimitCokernelCoforkChainComplex realHomologyCoefficients).desc
    (Limits.CokernelCofork.ofπ (barycentricSubdivision X ≫ relativeSingularProjection X A) (by
      change subspaceSingularChainMap X A ≫
        (barycentricSubdivision X ≫ relativeSingularProjection X A) = 0
      rw [← Category.assoc]
      change (singularChainPostcompose (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) ≫
        barycentricSubdivision X) ≫ relativeSingularProjection X A = 0
      rw [← barycentricSubdivision_postcompose, Category.assoc]
      change barycentricSubdivision A ≫
        (subspaceSingularChainMap X A ≫ relativeSingularProjection X A) = 0
      rw [subspaceSingularChainMap_projection, Limits.comp_zero]))

theorem relativeSingularProjection_subdivision (X : Type u) [TopologicalSpace X] (A : Set X) :
    relativeSingularProjection X A ≫ relativeBarycentricSubdivision X A =
      barycentricSubdivision X ≫ relativeSingularProjection X A :=
  Limits.Cofork.IsColimit.π_desc
    ((singularPair X A).isColimitCokernelCoforkChainComplex realHomologyCoefficients)

/-- The natural support-preserving homotopy descends degreewise to the actual
relative chain cokernel, rather than being postulated as relative data. -/
def relativeSubdivisionHomotopyDegree (X : Type u) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (relativeSingularChains X A).X n ⟶ (relativeSingularChains X A).X (n + 1) :=
  ((singularPair X A).isColimitCokernelCoforkChainComplexX realHomologyCoefficients n).desc
    (Limits.CokernelCofork.ofπ
      (subdivisionHomotopyDegree n X ≫ (relativeSingularProjection X A).f (n + 1)) (by
        change (subspaceSingularChainMap X A).f n ≫
          (subdivisionHomotopyDegree n X ≫ (relativeSingularProjection X A).f (n + 1)) = 0
        rw [← Category.assoc]
        change ((singularChainPostcompose (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).f n ≫
          subdivisionHomotopyDegree n X) ≫ (relativeSingularProjection X A).f (n + 1) = 0
        rw [← subdivisionHomotopyDegree_postcompose, Category.assoc]
        change subdivisionHomotopyDegree n A ≫
          ((subspaceSingularChainMap X A).f (n + 1) ≫
            (relativeSingularProjection X A).f (n + 1)) = 0
        rw [← HomologicalComplex.comp_f, subspaceSingularChainMap_projection,
          HomologicalComplex.zero_f, Limits.comp_zero]))

theorem relativeSingularProjection_homotopyDegree (X : Type u) [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    (relativeSingularProjection X A).f n ≫ relativeSubdivisionHomotopyDegree X A n =
      subdivisionHomotopyDegree n X ≫ (relativeSingularProjection X A).f (n + 1) :=
  Limits.Cofork.IsColimit.π_desc
    ((singularPair X A).isColimitCokernelCoforkChainComplexX realHomologyCoefficients n)

def relativeSubdivisionHomotopyLowerTerm (X : Type u) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (relativeSingularChains X A).X n ⟶ (relativeSingularChains X A).X n := match n with
  | 0 => 0
  | n + 1 => (relativeSingularChains X A).d (n + 1) n ≫ relativeSubdivisionHomotopyDegree X A n

theorem relativeSingularProjection_lowerTerm (X : Type u) [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    (relativeSingularProjection X A).f n ≫ relativeSubdivisionHomotopyLowerTerm X A n =
      subdivisionHomotopyLowerTerm n X ≫ (relativeSingularProjection X A).f n := by
  cases n with
  | zero => simp [relativeSubdivisionHomotopyLowerTerm, subdivisionHomotopyLowerTerm]
  | succ n =>
    rw [relativeSubdivisionHomotopyLowerTerm, subdivisionHomotopyLowerTerm,
      ← Category.assoc, (relativeSingularProjection X A).comm (n + 1) n,
      Category.assoc, relativeSingularProjection_homotopyDegree, ← Category.assoc]

theorem relativeSubdivisionHomotopyDegree_boundary (X : Type u) [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    relativeSubdivisionHomotopyDegree X A n ≫ (relativeSingularChains X A).d (n + 1) n +
      relativeSubdivisionHomotopyLowerTerm X A n = (relativeBarycentricSubdivision X A).f n - 𝟙 _ := by
  have : Epi ((relativeSingularProjection X A).f n) :=
    inferInstanceAs (Epi (((singularPair X A).chainComplexπ realHomologyCoefficients).f n))
  have hs := congrArg (fun f ↦ f.f n) (relativeSingularProjection_subdivision X A)
  simp only [HomologicalComplex.comp_f, barycentricSubdivision_f] at hs
  have hd : (relativeSingularProjection X A).f n ≫
      (relativeSubdivisionHomotopyDegree X A n ≫ (relativeSingularChains X A).d (n + 1) n) =
      (subdivisionHomotopyDegree n X ≫ (singularChains X).d (n + 1) n) ≫
        (relativeSingularProjection X A).f n := by
    rw [← Category.assoc, relativeSingularProjection_homotopyDegree, Category.assoc,
      (relativeSingularProjection X A).comm (n + 1) n, ← Category.assoc]
  apply (cancel_epi ((relativeSingularProjection X A).f n)).mp
  rw [Preadditive.comp_add, hd, relativeSingularProjection_lowerTerm,
    ← Preadditive.add_comp, subdivisionHomotopyDegree_boundary,
    Preadditive.sub_comp, Category.id_comp,
    Preadditive.comp_sub, hs, Category.comp_id]

def relativeSubdivisionHomotopyHom (X : Type u) [TopologicalSpace X] (A : Set X) (i j : ℕ) :
    (relativeSingularChains X A).X i ⟶ (relativeSingularChains X A).X j :=
  if h : i + 1 = j then relativeSubdivisionHomotopyDegree X A i ≫
    eqToHom (congrArg (relativeSingularChains X A).X h) else 0

@[simp]
theorem relativeSubdivisionHomotopyHom_succ (X : Type u) [TopologicalSpace X]
    (A : Set X) (i : ℕ) :
    relativeSubdivisionHomotopyHom X A i (i + 1) = relativeSubdivisionHomotopyDegree X A i := by
  simp [relativeSubdivisionHomotopyHom]

/-- The support-preserving subdivision homotopy on every actual relative pair. -/
def relativeBarycentricSubdivisionHomotopy (X : Type u) [TopologicalSpace X] (A : Set X) :
    Homotopy (relativeBarycentricSubdivision X A) (𝟙 (relativeSingularChains X A)) where
  hom := relativeSubdivisionHomotopyHom X A
  zero i j h := by
    have h' : ¬ i + 1 = j := by simpa only [ComplexShape.down_Rel] using h
    simp [relativeSubdivisionHomotopyHom, h']
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [relativeSubdivisionHomotopyHom_succ, zero_add, HomologicalComplex.id_f]
      have h := relativeSubdivisionHomotopyDegree_boundary X A 0
      simp only [relativeSubdivisionHomotopyLowerTerm, add_zero] at h
      exact ((eq_sub_iff_add_eq).mp h).symm
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [relativeSubdivisionHomotopyHom_succ, HomologicalComplex.id_f]
      have h := relativeSubdivisionHomotopyDegree_boundary X A (n + 1)
      simp only [relativeSubdivisionHomotopyLowerTerm] at h
      calc
        _ = (relativeSubdivisionHomotopyDegree X A (n + 1) ≫
            (relativeSingularChains X A).d (n + 2) (n + 1) +
            (relativeSingularChains X A).d (n + 1) n ≫ relativeSubdivisionHomotopyDegree X A n) + 𝟙 _ :=
          ((eq_sub_iff_add_eq).mp h).symm
        _ = _ := congrArg (fun f ↦ f + 𝟙 _) (add_comm
          (relativeSubdivisionHomotopyDegree X A (n + 1) ≫
            (relativeSingularChains X A).d (n + 2) (n + 1))
          ((relativeSingularChains X A).d (n + 1) n ≫ relativeSubdivisionHomotopyDegree X A n))

theorem relativeBarycentricSubdivision_homologyMap (X : Type u) [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeBarycentricSubdivision X A) n = 𝟙 _ := by
  rw [(relativeBarycentricSubdivisionHomotopy X A).homologyMap_eq,
    HomologicalComplex.homologyMap_id]

theorem singularChainCoordinatesIso_hom_generator {X : Type u} [TopologicalSpace X]
    {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 1)), X)) (a : ULift.{u} ℝ) :
    (singularChainCoordinatesIso X n).hom (singularSimplexGenerator s a) =
      Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).symm s) a := by
  let e := singularChainCoordinatesIso X n
  apply (ModuleCat.mono_iff_injective e.inv).mp inferInstance
  have h := singularChainCoordinatesIso_inv_single X n
    ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).symm s) a
  change e.inv (e.hom (singularSimplexGenerator s a)) = _
  rw [← ModuleCat.comp_apply, e.hom_inv_id]
  exact h.symm

def singularSimplexSubsetSet (X : Type u) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    Set ((TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌)) :=
  {t | Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌) t) ⊆ A}

def subspaceSupportedChains (X : Type u) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    Submodule ℝ ((singularChains X).X n) :=
  (Finsupp.supported (ULift.{u} ℝ) ℝ (singularSimplexSubsetSet X A n)).comap
    (singularChainCoordinatesIso X n).hom.hom

theorem singularSimplexGenerator_mem_subspaceSupported {X : Type u} [TopologicalSpace X]
    {n : ℕ} (A : Set X) (s : C(StdSimplex ℝ (Fin (n + 1)), X))
    (hs : Set.range s ⊆ A) (a : ULift.{u} ℝ) :
    singularSimplexGenerator s a ∈ subspaceSupportedChains X A n := by
  change (singularChainCoordinatesIso X n).hom (singularSimplexGenerator s a) ∈
    Finsupp.supported (ULift.{u} ℝ) ℝ (singularSimplexSubsetSet X A n)
  rw [singularChainCoordinatesIso_hom_generator]
  apply Finsupp.single_mem_supported ℝ a
  change Set.range ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌))
    ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).symm s)) ⊆ A
  simpa only [Equiv.apply_symm_apply] using hs

/-- The image of actual subspace chains is precisely the support condition in
the proved coordinates of the actual ambient singular-chain coproduct. -/
theorem subspaceSingularChainMap_range_eq_supported (X : Type u) [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    LinearMap.range ((subspaceSingularChainMap X A).f n).hom = subspaceSupportedChains X A n := by
  classical
  apply le_antisymm
  · intro z hz
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨c, hc⟩ := singularChain_eq_finite_sum A n a
    rw [hc]
    simp only [map_sum]
    apply Submodule.sum_mem
    intro t _
    change (singularSimplexGenerator (TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op ⦋n⦌) t) ≫
      (singularChainPostcompose (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).f n) (c t) ∈ _
    rw [singularSimplexGenerator_postcompose]
    apply singularSimplexGenerator_mem_subspaceSupported
    rintro _ ⟨x, rfl⟩
    exact (TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op ⦋n⦌) t x).property
  · intro z hz
    obtain ⟨c, hc⟩ := singularChain_eq_finite_sum X n z
    have hcoord : (singularChainCoordinatesIso X n).hom z = c := by
      rw [hc]
      simp only [map_sum]
      calc
        _ = ∑ t ∈ c.support, Finsupp.single t (c t) := by
          apply Finset.sum_congr rfl
          intro t _
          simpa only [Equiv.symm_apply_apply] using
            singularChainCoordinatesIso_hom_generator (n := n)
              (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌) t) (c t)
        _ = c := c.sum_single
    change (singularChainCoordinatesIso X n).hom z ∈
      Finsupp.supported (ULift.{u} ℝ) ℝ (singularSimplexSubsetSet X A n) at hz
    rw [hcoord, Finsupp.mem_supported] at hz
    rw [hc]
    apply Submodule.sum_mem
    intro t ht
    exact singularSimplexGenerator_mem_subspaceRange A _ (hz ht) _

theorem singularSimplexSubsetSet_inter (X : Type u) [TopologicalSpace X]
    (A B : Set X) (n : ℕ) :
    singularSimplexSubsetSet X (A ∩ B) n =
      singularSimplexSubsetSet X A n ∩ singularSimplexSubsetSet X B n := by
  ext t
  exact Set.subset_inter_iff

/-- Exact intersection of actual subspace chain images, proved from actual
singular coproduct coordinates. -/
theorem subspaceSingularChainMap_range_inter (X : Type u) [TopologicalSpace X]
    (A B : Set X) (n : ℕ) :
    LinearMap.range ((subspaceSingularChainMap X A).f n).hom ⊓
      LinearMap.range ((subspaceSingularChainMap X B).f n).hom =
        LinearMap.range ((subspaceSingularChainMap X (A ∩ B)).f n).hom := by
  rw [subspaceSingularChainMap_range_eq_supported, subspaceSingularChainMap_range_eq_supported,
    subspaceSingularChainMap_range_eq_supported]
  unfold subspaceSupportedChains
  rw [← Submodule.comap_inf, ← Finsupp.supported_inter, ← singularSimplexSubsetSet_inter]

instance subspaceSingularChainMap_f_mono (X : Type u) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    Mono ((subspaceSingularChainMap X A).f n) :=
  inferInstanceAs (Mono ((SSet.chainComplexMap (singularPair X A).hom realHomologyCoefficients).f n))

theorem relativeSingularProjection_eq_zero_iff (X : Type u) [TopologicalSpace X]
    (A : Set X) (n : ℕ) (x : (singularChains X).X n) :
    (relativeSingularProjection X A).f n x = 0 ↔
      ∃ a : (singularChains A).X n, (subspaceSingularChainMap X A).f n a = x := by
  let S : ShortComplex (ModuleCat.{u} ℝ) := ShortComplex.mk
    ((subspaceSingularChainMap X A).f n) ((relativeSingularProjection X A).f n)
      ((singularPair X A).chainComplex_condition_f realHomologyCoefficients n)
  have hs : S.Exact := S.exact_of_g_is_cokernel
    ((singularPair X A).isColimitCokernelCoforkChainComplexX realHomologyCoefficients n)
  constructor
  · exact S.moduleCat_exact_iff.mp hs x
  · rintro ⟨a, rfl⟩
    exact S.moduleCat_zero_apply a

theorem relativeExcisionChainMap_projection (X : Type u) [TopologicalSpace X] (A Z : Set X) :
    relativeSingularProjection (Zᶜ : Set X) (excisionSourceSubset X A Z) ≫
        relativeExcisionChainMap X A Z =
      subspaceSingularChainMap X Zᶜ ≫ relativeSingularProjection X A :=
  (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℝ)).app realHomologyCoefficients).naturality
    (excisionPairMap X A Z)).symm

def intersectionToExcisionSource (X : Type u) [TopologicalSpace X] (A Z : Set X) :
    C((A ∩ Zᶜ : Set X), excisionSourceSubset X A Z) :=
  ⟨fun x ↦ ⟨⟨x.val, x.property.2⟩, x.property.1⟩,
    (continuous_subtype_val.subtype_mk _).subtype_mk _⟩

theorem intersectionToExcisionSource_chainMap (X : Type u) [TopologicalSpace X]
    (A Z : Set X) :
    singularChainPostcompose (intersectionToExcisionSource X A Z) ≫
        subspaceSingularChainMap (Zᶜ : Set X) (excisionSourceSubset X A Z) ≫
          subspaceSingularChainMap X Zᶜ = subspaceSingularChainMap X (A ∩ Zᶜ) := by
  change singularChainPostcompose (intersectionToExcisionSource X A Z) ≫
      singularChainPostcompose (⟨Subtype.val, continuous_subtype_val⟩ :
        C(excisionSourceSubset X A Z, (Zᶜ : Set X))) ≫
      singularChainPostcompose (⟨Subtype.val, continuous_subtype_val⟩ : C((Zᶜ : Set X), X)) =
    singularChainPostcompose (⟨Subtype.val, continuous_subtype_val⟩ : C((A ∩ Zᶜ : Set X), X))
  rw [← Category.assoc, singularChainPostcompose_comp, singularChainPostcompose_comp]
  rfl

/-- The actual relative excision chain map is injective in each degree. This is
proved from the exact intersection of actual subspace chain images. -/
theorem relativeExcisionChainMap_f_injective (X : Type u) [TopologicalSpace X]
    (A Z : Set X) (n : ℕ) : Function.Injective ((relativeExcisionChainMap X A Z).f n) := by
  have hzero (z : (relativeSingularChains (Zᶜ : Set X) (excisionSourceSubset X A Z)).X n)
      (hz : (relativeExcisionChainMap X A Z).f n z = 0) : z = 0 := by
    obtain ⟨b, hb⟩ := relativeSingularProjection_lift (Zᶜ : Set X) (excisionSourceSubset X A Z) n z
    have hp := congrArg (fun f ↦ f b) (congrArg (fun f ↦ f.f n)
      (relativeExcisionChainMap_projection X A Z))
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, hb] at hp
    obtain ⟨a, ha⟩ := (relativeSingularProjection_eq_zero_iff X A n _).mp (hp.symm.trans hz)
    have hi : (subspaceSingularChainMap X Zᶜ).f n b ∈
        LinearMap.range ((subspaceSingularChainMap X A).f n).hom ⊓
          LinearMap.range ((subspaceSingularChainMap X Zᶜ).f n).hom :=
      ⟨⟨a, ha⟩, ⟨b, rfl⟩⟩
    rw [subspaceSingularChainMap_range_inter] at hi
    obtain ⟨c, hc⟩ := hi
    let a' := (singularChainPostcompose (intersectionToExcisionSource X A Z)).f n c
    have hm := congrArg (fun f ↦ f c) (congrArg (fun f ↦ f.f n)
      (intersectionToExcisionSource_chainMap X A Z))
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hm
    have hb' : (subspaceSingularChainMap (Zᶜ : Set X) (excisionSourceSubset X A Z)).f n a' = b :=
      (ModuleCat.mono_iff_injective ((subspaceSingularChainMap X Zᶜ).f n)).mp inferInstance (hm.trans hc)
    have hq := congrArg (fun f ↦ f a') (congrArg (fun f ↦ f.f n)
      (subspaceSingularChainMap_projection (Zᶜ : Set X) (excisionSourceSubset X A Z)))
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, ModuleCat.comp_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply, hb'] at hq
    exact hb.symm.trans hq
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hxy, sub_self]

def iteratedRelativeSubdivision (X : Type u) [TopologicalSpace X] (A : Set X) (k : ℕ) :
    relativeSingularChains X A ⟶ relativeSingularChains X A := match k with
  | 0 => 𝟙 _
  | k + 1 => relativeBarycentricSubdivision X A ≫ iteratedRelativeSubdivision X A k

def iteratedRelativeSubdivisionHomotopy (X : Type u) [TopologicalSpace X] (A : Set X) (k : ℕ) :
    Homotopy (iteratedRelativeSubdivision X A k) (𝟙 (relativeSingularChains X A)) := match k with
  | 0 => Homotopy.refl _
  | k + 1 => ((relativeBarycentricSubdivisionHomotopy X A).compRightId
      (iteratedRelativeSubdivision X A k)).trans (iteratedRelativeSubdivisionHomotopy X A k)

theorem relativeSingularProjection_iteratedSubdivision (X : Type u) [TopologicalSpace X]
    (A : Set X) (k : ℕ) :
    relativeSingularProjection X A ≫ iteratedRelativeSubdivision X A k =
      iteratedSubdivision X k ≫ relativeSingularProjection X A := by
  induction k with
  | zero => simp [iteratedSubdivision, iteratedRelativeSubdivision]
  | succ k ih =>
    rw [iteratedSubdivision, iteratedRelativeSubdivision, ← Category.assoc,
      relativeSingularProjection_subdivision, Category.assoc, ih, ← Category.assoc]

theorem relativeExcisionChainMap_subdivision (X : Type u) [TopologicalSpace X] (A Z : Set X) :
    relativeExcisionChainMap X A Z ≫ relativeBarycentricSubdivision X A =
      relativeBarycentricSubdivision (Zᶜ : Set X) (excisionSourceSubset X A Z) ≫
        relativeExcisionChainMap X A Z := by
  have : Epi (relativeSingularProjection (Zᶜ : Set X) (excisionSourceSubset X A Z)) :=
    inferInstanceAs (Epi ((singularPair (Zᶜ : Set X) (excisionSourceSubset X A Z)).chainComplexπ
      realHomologyCoefficients))
  apply (cancel_epi (relativeSingularProjection (Zᶜ : Set X) (excisionSourceSubset X A Z))).mp
  rw [← Category.assoc, relativeExcisionChainMap_projection, Category.assoc,
    relativeSingularProjection_subdivision, ← Category.assoc]
  change (singularChainPostcompose (⟨Subtype.val, continuous_subtype_val⟩ : C((Zᶜ : Set X), X)) ≫
      barycentricSubdivision X) ≫ relativeSingularProjection X A = _
  rw [← barycentricSubdivision_postcompose, Category.assoc]
  change barycentricSubdivision (Zᶜ : Set X) ≫
      (subspaceSingularChainMap X Zᶜ ≫ relativeSingularProjection X A) = _
  rw [← relativeExcisionChainMap_projection, ← Category.assoc,
    ← relativeSingularProjection_subdivision, Category.assoc]

theorem relativeExcisionChainMap_iteratedSubdivision (X : Type u) [TopologicalSpace X]
    (A Z : Set X) (k : ℕ) :
    relativeExcisionChainMap X A Z ≫ iteratedRelativeSubdivision X A k =
      iteratedRelativeSubdivision (Zᶜ : Set X) (excisionSourceSubset X A Z) k ≫
        relativeExcisionChainMap X A Z := by
  induction k with
  | zero => simp [iteratedRelativeSubdivision]
  | succ k ih =>
    rw [iteratedRelativeSubdivision, iteratedRelativeSubdivision, ← Category.assoc,
      relativeExcisionChainMap_subdivision, Category.assoc, ih, ← Category.assoc]

theorem iteratedRelativeSubdivisionHomotopy_cycle_boundary (X : Type u) [TopologicalSpace X]
    (A : Set X) (k n : ℕ) (z : (relativeSingularChains X A).X n)
    (hz : (relativeSingularChains X A).d n (n - 1) z = 0) :
    (relativeSingularChains X A).d (n + 1) n
        ((iteratedRelativeSubdivisionHomotopy X A k).hom n (n + 1) z) =
      (iteratedRelativeSubdivision X A k).f n z - z := by
  have h := (iteratedRelativeSubdivisionHomotopy X A k).comm n
  rw [dNext_nat, Homotopy.prevD_chainComplex] at h
  have hv := congrArg (fun f ↦ f z) h
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
    hz, map_zero, zero_add, HomologicalComplex.id_f, ModuleCat.id_apply] at hv
  exact eq_sub_of_add_eq hv.symm

theorem relativeChain_eventually_excision_image (X : Type u) [TopologicalSpace X]
    (A Z : Set X) (hZ : closure Z ⊆ interior A) (n : ℕ)
    (z : (relativeSingularChains X A).X n) :
    ∃ k : ℕ, ∀ l ≥ k,
      ∃ b : (relativeSingularChains (Zᶜ : Set X) (excisionSourceSubset X A Z)).X n,
        (iteratedRelativeSubdivision X A l).f n z = (relativeExcisionChainMap X A Z).f n b := by
  obtain ⟨x, hx⟩ := relativeSingularProjection_lift X A n z
  obtain ⟨k, hk⟩ := singularChain_eventually_excision_decomposition X A Z hZ n x
  refine ⟨k, fun l hl ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := hk l hl
  refine ⟨(relativeSingularProjection (Zᶜ : Set X) (excisionSourceSubset X A Z)).f n b, ?_⟩
  have hp := congrArg (fun f ↦ f x) (congrArg (fun f ↦ f.f n)
    (relativeSingularProjection_iteratedSubdivision X A l))
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, hx] at hp
  rw [hab, map_add] at hp
  have hA := congrArg (fun f ↦ f a) (congrArg (fun f ↦ f.f n)
    (subspaceSingularChainMap_projection X A))
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, ModuleCat.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] at hA
  rw [hA, zero_add] at hp
  have hE := congrArg (fun f ↦ f b) (congrArg (fun f ↦ f.f n)
    (relativeExcisionChainMap_projection X A Z))
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hE
  exact hp.trans hE.symm

/-- Actual-pair singular excision in all degrees, under the original closure
condition. The map is the functorial inclusion `(X \ Z,A \ Z) → (X,A)`. -/
theorem relativeExcisionChainMap_quasiIso (X : Type u) [TopologicalSpace X]
    (A Z : Set X) (hZ : closure Z ⊆ interior A) : QuasiIso (relativeExcisionChainMap X A Z) := by
  constructor
  intro n
  apply (quasiIsoAt_iff' (relativeExcisionChainMap X A Z) (n + 1) n (n - 1)
    (by simp) (by cases n <;> simp)).mpr
  apply moduleShortComplex_quasiIso_of_cycle_lift
  · change ∀ z : (relativeSingularChains X A).X n,
      (relativeSingularChains X A).d n (n - 1) z = 0 →
        ∃ z' : (relativeSingularChains (Zᶜ : Set X) (excisionSourceSubset X A Z)).X n,
          (relativeSingularChains (Zᶜ : Set X) (excisionSourceSubset X A Z)).d n (n - 1) z' = 0 ∧
          ∃ w : (relativeSingularChains X A).X (n + 1),
            (relativeSingularChains X A).d (n + 1) n w = (relativeExcisionChainMap X A Z).f n z' - z
    intro z hz
    obtain ⟨k, hk⟩ := relativeChain_eventually_excision_image X A Z hZ n z
    obtain ⟨z', himage⟩ := hk k (le_refl _)
    have hcycle : (relativeSingularChains X A).d n (n - 1)
        ((iteratedRelativeSubdivision X A k).f n z) = 0 := by
      have h := congrArg (fun f ↦ f z) ((iteratedRelativeSubdivision X A k).comm n (n - 1))
      simpa only [ModuleCat.comp_apply, hz, map_zero] using h
    have hz' : (relativeSingularChains (Zᶜ : Set X) (excisionSourceSubset X A Z)).d n (n - 1) z' = 0 := by
      apply relativeExcisionChainMap_f_injective X A Z (n - 1)
      have h := congrArg (fun f ↦ f z') ((relativeExcisionChainMap X A Z).comm n (n - 1))
      simp only [ModuleCat.comp_apply] at h
      rw [← himage, hcycle] at h
      simpa only [map_zero] using h.symm
    refine ⟨z', hz', (iteratedRelativeSubdivisionHomotopy X A k).hom n (n + 1) z, ?_⟩
    rw [iteratedRelativeSubdivisionHomotopy_cycle_boundary X A k n z hz, himage]
  · change ∀ z : (relativeSingularChains (Zᶜ : Set X) (excisionSourceSubset X A Z)).X n,
      (relativeSingularChains (Zᶜ : Set X) (excisionSourceSubset X A Z)).d n (n - 1) z = 0 →
      ∀ w : (relativeSingularChains X A).X (n + 1),
        (relativeSingularChains X A).d (n + 1) n w = (relativeExcisionChainMap X A Z).f n z →
        ∃ v : (relativeSingularChains (Zᶜ : Set X) (excisionSourceSubset X A Z)).X (n + 1),
          (relativeSingularChains (Zᶜ : Set X) (excisionSourceSubset X A Z)).d (n + 1) n v = z
    intro z hz w hw
    obtain ⟨k, hk⟩ := relativeChain_eventually_excision_image X A Z hZ (n + 1) w
    obtain ⟨v, himage⟩ := hk k (le_refl _)
    have hd : (relativeSingularChains (Zᶜ : Set X) (excisionSourceSubset X A Z)).d (n + 1) n v =
        (iteratedRelativeSubdivision (Zᶜ : Set X) (excisionSourceSubset X A Z) k).f n z := by
      apply relativeExcisionChainMap_f_injective X A Z n
      have hE := congrArg (fun f ↦ f v) ((relativeExcisionChainMap X A Z).comm (n + 1) n)
      simp only [ModuleCat.comp_apply] at hE
      have hT := congrArg (fun f ↦ f w) ((iteratedRelativeSubdivision X A k).comm (n + 1) n)
      simp only [ModuleCat.comp_apply, hw] at hT
      have hN := congrArg (fun f ↦ f z) (congrArg (fun f ↦ f.f n)
        (relativeExcisionChainMap_iteratedSubdivision X A Z k))
      simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hN
      exact hE.symm.trans ((congrArg ((relativeSingularChains X A).d (n + 1) n) himage.symm).trans
        (hT.trans hN))
    refine ⟨v - (iteratedRelativeSubdivisionHomotopy (Zᶜ : Set X) (excisionSourceSubset X A Z) k).hom n (n + 1) z, ?_⟩
    rw [map_sub, hd, iteratedRelativeSubdivisionHomotopy_cycle_boundary
      (Zᶜ : Set X) (excisionSourceSubset X A Z) k n z hz, sub_sub_cancel]

/-- The actual excision isomorphism on the project's relative real singular homology. -/
def relativeExcisionHomologyIso (X : Type u) [TopologicalSpace X]
    (A Z : Set X) (hZ : closure Z ⊆ interior A) (n : ℕ) :
    relativeSingularHomology (Zᶜ : Set X) (excisionSourceSubset X A Z) n ≅
      relativeSingularHomology X A n := by
  have : QuasiIso (relativeExcisionChainMap X A Z) := relativeExcisionChainMap_quasiIso X A Z hZ
  exact asIso (HomologicalComplex.homologyMap (relativeExcisionChainMap X A Z) n)

end GaussBonnetChern
