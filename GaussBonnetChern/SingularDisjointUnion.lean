import GaussBonnetChern.MorseHandleAttachment
import GaussBonnetChern.DiskPairHomology
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

noncomputable section
universe u
namespace GaussBonnetChern
open CategoryTheory CategoryTheory.Limits HomologicalComplex Convexity
open scoped Simplicial DirectSum

variable {ι : Type u} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

set_option backward.isDefEq.respectTransparency false in
theorem singularChains_degree_hom_ext {T : Type u} [TopologicalSpace T]
    {n : ℕ} {V : ModuleCat.{u} ℝ} {f g : (singularChains T).X n ⟶ V}
    (h : ∀ s : C(StdSimplex ℝ (Fin (n + 1)), T),
      singularSimplexGenerator s ≫ f = singularSimplexGenerator s ≫ g) : f = g := by
  apply SSet.chainComplex_hom_ext
  intro t
  simpa only [singularSimplexGenerator, Equiv.symm_apply_apply] using
    h ((TopCat.toSSetObjEquiv (TopCat.of T) (Opposite.op ⦋n⦌)) t)

def sigmaSingularSimplexEquiv (n : ℕ) :
    C(StdSimplex ℝ (Fin (n + 1)), Σ i, X i) ≃ Σ i, C(StdSimplex ℝ (Fin (n + 1)), X i) :=
  (ContinuousMap.sigmaCodHomeomorph _ X).toEquiv

@[simp]
theorem sigmaSingularSimplexEquiv_sigmaMk (n : ℕ) (i : ι)
    (s : C(StdSimplex ℝ (Fin (n + 1)), X i)) :
    sigmaSingularSimplexEquiv X n ((ContinuousMap.sigmaMk i).comp s) = ⟨i, s⟩ :=
  (sigmaSingularSimplexEquiv X n).apply_symm_apply ⟨i, s⟩

def sigmaSingularChainsCofan : Cofan (fun i ↦ singularChains (X i)) :=
  Cofan.mk (singularChains (Σ i, X i))
    (fun i ↦ singularChainPostcompose (ContinuousMap.sigmaMk i))

def sigmaSingularChainDegreeDesc (n : ℕ)
    (s : Cocone (Discrete.functor (fun i ↦ singularChains (X i)) ⋙
      HomologicalComplex.eval (ModuleCat.{u} ℝ) (ComplexShape.down ℕ) n)) :
    (singularChains (Σ i, X i)).X n ⟶ s.pt :=
  Sigma.desc (fun t ↦
    let q := sigmaSingularSimplexEquiv X n
      (TopCat.toSSetObjEquiv (TopCat.of (Σ i, X i)) (Opposite.op ⦋n⦌) t)
    singularSimplexGenerator q.2 ≫ s.ι.app ⟨q.1⟩)

set_option backward.isDefEq.respectTransparency false in
theorem singularSimplexGenerator_sigmaDegreeDesc (n : ℕ)
    (s : Cocone (Discrete.functor (fun i ↦ singularChains (X i)) ⋙
      HomologicalComplex.eval (ModuleCat.{u} ℝ) (ComplexShape.down ℕ) n))
    (t : C(StdSimplex ℝ (Fin (n + 1)), Σ i, X i)) :
    singularSimplexGenerator t ≫ sigmaSingularChainDegreeDesc X n s =
      let q := sigmaSingularSimplexEquiv X n t
      singularSimplexGenerator q.2 ≫ s.ι.app ⟨q.1⟩ := by
  simp only [singularSimplexGenerator, sigmaSingularChainDegreeDesc, SSet.ιChainComplex]
  rw [Sigma.ι_comp_desc]
  rw [Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
def sigmaSingularChainsCofanIsColimit : IsColimit (sigmaSingularChainsCofan X) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  refine ⟨sigmaSingularChainDegreeDesc X n, ?_, ?_⟩
  · intro s i
    apply singularChains_degree_hom_ext
    intro t
    change singularSimplexGenerator t ≫
      ((singularChainPostcompose (ContinuousMap.sigmaMk i.as)).f n ≫
        sigmaSingularChainDegreeDesc X n s) = singularSimplexGenerator t ≫ s.ι.app i
    rw [← Category.assoc, singularSimplexGenerator_postcompose,
      singularSimplexGenerator_sigmaDegreeDesc, sigmaSingularSimplexEquiv_sigmaMk]
  · intro s m hm
    apply singularChains_degree_hom_ext
    intro t
    obtain ⟨q, hq⟩ := (sigmaSingularSimplexEquiv X n).symm.surjective t
    rcases q with ⟨i, t⟩
    subst hq
    change singularSimplexGenerator ((ContinuousMap.sigmaMk i).comp t) ≫ m = _
    rw [singularSimplexGenerator_sigmaDegreeDesc, Equiv.apply_symm_apply]
    dsimp only
    rw [← singularSimplexGenerator_postcompose, Category.assoc]
    exact congrArg (fun f ↦ singularSimplexGenerator t ≫ f) (hm ⟨i⟩)

/-- Actual singular chains of a disjoint union are the coproduct of the
component chains, proved using connectedness of every topological simplex. -/
def singularChainsSigmaIso : singularChains (Σ i, X i) ≅ ∐ (fun i : ι ↦ singularChains (X i)) :=
  (sigmaSingularChainsCofanIsColimit X).coconePointUniqueUpToIso (coproductIsCoproduct _)

def singularHomologySigmaIso [Finite ι] (k : ℕ) :
    singularHomology (Σ i, X i) k ≅ ModuleCat.of ℝ (⨁ i, singularHomology (X i) k) := by
  classical
  exact (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℝ) (ComplexShape.down ℕ) k).mapIso
      (singularChainsSigmaIso X) ≪≫
    PreservesCoproduct.iso (HomologicalComplex.homologyFunctor
      (ModuleCat.{u} ℝ) (ComplexShape.down ℕ) k) (fun i ↦ singularChains (X i)) ≪≫
    ModuleCat.coprodIsoDirectSum (fun i ↦ singularHomology (X i) k)

end GaussBonnetChern



noncomputable section
namespace GaussBonnetChern
open CategoryTheory CategoryTheory.Limits HomologicalComplex Convexity
open scoped Simplicial DirectSum

variable {ι : Type u} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
  (A : ∀ i, Set (X i))

instance relativeSingularProjection_epi (T : Type u) [TopologicalSpace T] (B : Set T) :
    Epi (relativeSingularProjection T B) :=
  inferInstanceAs (Epi ((singularPair T B).chainComplexπ realHomologyCoefficients))

/-- The actual attaching subset in a topological disjoint union. -/
def sigmaPairSubset : Set (Σ i, X i) := {x | x.2 ∈ A x.1}

def sigmaPairInclusion (i : ι) : C(A i, sigmaPairSubset X A) :=
  continuousMapOfPair (ContinuousMap.sigmaMk i) (fun _ h ↦ h)

set_option backward.isDefEq.respectTransparency false in
theorem sigmaPairInclusion_chains_hom_ext
    {K : ChainComplex (ModuleCat.{u} ℝ) ℕ}
    {f g : singularChains (sigmaPairSubset X A) ⟶ K}
    (h : ∀ i, singularChainPostcompose (sigmaPairInclusion X A i) ≫ f =
      singularChainPostcompose (sigmaPairInclusion X A i) ≫ g) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply singularChains_degree_hom_ext
  intro t
  let s : C(StdSimplex ℝ (Fin (n + 1)), Σ i, X i) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(sigmaPairSubset X A, Σ i, X i)).comp t
  obtain ⟨i, v, hv⟩ := s.exists_lift_sigma
  have hmem (x : StdSimplex ℝ (Fin (n + 1))) : v x ∈ A i := by
    have ht := (t x).property
    change (s x).2 ∈ A (s x).1 at ht
    rw [hv] at ht
    exact ht
  let a : C(StdSimplex ℝ (Fin (n + 1)), A i) :=
    ⟨fun x ↦ ⟨v x, hmem x⟩, v.continuous.subtype_mk _⟩
  have ht : t = (sigmaPairInclusion X A i).comp a := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun q ↦ q x) hv
  rw [ht, ← singularSimplexGenerator_postcompose, Category.assoc, Category.assoc]
  exact congrArg (fun m ↦ singularSimplexGenerator a ≫ m.f n) (h i)

def sigmaRelativeChainsCofan : Cofan (fun i ↦ relativeSingularChains (X i) (A i)) :=
  Cofan.mk (relativeSingularChains (Σ i, X i) (sigmaPairSubset X A))
    (fun i ↦ relativeSingularChainsMap (ContinuousMap.sigmaMk i) (fun _ h ↦ h))

def sigmaRelativeAbsoluteDesc
    (s : Cofan (fun i ↦ relativeSingularChains (X i) (A i))) :
    singularChains (Σ i, X i) ⟶ s.pt :=
  (sigmaSingularChainsCofanIsColimit X).desc
    (Cofan.mk _ (fun i ↦ relativeSingularProjection (X i) (A i) ≫ s.inj i))

set_option backward.isDefEq.respectTransparency false in
theorem sigmaRelativeAbsoluteDesc_condition
    (s : Cofan (fun i ↦ relativeSingularChains (X i) (A i))) :
    subspaceSingularChainMap (Σ i, X i) (sigmaPairSubset X A) ≫
      sigmaRelativeAbsoluteDesc X A s = 0 := by
  apply sigmaPairInclusion_chains_hom_ext X A
  intro i
  have hcomm :
      singularChainPostcompose (sigmaPairInclusion X A i) ≫
        subspaceSingularChainMap (Σ i, X i) (sigmaPairSubset X A) =
      subspaceSingularChainMap (X i) (A i) ≫
        singularChainPostcompose (ContinuousMap.sigmaMk i) :=
    (singularPairChainSequenceMap (singularPairMap
      (ContinuousMap.sigmaMk i) (show Set.MapsTo _ (A i) (sigmaPairSubset X A) from
        fun _ h ↦ h))).comm₁₂
  rw [← Category.assoc, hcomm, Category.assoc]
  have hd := (sigmaSingularChainsCofanIsColimit X).fac
    (Cofan.mk _ (fun i ↦ relativeSingularProjection (X i) (A i) ≫ s.inj i)) ⟨i⟩
  change singularChainPostcompose (ContinuousMap.sigmaMk i) ≫
    sigmaRelativeAbsoluteDesc X A s = relativeSingularProjection (X i) (A i) ≫ s.inj i at hd
  rw [hd, ← Category.assoc, subspaceSingularChainMap_projection, zero_comp, comp_zero]

def sigmaRelativeChainsDesc
    (s : Cofan (fun i ↦ relativeSingularChains (X i) (A i))) :
    relativeSingularChains (Σ i, X i) (sigmaPairSubset X A) ⟶ s.pt :=
  ((singularPair (Σ i, X i) (sigmaPairSubset X A)).isColimitCokernelCoforkChainComplex
    realHomologyCoefficients).desc
      (CokernelCofork.ofπ (sigmaRelativeAbsoluteDesc X A s)
        (sigmaRelativeAbsoluteDesc_condition X A s))

theorem sigmaRelativeProjection_desc
    (s : Cofan (fun i ↦ relativeSingularChains (X i) (A i))) :
    relativeSingularProjection (Σ i, X i) (sigmaPairSubset X A) ≫
      sigmaRelativeChainsDesc X A s = sigmaRelativeAbsoluteDesc X A s :=
  Cofork.IsColimit.π_desc
    ((singularPair (Σ i, X i) (sigmaPairSubset X A)).isColimitCokernelCoforkChainComplex
      realHomologyCoefficients)

set_option backward.isDefEq.respectTransparency false in
def sigmaRelativeChainsCofanIsColimit : IsColimit (sigmaRelativeChainsCofan X A) := by
  refine Cofan.IsColimit.mk _ (sigmaRelativeChainsDesc X A) ?_ ?_
  · intro s i
    apply (cancel_epi (relativeSingularProjection (X i) (A i))).mp
    have hp := (singularPairChainSequenceMap (singularPairMap
      (ContinuousMap.sigmaMk i) (show Set.MapsTo _ (A i) (sigmaPairSubset X A) from
        fun _ h ↦ h))).comm₂₃
    change singularChainPostcompose (ContinuousMap.sigmaMk i) ≫
      relativeSingularProjection (Σ i, X i) (sigmaPairSubset X A) =
      relativeSingularProjection (X i) (A i) ≫
        (sigmaRelativeChainsCofan X A).inj i at hp
    rw [← Category.assoc, ← hp, Category.assoc, sigmaRelativeProjection_desc]
    exact (sigmaSingularChainsCofanIsColimit X).fac
      (Cofan.mk _ (fun i ↦ relativeSingularProjection (X i) (A i) ≫ s.inj i)) ⟨i⟩
  · intro s m hm
    apply (cancel_epi (relativeSingularProjection (Σ i, X i) (sigmaPairSubset X A))).mp
    rw [sigmaRelativeProjection_desc]
    apply (sigmaSingularChainsCofanIsColimit X).hom_ext
    intro i
    have hp := (singularPairChainSequenceMap (singularPairMap
      (ContinuousMap.sigmaMk i.as) (show Set.MapsTo _ (A i.as) (sigmaPairSubset X A) from
        fun _ h ↦ h))).comm₂₃
    change singularChainPostcompose (ContinuousMap.sigmaMk i.as) ≫
      relativeSingularProjection (Σ i, X i) (sigmaPairSubset X A) =
      relativeSingularProjection (X i.as) (A i.as) ≫
        (sigmaRelativeChainsCofan X A).inj i.as at hp
    change singularChainPostcompose (ContinuousMap.sigmaMk i.as) ≫
      (relativeSingularProjection (Σ i, X i) (sigmaPairSubset X A) ≫ m) = _
    rw [← Category.assoc, hp, Category.assoc, hm]
    exact ((sigmaSingularChainsCofanIsColimit X).fac
      (Cofan.mk _ (fun i ↦ relativeSingularProjection (X i) (A i) ≫ s.inj i)) i).symm

def relativeSingularChainsSigmaIso :
    relativeSingularChains (Σ i, X i) (sigmaPairSubset X A) ≅
      ∐ (fun i : ι ↦ relativeSingularChains (X i) (A i)) :=
  (sigmaRelativeChainsCofanIsColimit X A).coconePointUniqueUpToIso (coproductIsCoproduct _)

def relativeSingularHomologySigmaIso [Finite ι] (k : ℕ) :
    relativeSingularHomology (Σ i, X i) (sigmaPairSubset X A) k ≅
      ModuleCat.of ℝ (⨁ i, relativeSingularHomology (X i) (A i) k) := by
  classical
  exact (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℝ) (ComplexShape.down ℕ) k).mapIso
      (relativeSingularChainsSigmaIso X A) ≪≫
    PreservesCoproduct.iso (HomologicalComplex.homologyFunctor
      (ModuleCat.{u} ℝ) (ComplexShape.down ℕ) k) (fun i ↦ relativeSingularChains (X i) (A i)) ≪≫
    ModuleCat.coprodIsoDirectSum (fun i ↦ relativeSingularHomology (X i) (A i) k)

end GaussBonnetChern



noncomputable section
namespace GaussBonnetChern
open Topology
variable {ι T : Type u} [TopologicalSpace T] (S : ι → Set T)

def sigmaToUnion : C((Σ i, S i), (⋃ i, S i : Set T)) where
  toFun x := ⟨x.2.val, Set.mem_iUnion.mpr ⟨x.1, x.2.property⟩⟩
  continuous_toFun := by
    apply continuous_sigma
    intro i
    exact continuous_subtype_val.subtype_mk _

theorem sigmaToUnion_bijective
    (hdisj : Pairwise (fun i j ↦ Disjoint (S i) (S j))) :
    Function.Bijective (sigmaToUnion S) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have hv : x.val = y.val := congrArg Subtype.val hxy
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hne) x.property (hv ▸ y.property)
    subst j
    have hxy' : x = y := Subtype.ext hv
    subst y
    rfl
  · intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.property
    exact ⟨⟨i, ⟨x.val, hi⟩⟩, rfl⟩

theorem sigmaToUnion_isClosedMap [Finite ι] (hclosed : ∀ i, IsClosed (S i)) :
    IsClosedMap (sigmaToUnion S) := by
  intro A hA
  have hc : IsClosed (⋃ i : ι, (Subtype.val : S i → T) ''
      ((fun x : S i ↦ (⟨i, x⟩ : Σ j, S j)) ⁻¹' A) : Set T) := by
    apply isClosed_iUnion_of_finite
    intro i
    exact (hclosed i).isClosedEmbedding_subtypeVal.isClosedMap _
      (hA.preimage continuous_sigmaMk)
  convert hc.preimage (continuous_subtype_val : Continuous (Subtype.val : (⋃ i, S i : Set T) → T)) using 1
  ext x
  constructor
  · rintro ⟨⟨i, y⟩, hy, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨y, hy, rfl⟩⟩
  · intro hx
    obtain ⟨i, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
    exact ⟨⟨i, y⟩, hy, Subtype.ext hxy⟩

/-- Actual finite disjoint closed union, without compactness of its components. -/
def finiteDisjointClosedUnionHomeomorph [Finite ι] (hclosed : ∀ i, IsClosed (S i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (S i) (S j))) :
    (Σ i, S i) ≃ₜ (⋃ i, S i : Set T) :=
  (Equiv.ofBijective (sigmaToUnion S) (sigmaToUnion_bijective S hdisj)).toHomeomorphOfContinuousClosed
    (sigmaToUnion S).continuous (sigmaToUnion_isClosedMap S hclosed)

@[simp]
theorem finiteDisjointClosedUnionHomeomorph_apply [Finite ι]
    (hclosed : ∀ i, IsClosed (S i)) (hdisj : Pairwise (fun i j ↦ Disjoint (S i) (S j)))
    (x : Σ i, S i) :
    ((finiteDisjointClosedUnionHomeomorph S hclosed hdisj) x).val = x.2.val := rfl

end GaussBonnetChern


noncomputable section
namespace GaussBonnetChern
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

variable {ι T : Type u} [TopologicalSpace T] [Finite ι] (S : ι → Set T)
  (hclosed : ∀ i, IsClosed (S i))
  (hdisj : Pairwise (fun i j ↦ Disjoint (S i) (S j))) (A : Set T)

/-- The disjoint-union homeomorphism respects an actual ambient pair subset. -/
def finiteDisjointClosedUnionPairHomologyIso (k : ℕ) :
    relativeSingularHomology (Σ i, S i)
      (sigmaPairSubset (fun i ↦ S i) (fun i ↦ Subtype.val ⁻¹' A)) k ≅
        relativeSingularHomology (⋃ i, S i : Set T) (Subtype.val ⁻¹' A) k := by
  let e := finiteDisjointClosedUnionHomeomorph S hclosed hdisj
  have hf : Set.MapsTo e.toHomotopyEquiv.toFun
      (sigmaPairSubset (fun i ↦ S i) (fun i ↦ Subtype.val ⁻¹' A))
      (Subtype.val ⁻¹' A) := fun _ h ↦ h
  let b := e.subtype (p := fun x ↦ x.2.val ∈ A) (q := fun x ↦ x.val ∈ A)
    (fun _ ↦ Iff.rfl)
  exact relativeSingularHomologyIsoOfHomotopyEquivs e.toHomotopyEquiv hf b.toHomotopyEquiv rfl k

/-- Relative singular homology of a finite union of disjoint closed subsets
splits into the actual homologies of its restrictions. -/
def finiteDisjointClosedUnionRelativeHomologySigmaIso (k : ℕ) :
    relativeSingularHomology (⋃ i, S i : Set T) (Subtype.val ⁻¹' A) k ≅
      ModuleCat.of ℝ (⨁ i, relativeSingularHomology (S i) (Subtype.val ⁻¹' A) k) := by
  classical
  exact (finiteDisjointClosedUnionPairHomologyIso S hclosed hdisj A k).symm ≪≫
    relativeSingularHomologySigmaIso (fun i ↦ S i) (fun i ↦ Subtype.val ⁻¹' A) k

end GaussBonnetChern

