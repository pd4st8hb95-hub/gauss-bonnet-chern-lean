import GaussBonnetChern.BasicHomology
import GaussBonnetChern.RelativeHomologyCalculations
import GaussBonnetChern.Excision
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

/-! # Homological ingredients for sphere computations

All maps below are induced by actual singular simplices and topological subset
inclusions. In particular, the low-degree argument uses the augmentation on a
vertex, rather than inferring nonzero homology maps from equal ranks.
-/

noncomputable section

universe u

namespace GaussBonnetChern

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial

/-- The actual degree-zero homology class of a simplicial vertex. -/
def vertexHomologyClass (S : SSet.{u}) (s : S _⦋0⦌) :
    realHomologyCoefficients.{u} ⟶ S.homology realHomologyCoefficients 0 :=
  (S.chainComplex realHomologyCoefficients).liftCycles
    (S.ιChainComplex s) 0 (by simp) (by simp) ≫
      (S.chainComplex realHomologyCoefficients).homologyπ 0

@[reassoc (attr := simp)]
theorem vertexHomologyClass_augmentation (S : SSet.{u}) (s : S _⦋0⦌) :
    vertexHomologyClass S s ≫ S.homology₀ε realHomologyCoefficients = 𝟙 _ :=
  SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε S realHomologyCoefficients s

@[reassoc (attr := simp)]
theorem vertexHomologyClass_naturality {S T : SSet.{u}} (f : S ⟶ T) (s : S _⦋0⦌) :
    vertexHomologyClass S s ≫ SSet.homologyMap f realHomologyCoefficients 0 =
      vertexHomologyClass T (f.app _ s) := by
  dsimp only [vertexHomologyClass, SSet.homologyMap]
  rw [Category.assoc, homologyπ_naturality, ← Category.assoc, liftCycles_comp_cyclesMap]
  simp only [SSet.ι_chainComplexMap_f]

/-- In a connected simplicial set, any vertex class generates the actual H₀. -/
theorem vertexHomologyClass_isIso (S : SSet.{u}) [S.IsConnected] (s : S _⦋0⦌) :
    IsIso (vertexHomologyClass S s) := by
  have h : vertexHomologyClass S s = inv (S.homology₀ε realHomologyCoefficients.{u}) := by
    apply (cancel_mono (S.homology₀ε realHomologyCoefficients.{u})).mp
    simp
  rw [h]
  infer_instance

/-- A map from a nonempty space to a path-connected space surjects on H₀. -/
theorem singularHomologyMapZero_epi {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] [PathConnectedSpace Y] (f : C(X, Y)) :
    Epi (singularHomologyMap f 0) := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  let T := TopCat.toSSet.obj (TopCat.of Y)
  let φ : S ⟶ T := TopCat.toSSet.map (TopCat.ofHom f)
  let s : S _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm (Classical.choice (inferInstance : Nonempty X))
  letI : T.IsConnected := inferInstanceAs ((TopCat.toSSet.obj (TopCat.of Y)).IsConnected)
  letI : IsIso (vertexHomologyClass T (φ.app _ s)) := vertexHomologyClass_isIso T (φ.app _ s)
  change Epi (SSet.homologyMap φ realHomologyCoefficients.{u} 0)
  exact epi_of_epi_fac (vertexHomologyClass_naturality φ s)

/-- Every map between path-connected spaces induces an H₀ isomorphism.
The surjectivity proof above prevents a zero map from passing this rank test. -/
theorem singularHomologyMapZero_isIso {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] [PathConnectedSpace Y] (f : C(X, Y)) :
    IsIso (singularHomologyMap f 0) := by
  letI := singularHomologyMapZero_epi f
  letI := singularHomologyZero_finiteDimensional X
  letI := singularHomologyZero_finiteDimensional Y
  rw [ConcreteCategory.isIso_iff_bijective]
  have hs := (ModuleCat.epi_iff_surjective (singularHomologyMap f 0)).mp inferInstance
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [singularHomologyZero_finrank X, singularHomologyZero_finrank Y])).mpr hs, hs⟩

variable (X : Type u) [TopologicalSpace X] (A : Set X)

/-- H₀ of a nonempty pair in a path-connected ambient space vanishes. -/
theorem relativeSingularHomologyZero_isZero [PathConnectedSpace X] (hne : A.Nonempty) :
    IsZero (relativeSingularHomology X A 0) := by
  letI : Nonempty A := hne.to_subtype
  letI : Epi (singularHomologyInclusion X A 0) :=
    singularHomologyMapZero_epi (subspaceInclusion X A).hom
  have hz : singularHomologyToRelative X A 0 = 0 := by
    apply (cancel_epi (singularHomologyInclusion X A 0)).mp
    simpa using singularHomologyInclusion_comp_toRelative X A 0
  letI : Epi (0 : singularHomology X 0 ⟶ relativeSingularHomology X A 0) :=
    hz ▸ inferInstanceAs (Epi (singularHomologyToRelative X A 0))
  exact IsZero.of_epi_zero (singularHomology X 0) (relativeSingularHomology X A 0)

/-- Removing a contractible subspace changes no positive-degree absolute
homology of a path-connected ambient space. This is the actual LES projection. -/
theorem singularHomologyToRelative_isIso_of_contractible_subspace
    [PathConnectedSpace X] [ContractibleSpace A] (k : ℕ) (hk : k ≠ 0) :
    IsIso (singularHomologyToRelative X A k) := by
  letI : Mono (singularHomologyToRelative X A k) :=
    (relativeSingularHomology_exact_at_space X A k).mono_g
      ((singularHomology_isZero_of_contractible A k hk).eq_zero_of_src _)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  letI : Epi (singularHomologyToRelative X A (l + 1)) := by
    apply (relativeSingularHomology_exact_at_relative X A l).epi_f
    by_cases hl : l = 0
    · subst l
      letI : IsIso (singularHomologyInclusion X A 0) :=
        singularHomologyMapZero_isIso (subspaceInclusion X A).hom
      apply (cancel_mono (singularHomologyInclusion X A 0)).mp
      simpa using relativeSingularHomologyConnecting_comp_inclusion X A 0
    · exact (singularHomology_isZero_of_contractible A l hl).eq_zero_of_tgt _
  exact isIso_of_mono_of_epi _

def singularHomologyIsoRelativeOfContractibleSubspace
    [PathConnectedSpace X] [ContractibleSpace A] (k : ℕ) (hk : k ≠ 0) :
    singularHomology X k ≅ relativeSingularHomology X A k := by
  letI := singularHomologyToRelative_isIso_of_contractible_subspace X A k hk
  exact asIso (singularHomologyToRelative X A k)

open scoped RealInnerProductSpace ContinuousMap

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def spherePunctureHomeomorph (v : Metric.sphere (0 : E) 1) :
    ({v}ᶜ : Set (Metric.sphere (0 : E) 1)) ≃ₜ (ℝ ∙ (v : E))ᗮ :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)

theorem spherePuncture_contractible (v : Metric.sphere (0 : E) 1) :
    ContractibleSpace ({v}ᶜ : Set (Metric.sphere (0 : E) 1)) :=
  (spherePunctureHomeomorph v).contractibleSpace

def sphereAntipodeInPuncture (v : Metric.sphere (0 : E) 1) :
    ({v}ᶜ : Set (Metric.sphere (0 : E) 1)) :=
  ⟨-v, by simpa using (ne_neg_of_mem_sphere ℝ (by norm_num : (1 : ℝ) ≠ 0) v).symm⟩

@[simp]
theorem spherePunctureHomeomorph_antipode (v : Metric.sphere (0 : E) 1) :
    spherePunctureHomeomorph v (sphereAntipodeInPuncture v) = 0 :=
  stereographic_apply_neg v

def sphereDoublePunctureHomeomorph (v : Metric.sphere (0 : E) 1) :
    {x : ({v}ᶜ : Set (Metric.sphere (0 : E) 1)) // (x : Metric.sphere (0 : E) 1) ≠ -v} ≃ₜ
      ({0}ᶜ : Set (ℝ ∙ (v : E))ᗮ) :=
  (spherePunctureHomeomorph v).subtype (fun x ↦ by
    change (x : Metric.sphere (0 : E) 1) ≠ -v ↔ spherePunctureHomeomorph v x ≠ 0
    rw [← spherePunctureHomeomorph_antipode v]
    apply not_congr
    constructor
    · intro h
      exact congrArg (spherePunctureHomeomorph v) (Subtype.ext h)
    · intro h
      exact congrArg Subtype.val ((spherePunctureHomeomorph v).injective h))

def prodContractibleHomotopyEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [ContractibleSpace Y] : (X × Y) ≃ₕ X :=
  ((ContinuousMap.HomotopyEquiv.refl X).prodCongr
    (Classical.choice (ContractibleSpace.hequiv Y Unit))).trans
      (Homeomorph.prodUnique X Unit).toHomotopyEquiv

def puncturedSpaceHomotopyEquivSphere (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ({0}ᶜ : Set E) ≃ₕ Metric.sphere (0 : E) 1 := by
  letI : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩
  exact (homeomorphUnitSphereProd E).toHomotopyEquiv.trans prodContractibleHomotopyEquiv


section SphereDimension
open Module Metric

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem sphere_eq_pair_of_finrank_one (hE : finrank ℝ E = 1)
    (v : Metric.sphere (0 : E) 1) :
    Metric.sphere (0 : E) 1 = {(v : E), -(v : E)} := by
  have hs : (⊤ : Submodule ℝ E) = ℝ ∙ (v : E) :=
    eq_span_singleton_of_mem_of_finrank_eq_one (by simpa using hE)
      (Submodule.mem_top) (ne_zero_of_mem_unit_sphere v)
  ext x
  constructor
  · intro hx
    have hxspan : x ∈ ℝ ∙ (v : E) := hs ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxspan
    have hnorm : |a| = 1 := by
      simpa [← ha, norm_smul, norm_eq_of_mem_sphere v] using mem_sphere_zero_iff_norm.mp hx
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hnorm with h | h
    · simp [← ha, h]
    · simp [← ha, h]
  · intro hx
    rcases hx with h | h
    · simpa [h] using v.property
    · simpa [Set.mem_singleton_iff.mp h] using v.property

theorem sphere_homology_of_finrank_one (hE : finrank ℝ E = 1)
    (v : Metric.sphere (0 : E) 1) :
    (∀ k, FiniteDimensional ℝ (singularHomology (Metric.sphere (0 : E) 1) k)) ∧
    (∀ k, k ≠ 0 → CategoryTheory.Limits.IsZero
      (singularHomology (Metric.sphere (0 : E) 1) k)) ∧
    finrank ℝ (singularHomology (Metric.sphere (0 : E) 1) 0) = 2 := by
  classical
  have hf : (Metric.sphere (0 : E) 1).Finite := by
    rw [sphere_eq_pair_of_finrank_one hE v]
    exact (Set.finite_singleton _).insert _
  letI := hf.fintype
  have hne : (v : E) ≠ -(v : E) := by
    intro h
    exact (ne_neg_of_mem_unit_sphere ℝ v) (Subtype.ext h)
  refine ⟨singularHomology_finiteDimensional_of_finite_totallyDisconnected _,
    singularHomology_isZero_of_totallyDisconnected _, ?_⟩
  rw [singularHomologyZero_finrank_of_finite_totallyDisconnected,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, sphere_eq_pair_of_finrank_one hE v]
  simp [hne]

theorem sphere_pathConnected_of_finrank_gt_one (hE : 1 < finrank ℝ E) :
    PathConnectedSpace (Metric.sphere (0 : E) 1) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere _ (0 : E) (by norm_num)
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hE


end SphereDimension
open CategoryTheory CategoryTheory.Limits Module Metric
open scoped ContinuousMap

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev sphereEquatorialSpace (v : Metric.sphere (0 : E) 1) := (ℝ ∙ (-(v : E)))ᗮ

abbrev sphereExcisionOverlap (v : Metric.sphere (0 : E) 1) :=
  excisionSourceSubset (Metric.sphere (0 : E) 1) ({v}ᶜ) {-v}

theorem sphere_excision_condition (v : Metric.sphere (0 : E) 1) :
    closure ({-v} : Set (Metric.sphere (0 : E) 1)) ⊆ interior ({v}ᶜ) := by
  rw [isClosed_singleton.closure_eq, isOpen_compl_singleton.interior_eq,
    Set.singleton_subset_iff]
  simpa using (ne_neg_of_mem_unit_sphere ℝ v).symm

def sphereExcisionIso (v : Metric.sphere (0 : E) 1)
    [PathConnectedSpace (Metric.sphere (0 : E) 1)] (k : ℕ) (hk : k ≠ 0) :
    singularHomology (Metric.sphere (0 : E) 1) k ≅
      relativeSingularHomology ({-v}ᶜ : Set (Metric.sphere (0 : E) 1))
        (sphereExcisionOverlap v) k := by
  letI := spherePuncture_contractible v
  exact singularHomologyIsoRelativeOfContractibleSubspace _ ({v}ᶜ) k hk ≪≫
    (relativeExcisionHomologyIso _ ({v}ᶜ) {-v} (sphere_excision_condition v) k).symm

def sphereExcisionOverlapHomotopyEquiv (v : Metric.sphere (0 : E) 1) :
    sphereExcisionOverlap v ≃ₕ Metric.sphere (0 : sphereEquatorialSpace v) 1 := by
  let e : sphereExcisionOverlap v ≃ₜ
      {x : ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)) //
        (x : Metric.sphere (0 : E) 1) ≠ - -v} :=
    (Homeomorph.refl _).subtype (fun x ↦ by
      change (x : Metric.sphere (0 : E) 1) ∈ ({v}ᶜ : Set (Metric.sphere (0 : E) 1)) ↔
        (x : Metric.sphere (0 : E) 1) ≠ - -v
      rw [neg_neg]
      rfl)
  exact e.toHomotopyEquiv.trans
    ((sphereDoublePunctureHomeomorph (-v)).toHomotopyEquiv.trans
      (puncturedSpaceHomotopyEquivSphere (sphereEquatorialSpace v)))

/-- The full positive-degree dimension shift from actual pair excision and
the actual connecting homomorphism; zero target degree is handled separately. -/
def sphereHomologyShiftIso (v : Metric.sphere (0 : E) 1)
    [PathConnectedSpace (Metric.sphere (0 : E) 1)] (k : ℕ) (hk : k ≠ 0) :
    singularHomology (Metric.sphere (0 : E) 1) (k + 1) ≅
      singularHomology (Metric.sphere (0 : sphereEquatorialSpace v) 1) k := by
  letI := spherePuncture_contractible (-v)
  exact sphereExcisionIso v (k + 1) (by omega) ≪≫
    relativeSingularHomologyIsoOfContractible _ (sphereExcisionOverlap v) k hk ≪≫
    singularHomologyIsoOfHomotopyEquiv (sphereExcisionOverlapHomotopyEquiv v) k

/-- Finite-dimensionality of the equatorial H₀ supplies the circle case. -/
theorem sphereHomologyOne_finiteDimensional (v : Metric.sphere (0 : E) 1)
    [PathConnectedSpace (Metric.sphere (0 : E) 1)]
    [FiniteDimensional ℝ (singularHomology (Metric.sphere (0 : sphereEquatorialSpace v) 1) 0)] :
    FiniteDimensional ℝ (singularHomology (Metric.sphere (0 : E) 1) 1) := by
  letI := spherePuncture_contractible (-v)
  letI := singularHomology_finiteDimensional_of_homotopyEquiv
    (sphereExcisionOverlapHomotopyEquiv v) 0
  letI := relativeSingularHomologyOne_finiteDimensional
    ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)) (sphereExcisionOverlap v)
  exact (sphereExcisionIso v 1 (by decide)).toLinearEquiv.symm.finiteDimensional

theorem sphereHomologyOne_finrank (v : Metric.sphere (0 : E) 1)
    [PathConnectedSpace (Metric.sphere (0 : E) 1)]
    [FiniteDimensional ℝ (singularHomology (Metric.sphere (0 : sphereEquatorialSpace v) 1) 0)]
    (hne : (sphereExcisionOverlap v).Nonempty) :
    finrank ℝ (singularHomology (Metric.sphere (0 : E) 1) 1) + 1 =
      finrank ℝ (singularHomology (Metric.sphere (0 : sphereEquatorialSpace v) 1) 0) := by
  letI := spherePuncture_contractible (-v)
  letI := singularHomology_finiteDimensional_of_homotopyEquiv
    (sphereExcisionOverlapHomotopyEquiv v) 0
  rw [(sphereExcisionIso v 1 (by decide)).toLinearEquiv.finrank_eq,
    relativeSingularHomologyOne_finrank _ _ hne]
  exact singularHomology_finrank_eq_of_homotopyEquiv
    (sphereExcisionOverlapHomotopyEquiv v) 0


/-- The complete real singular homology ranks of every finite-dimensional
unit sphere, with finite-dimensionality proved in the same induction. -/
theorem unitSphere_homology_finite_and_finrank (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E], finrank ℝ E = n + 1 →
      ∀ k, FiniteDimensional ℝ (singularHomology (Metric.sphere (0 : E) 1) k) ∧
        finrank ℝ (singularHomology (Metric.sphere (0 : E) 1) k) =
          if k = 0 then (if n = 0 then 2 else 1) else (if k = n then 1 else 0) := by
  induction n with
  | zero =>
      intro E _ _ _ hE k
      letI : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
      obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).mpr (by norm_num)
      have h := sphere_homology_of_finrank_one hE ⟨v, hv⟩
      refine ⟨h.1 k, ?_⟩
      by_cases hk : k = 0
      · subst k
        simpa using h.2.2
      · letI := ModuleCat.subsingleton_of_isZero (h.2.1 k hk)
        simp [hk, Module.finrank_zero_of_subsingleton]
  | succ n ih =>
      intro E _ _ _ hE
      letI : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
      obtain ⟨v₀, hv₀⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).mpr (by norm_num)
      let v : Metric.sphere (0 : E) 1 := ⟨v₀, hv₀⟩
      letI : PathConnectedSpace (Metric.sphere (0 : E) 1) :=
        sphere_pathConnected_of_finrank_gt_one (by omega)
      letI : Fact (finrank ℝ E = (n + 1) + 1) := ⟨hE⟩
      have hH : finrank ℝ (sphereEquatorialSpace v) = n + 1 :=
        Submodule.finrank_orthogonal_span_singleton (neg_ne_zero.mpr (ne_zero_of_mem_unit_sphere v))
      have hlow := ih (sphereEquatorialSpace v) hH
      letI : Nontrivial (sphereEquatorialSpace v) :=
        Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ (sphereEquatorialSpace v))
      obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty
        (x := (0 : sphereEquatorialSpace v)) (r := 1)).mpr (by norm_num)
      have hne : (sphereExcisionOverlap v).Nonempty :=
        Set.nonempty_coe_sort.mp ⟨(sphereExcisionOverlapHomotopyEquiv v).invFun ⟨w, hw⟩⟩
      intro k
      rcases k with _ | _ | k
      · exact ⟨singularHomologyZero_finiteDimensional _, by simp [singularHomologyZero_finrank]⟩
      · letI := (hlow 0).1
        refine ⟨sphereHomologyOne_finiteDimensional v, ?_⟩
        have hr := sphereHomologyOne_finrank v hne
        rw [(hlow 0).2] at hr
        by_cases hn : n = 0
        · subst n
          norm_num at hr ⊢
          omega
        · simp [hn] at hr
          have hneq : 1 ≠ n + 1 := by omega
          simp [hneq, hn]
          omega
      · let e := sphereHomologyShiftIso v (k + 1) (by omega)
        letI := (hlow (k + 1)).1
        refine ⟨e.toLinearEquiv.symm.finiteDimensional, ?_⟩
        have hr := e.toLinearEquiv.finrank_eq.trans (hlow (k + 1)).2
        simpa only [Nat.succ_eq_add_one, show k + 1 ≠ 0 by omega,
          show k + 1 + 1 ≠ 0 by omega, if_false,
          show (k + 1 + 1 = n + 1) ↔ (k + 1 = n) by omega] using hr


open CategoryTheory CategoryTheory.Limits Module Metric
open scoped BigOperators

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unitSphere_homology_isZero (n : ℕ) (hE : finrank ℝ E = n + 1)
    (k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n) :
    IsZero (singularHomology (Metric.sphere (0 : E) 1) k) := by
  have h := unitSphere_homology_finite_and_finrank n E hE k
  letI := h.1
  letI : Subsingleton (singularHomology (Metric.sphere (0 : E) 1) k) :=
    Module.finrank_zero_iff.mp (by simpa [hk, hkn] using h.2)
  exact ModuleCat.isZero_of_subsingleton _

theorem unitSphere_topologicalEulerCharacteristic (n : ℕ) (hE : finrank ℝ E = n + 1) :
    topologicalEulerCharacteristic (Metric.sphere (0 : E) 1) = 1 + (-1 : ℤ) ^ n := by
  rw [topologicalEulerCharacteristic,
    homologyEulerChar_eq_sum_range_of_vanishing (singularChains (Metric.sphere (0 : E) 1)) n
      (fun k hk ↦ ModuleCat.subsingleton_of_isZero
        (unitSphere_homology_isZero n hE k (by omega) (by omega)))]
  have hterm (k : ℕ) :
      (-1 : ℤ) ^ k * (finrank ℝ (singularHomology (Metric.sphere (0 : E) 1) k) : ℤ) =
        (if k = 0 then 1 else 0) + (if k = n then (-1 : ℤ) ^ n else 0) := by
    rw [(unitSphere_homology_finite_and_finrank n E hE k).2]
    by_cases hk : k = 0
    · subst k
      by_cases hn : n = 0
      · subst n
        norm_num
      · simp [hn, Ne.symm hn]
    · by_cases hkn : k = n
      · subst k
        simp [hk]
      · simp [hk, hkn]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp


end GaussBonnetChern




