import GaussBonnetChern.SubdivisionHomotopy
import Mathlib.Topology.MetricSpace.Bounded

/-! # Small geometric singular simplices and actual chain coordinates

The mesh theorem applies to every path of iterated geometric subdivision.
The coordinates below are a proved coproduct isomorphism for the project's
actual singular chains; they do not replace the chain complex by an assumed model.
-/

noncomputable section

universe u v

namespace GaussBonnetChern

open CategoryTheory Convexity
open scoped BigOperators Simplicial

def singularSimplexIsSmall {X : Type u} [TopologicalSpace X] {n : ℕ}
    {ι : Type v} (U : ι → Set X) (s : C(StdSimplex ℝ (Fin (n + 1)), X)) : Prop :=
  ∃ i, Set.range s ⊆ U i

/-- A single uniform depth makes every geometric subdivision path of an actual
singular simplex small for any open cover of the target space. -/
theorem singularSimplex_eventually_small {X : Type u} [TopologicalSpace X] {n : ℕ}
    {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (s : C(StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ k : ℕ, ∀ σ : ℕ → Equiv.Perm (Fin (n + 1)),
      singularSimplexIsSmall U (s.comp (iteratedBarycentricSimplex σ k)) := by
  let : MetricSpace (StdSimplex ℝ (Fin (n + 1))) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).comapMetricSpace _
  obtain ⟨δ, hδ, hb⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ : IsCompact (Set.univ : Set (StdSimplex ℝ (Fin (n + 1)))))
    (fun i ↦ (hU i).preimage s.continuous)
    (show Set.univ ⊆ ⋃ i, s ⁻¹' U i by
      rw [← Set.preimage_iUnion, hcover]
      simp)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 2 by positivity)
    (barycentricContractionFactor_lt_one n)
  refine ⟨k, fun σ ↦ ?_⟩
  let x₀ : StdSimplex ℝ (Fin (n + 1)) := StdSimplex.single 0
  obtain ⟨i, hi⟩ := hb (iteratedBarycentricSimplex σ k x₀) (Set.mem_univ _)
  refine ⟨i, ?_⟩
  rintro _ ⟨y, rfl⟩
  apply hi
  apply Metric.mem_ball.mpr
  change dist (fun j ↦ (iteratedBarycentricSimplex σ k y).weights j)
    (fun j ↦ (iteratedBarycentricSimplex σ k x₀).weights j) < δ
  exact lt_of_le_of_lt (iteratedBarycentricSimplex_coordinate_mesh_bound σ k y x₀)
    (by linarith)

/-- Actual singular-chain degree object as a finite-support coproduct, obtained
from the two genuine colimit cocones. -/
def singularChainCoordinatesIso (X : Type u) [TopologicalSpace X] (n : ℕ) :
    (singularChains X).X n ≅ ModuleCat.of ℝ
      ((TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌) →₀ ULift.{u} ℝ) :=
  ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan
    (ModuleCat.of ℝ (ULift.{u} ℝ)) n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℝ (ULift.{u} ℝ)
        ((TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌)))

theorem iteratedBarycentricSimplex_range_mono {n : ℕ}
    (σ : ℕ → Equiv.Perm (Fin (n + 1))) {k l : ℕ} (h : k ≤ l) :
    Set.range (iteratedBarycentricSimplex σ l) ⊆ Set.range (iteratedBarycentricSimplex σ k) := by
  induction l, h using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ l _ ih =>
    exact (iteratedBarycentricSimplex_range_succ_subset σ l).trans ih

theorem singularSimplexIsSmall_iterate_mono {X : Type u} [TopologicalSpace X] {n : ℕ}
    {ι : Type v} {U : ι → Set X} (s : C(StdSimplex ℝ (Fin (n + 1)), X))
    (σ : ℕ → Equiv.Perm (Fin (n + 1))) {k l : ℕ} (h : k ≤ l)
    (hs : singularSimplexIsSmall U (s.comp (iteratedBarycentricSimplex σ k))) :
    singularSimplexIsSmall U (s.comp (iteratedBarycentricSimplex σ l)) := by
  obtain ⟨i, hi⟩ := hs
  refine ⟨i, fun y hy ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨z, hz⟩ := iteratedBarycentricSimplex_range_mono σ h ⟨x, rfl⟩
  apply hi
  exact ⟨z, congrArg s hz⟩

/-- The same depth works for all geometric descendants of a finite family of
actual singular simplices; later depths continue to work. -/
theorem finite_singularSimplexes_eventually_small {X : Type u} [TopologicalSpace X] {n : ℕ}
    {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ)
    (S : Finset C(StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ k : ℕ, ∀ s ∈ S, ∀ l ≥ k, ∀ σ : ℕ → Equiv.Perm (Fin (n + 1)),
      singularSimplexIsSmall U (s.comp (iteratedBarycentricSimplex σ l)) := by
  classical
  choose K hK using fun s : C(StdSimplex ℝ (Fin (n + 1)), X) ↦
    singularSimplex_eventually_small U hU hcover s
  refine ⟨S.sup K, fun s hs l hl σ ↦ ?_⟩
  exact singularSimplexIsSmall_iterate_mono s σ ((Finset.le_sup hs).trans hl) (hK s σ)

set_option backward.isDefEq.respectTransparency false in
theorem singularChainCoordinatesIso_inv_single (X : Type u) [TopologicalSpace X]
    (n : ℕ) (t : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌))
    (a : ULift.{u} ℝ) :
    (singularChainCoordinatesIso X n).inv (Finsupp.single t a) =
      ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := ModuleCat.of ℝ (ULift.{u} ℝ)) t) a := by
  have h : ModuleCat.ofHom (Finsupp.lsingle t (R := ℝ) (M := ULift.{u} ℝ)) ≫
        (singularChainCoordinatesIso X n).inv =
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex t :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_inv
      ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan
        (ModuleCat.of ℝ (ULift.{u} ℝ)) n)
      (ModuleCat.finsuppCoconeIsColimit ℝ (ULift.{u} ℝ)
        ((TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌))) ⟨t⟩
  exact congrArg (fun f ↦ f a) h

/-- Every element of the actual project singular-chain group is a finite sum of
its genuine coproduct simplex generators. -/
theorem singularChain_eq_finite_sum (X : Type u) [TopologicalSpace X] (n : ℕ)
    (z : (singularChains X).X n) :
    ∃ c : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌) →₀ ULift.{u} ℝ,
      z = ∑ t ∈ c.support, singularSimplexGenerator
        (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌) t) (c t) := by
  classical
  let e := singularChainCoordinatesIso X n
  let c := e.hom z
  refine ⟨c, ?_⟩
  have hz : e.inv c = z := by
    change (e.hom ≫ e.inv) z = z
    rw [e.hom_inv_id]
    rfl
  calc
    z = e.inv c := hz.symm
    _ = e.inv (∑ t ∈ c.support, Finsupp.single t (c t)) := congrArg e.inv c.sum_single.symm
    _ = ∑ t ∈ c.support, e.inv (Finsupp.single t (c t)) := by
      simp only [map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [singularChainCoordinatesIso_inv_single]
      simp only [singularSimplexGenerator, Equiv.symm_apply_apply]
      rfl

/-- The span of small genuine simplex generators inside the actual chain group. -/
def smallChainSubmodule {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (n : ℕ) : Submodule ℝ ((singularChains X).X n) :=
  Submodule.span ℝ {z | ∃ (s : C(StdSimplex ℝ (Fin (n + 1)), X)) (a : ULift.{u} ℝ),
    singularSimplexIsSmall U s ∧ z = singularSimplexGenerator s a}

theorem singularSimplexGenerator_mem_small {X : Type u} [TopologicalSpace X] {n : ℕ}
    {ι : Type v} {U : ι → Set X} {s : C(StdSimplex ℝ (Fin (n + 1)), X)}
    (hs : singularSimplexIsSmall U s) (a : ULift.{u} ℝ) :
    singularSimplexGenerator s a ∈ smallChainSubmodule U n :=
  Submodule.subset_span ⟨s, a, hs, rfl⟩

def iteratedSubdivision (X : Type u) [TopologicalSpace X] (k : ℕ) :
    singularChains X ⟶ singularChains X := match k with
  | 0 => 𝟙 _
  | k + 1 => barycentricSubdivision X ≫ iteratedSubdivision X k

def prependBarycentricPath {n : ℕ} (ρ : Equiv.Perm (Fin (n + 1)))
    (τ : ℕ → Equiv.Perm (Fin (n + 1))) (k : ℕ) : Equiv.Perm (Fin (n + 1)) := match k with
  | 0 => ρ
  | k + 1 => τ k

theorem iteratedBarycentricSimplex_cons {n : ℕ}
    (ρ : Equiv.Perm (Fin (n + 1))) (τ : ℕ → Equiv.Perm (Fin (n + 1))) (k : ℕ) :
    iteratedBarycentricSimplex (prependBarycentricPath ρ τ) (k + 1) =
      (barycentricSimplex ρ).comp (iteratedBarycentricSimplex τ k) := by
  induction k with
  | zero => simp [iteratedBarycentricSimplex, prependBarycentricPath]
  | succ k ih =>
    change (iteratedBarycentricSimplex (prependBarycentricPath ρ τ) (k + 1)).comp
        (barycentricSimplex (τ k)) =
      (barycentricSimplex ρ).comp
        ((iteratedBarycentricSimplex τ k).comp (barycentricSimplex (τ k)))
    rw [ih, ContinuousMap.comp_assoc]

theorem iteratedSubdivision_generator_mem_small {X : Type u} [TopologicalSpace X] {n : ℕ}
    {ι : Type v} {U : ι → Set X} (k : ℕ)
    (s : C(StdSimplex ℝ (Fin (n + 1)), X)) (a : ULift.{u} ℝ)
    (hsmall : ∀ σ : ℕ → Equiv.Perm (Fin (n + 1)),
      singularSimplexIsSmall U (s.comp (iteratedBarycentricSimplex σ k))) :
    (iteratedSubdivision X k).f n (singularSimplexGenerator s a) ∈ smallChainSubmodule U n := by
  induction k generalizing s with
  | zero =>
    simpa [iteratedSubdivision, iteratedBarycentricSimplex] using
      singularSimplexGenerator_mem_small (hsmall (fun _ ↦ 1)) a
  | succ k ih =>
    have hmor : singularSimplexGenerator s ≫ (iteratedSubdivision X (k + 1)).f n =
        ∑ ρ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign ρ : ℤ) •
          (singularSimplexGenerator (barycentricSingularSimplex s ρ) ≫
            (iteratedSubdivision X k).f n) := by
      rw [iteratedSubdivision, HomologicalComplex.comp_f, ← Category.assoc,
        barycentricSubdivision_f, singularSimplexGenerator_comp_subdivision,
        Preadditive.sum_comp]
      simp only [Preadditive.zsmul_comp]
    change (singularSimplexGenerator s ≫ (iteratedSubdivision X (k + 1)).f n) a ∈ _
    rw [hmor]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
      LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
    apply Submodule.sum_mem
    intro ρ _
    apply (smallChainSubmodule U n).toAddSubgroup.zsmul_mem
    apply ih
    intro τ
    have h := hsmall (prependBarycentricPath ρ τ)
    simpa only [iteratedBarycentricSimplex_cons, barycentricSingularSimplex,
      ContinuousMap.comp_assoc] using h

/-- Every actual singular chain eventually becomes a small chain under the
proved geometric subdivision chain map. All later depths remain small. -/
theorem singularChain_eventually_small {X : Type u} [TopologicalSpace X] {n : ℕ}
    {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (z : (singularChains X).X n) :
    ∃ k : ℕ, ∀ l ≥ k, (iteratedSubdivision X l).f n z ∈ smallChainSubmodule U n := by
  classical
  obtain ⟨c, hc⟩ := singularChain_eq_finite_sum X n z
  let S := c.support.image (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌))
  obtain ⟨k, hk⟩ := finite_singularSimplexes_eventually_small U hU hcover S
  refine ⟨k, fun l hl ↦ ?_⟩
  rw [hc]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro t ht
  apply iteratedSubdivision_generator_mem_small
  exact hk _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩) l hl

theorem singularChainPostcompose_mem_small {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ} {ι : Type v}
    {U : ι → Set X} (f : C(Y, X)) {i : ι} (hf : Set.range f ⊆ U i)
    (z : (singularChains Y).X n) :
    (singularChainPostcompose f).f n z ∈ smallChainSubmodule U n := by
  classical
  obtain ⟨c, hc⟩ := singularChain_eq_finite_sum Y n z
  rw [hc]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro t _
  change (singularSimplexGenerator
    (TopCat.toSSetObjEquiv (TopCat.of Y) (Opposite.op ⦋n⦌) t) ≫
      (singularChainPostcompose f).f n) (c t) ∈ _
  rw [singularSimplexGenerator_postcompose]
  apply singularSimplexGenerator_mem_small
  refine ⟨i, fun y hy ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hy
  exact hf ⟨_, rfl⟩

/-- Each homotopy component sends a small genuine generator to a small chain;
the canonical cone is postcomposed through the original simplex image. -/
theorem subdivisionHomotopy_generator_mem_small {X : Type u} [TopologicalSpace X]
    {n : ℕ} {ι : Type v} {U : ι → Set X}
    {s : C(StdSimplex ℝ (Fin (n + 1)), X)} (hs : singularSimplexIsSmall U s)
    (a : ULift.{u} ℝ) :
    subdivisionHomotopyDegree n X (singularSimplexGenerator s a) ∈ smallChainSubmodule U (n + 1) := by
  cases n with
  | zero => simp [subdivisionHomotopyDegree]
  | succ n =>
    change (singularSimplexGenerator s ≫ subdivisionHomotopyDegree (n + 1) X) a ∈ _
    rw [singularSimplexGenerator_subdivisionHomotopy_succ, ModuleCat.comp_apply]
    obtain ⟨i, hi⟩ := hs
    apply singularChainPostcompose_mem_small
    rintro _ ⟨x, rfl⟩
    apply hi
    exact ⟨canonicalSimplexProjection (n + 1) x, rfl⟩

theorem smallChainSubmodule_homotopy {X : Type u} [TopologicalSpace X]
    {n : ℕ} {ι : Type v} {U : ι → Set X} {z : (singularChains X).X n}
    (hz : z ∈ smallChainSubmodule U n) :
    subdivisionHomotopyDegree n X z ∈ smallChainSubmodule U (n + 1) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, a, hs, rfl⟩ := hz
    exact subdivisionHomotopy_generator_mem_small hs a
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

theorem smallChainSubmodule_boundary {X : Type u} [TopologicalSpace X]
    {n : ℕ} {ι : Type v} {U : ι → Set X} {z : (singularChains X).X (n + 1)}
    (hz : z ∈ smallChainSubmodule U (n + 1)) :
    (singularChains X).d (n + 1) n z ∈ smallChainSubmodule U n := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, a, ⟨j, hs⟩, rfl⟩ := hz
    change (singularSimplexGenerator s ≫ (singularChains X).d (n + 1) n) a ∈ _
    rw [singularSimplexGenerator_boundary]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply]
    apply Submodule.sum_mem
    intro i _
    apply (smallChainSubmodule U n).toAddSubgroup.zsmul_mem
    apply singularSimplexGenerator_mem_small
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hy
    exact hs ⟨standardSimplexFace i x, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

/-- The actual small-chain subcomplex, using restrictions of the project's differential. -/
def smallSingularChains {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) : ChainComplex (ModuleCat.{u} ℝ) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of ℝ (smallChainSubmodule U n))
    (fun n ↦ ModuleCat.ofHom (((singularChains X).d (n + 1) n).hom.restrict
      (fun _ hz ↦ smallChainSubmodule_boundary hz)))
    (fun n ↦ by
      ext z
      change ((singularChains X).d (n + 2) (n + 1) ≫ (singularChains X).d (n + 1) n) z.val = 0
      rw [HomologicalComplex.d_comp_d]
      rfl)

def smallSingularChainsInclusion {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) : smallSingularChains U ⟶ singularChains X :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (smallChainSubmodule U n).subtype)
    (fun n ↦ by
      simp only [smallSingularChains, ChainComplex.of_d]
      ext z
      rfl)

theorem smallChainSubmodule_iteratedSubdivision {X : Type u} [TopologicalSpace X]
    {n : ℕ} {ι : Type v} {U : ι → Set X} (k : ℕ) {z : (singularChains X).X n}
    (hz : z ∈ smallChainSubmodule U n) :
    (iteratedSubdivision X k).f n z ∈ smallChainSubmodule U n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, a, hs, rfl⟩ := hz
    apply iteratedSubdivision_generator_mem_small
    intro σ
    apply singularSimplexIsSmall_iterate_mono s σ (Nat.zero_le k)
    simpa [iteratedBarycentricSimplex] using hs
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

def iteratedSubdivisionHomotopy (X : Type u) [TopologicalSpace X] (k : ℕ) :
    Homotopy (iteratedSubdivision X k) (𝟙 (singularChains X)) := match k with
  | 0 => Homotopy.refl _
  | k + 1 => ((barycentricSubdivisionHomotopy X).compRightId (iteratedSubdivision X k)).trans
    (iteratedSubdivisionHomotopy X k)

theorem iteratedSubdivisionHomotopy_hom_succ (X : Type u) [TopologicalSpace X] (k n : ℕ) :
    (iteratedSubdivisionHomotopy X (k + 1)).hom n (n + 1) =
      subdivisionHomotopyDegree n X ≫ (iteratedSubdivision X k).f (n + 1) +
        (iteratedSubdivisionHomotopy X k).hom n (n + 1) := by
  simp [iteratedSubdivisionHomotopy, Homotopy.compRightId, Homotopy.trans,
    Homotopy.compRight, Homotopy.ofEq, barycentricSubdivisionHomotopy]

theorem smallChainSubmodule_iteratedHomotopy {X : Type u} [TopologicalSpace X]
    {n : ℕ} {ι : Type v} {U : ι → Set X} (k : ℕ) {z : (singularChains X).X n}
    (hz : z ∈ smallChainSubmodule U n) :
    (iteratedSubdivisionHomotopy X k).hom n (n + 1) z ∈ smallChainSubmodule U (n + 1) := by
  induction k with
  | zero => simp [iteratedSubdivisionHomotopy, Homotopy.refl, Homotopy.ofEq]
  | succ k ih =>
    rw [iteratedSubdivisionHomotopy_hom_succ]
    simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply]
    exact Submodule.add_mem _
      (smallChainSubmodule_iteratedSubdivision k (smallChainSubmodule_homotopy hz)) ih

theorem iteratedSubdivisionHomotopy_cycle_boundary {X : Type u} [TopologicalSpace X]
    (k n : ℕ) (z : (singularChains X).X n)
    (hz : (singularChains X).d n (n - 1) z = 0) :
    (singularChains X).d (n + 1) n ((iteratedSubdivisionHomotopy X k).hom n (n + 1) z) =
      (iteratedSubdivision X k).f n z - z := by
  have h := (iteratedSubdivisionHomotopy X k).comm n
  rw [dNext_nat, Homotopy.prevD_chainComplex] at h
  have hv := congrArg (fun f ↦ f z) h
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
    hz, map_zero, zero_add, HomologicalComplex.id_f, ModuleCat.id_apply] at hv
  exact eq_sub_of_add_eq hv.symm

/-- Every actual singular cycle is homologous to a small cycle for an open cover. -/
theorem singularCycle_small_representative {X : Type u} [TopologicalSpace X]
    {n : ℕ} {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (z : (singularChains X).X n)
    (hz : (singularChains X).d n (n - 1) z = 0) :
    ∃ z' : (singularChains X).X n, z' ∈ smallChainSubmodule U n ∧
      (singularChains X).d n (n - 1) z' = 0 ∧
      ∃ w : (singularChains X).X (n + 1), (singularChains X).d (n + 1) n w = z' - z := by
  obtain ⟨k, hk⟩ := singularChain_eventually_small U hU hcover z
  refine ⟨(iteratedSubdivision X k).f n z, hk k (le_refl _), ?_,
    (iteratedSubdivisionHomotopy X k).hom n (n + 1) z,
    iteratedSubdivisionHomotopy_cycle_boundary k n z hz⟩
  have h := congrArg (fun f ↦ f z) ((iteratedSubdivision X k).comm n (n - 1))
  simpa only [ModuleCat.comp_apply, hz, map_zero] using h

/-- A small actual cycle which bounds in the full singular complex already
bounds by a small chain. This is the injective half of the small-chain theorem. -/
theorem smallCycle_small_boundary {X : Type u} [TopologicalSpace X]
    {n : ℕ} {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (z : (singularChains X).X n)
    (hsmall : z ∈ smallChainSubmodule U n) (hz : (singularChains X).d n (n - 1) z = 0)
    (w : (singularChains X).X (n + 1)) (hw : (singularChains X).d (n + 1) n w = z) :
    ∃ w' : (singularChains X).X (n + 1), w' ∈ smallChainSubmodule U (n + 1) ∧
      (singularChains X).d (n + 1) n w' = z := by
  obtain ⟨k, hk⟩ := singularChain_eventually_small U hU hcover w
  refine ⟨(iteratedSubdivision X k).f (n + 1) w -
    (iteratedSubdivisionHomotopy X k).hom n (n + 1) z,
    Submodule.sub_mem _ (hk k (le_refl _)) (smallChainSubmodule_iteratedHomotopy k hsmall), ?_⟩
  have h := congrArg (fun f ↦ f w) ((iteratedSubdivision X k).comm (n + 1) n)
  simp only [ModuleCat.comp_apply, hw] at h
  rw [map_sub, h, iteratedSubdivisionHomotopy_cycle_boundary k n z hz, sub_sub_cancel]

end GaussBonnetChern
