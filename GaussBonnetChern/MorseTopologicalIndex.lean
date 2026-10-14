import GaussBonnetChern.MorseEulerFiltration
import GaussBonnetChern.CriticalLevelAttachment
import GaussBonnetChern.MorseIndexBounds

noncomputable section
universe u
namespace GaussBonnetChern
open CategoryTheory CategoryTheory.Limits Module Set
open Bundle
open scoped Manifold ContDiff ContinuousMap DirectSum BigOperators

/-- A genuine homeomorphism of pairs induces relative singular-homology isomorphisms. -/
def relativeSingularHomologyIsoOfHomeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (e : X ≃ₜ Y) (h : ∀ x, x ∈ A ↔ e x ∈ B) (k : ℕ) :
    relativeSingularHomology X A k ≅ relativeSingularHomology Y B k :=
  relativeSingularHomologyIsoOfHomotopyEquivs e.toHomotopyEquiv
    (fun x hx ↦ (h x).mp hx) (e.subtype h).toHomotopyEquiv rfl k

/-- An ambient inclusion homotopy equivalence induces the genuine relative
comparison while keeping the original lower sublevel fixed. -/
def nestedPairRelativeHomologyIsoOfInclusionHomotopyEquiv
    {M : Type u} [TopologicalSpace M] {L A U : Set M}
    (hLA : L ⊆ A) (hLU : L ⊆ U) (e : A ≃ₕ U)
    (he : ∀ x, (e x : M) = x) (k : ℕ) :
    relativeSingularHomology A (nestedPairSubset L A) k ≅
      relativeSingularHomology U (nestedPairSubset L U) k := by
  have hf : MapsTo e.toFun (nestedPairSubset L A) (nestedPairSubset L U) := by
    intro x hx
    change (e x).val ∈ L
    rw [he]
    exact hx
  let b := (nestedPairSubsetHomeomorph hLA).trans (nestedPairSubsetHomeomorph hLU).symm
  apply relativeSingularHomologyIsoOfHomotopyEquivs e hf b.toHomotopyEquiv _ k
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact (he x.val).symm

section CriticalLevel
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]
variable {ι : Type u} [Fintype ι] {E F : ι → Type u}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, FiniteDimensional ℝ (F i)]
open Morse

/-- The actual lower piece is compared with the negative disk pair by its
normal-form chart and the proved quadratic contraction. -/
def localLowerPieceHomologyIsoDisk
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) {ε c : ℝ} (hε : 0 < ε) (f : M → ℝ)
    (hsub : ∀ i, coordinateBlock ε ⊆ (e i).target)
    (hdisj : Pairwise (fun i j ↦ Disjoint (e i).source (e j).source))
    (hform : ∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x)) (i : ι) (k : ℕ) :
    relativeSingularHomology (localLowerPiece e ε c f i)
      {x | f x.val.val ≤ c - ε} k ≅
        relativeSingularHomology (Metric.closedBall (0 : E i) 1) (unitDiskBoundarySubset (E i)) k := by
  let e₁ := relativeSingularHomologyIsoOfHomeomorph
    (localLowerPieceHomeomorph e ε c f hsub hdisj hform i)
    (fun x ↦ (localLowerPieceHomeomorph_oldLower e ε c f hsub hdisj hform i x).symm) k
  have ha : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have har : Real.sqrt ε ≤ 2 * Real.sqrt ε := by linarith
  have hs : 0 ≤ 2 * Real.sqrt ε := by positivity
  have hcover : ∀ b ≥ 0, (Real.sqrt ε) ^ 2 ≤ b + handleCutoff ε b := by
    intro b hb
    simpa only [Real.sq_sqrt hε.le] using handleCutoff_covers_lower_level hε hb
  have e₂ := quadraticLowerPairHomologyIsoDisk (U := E i) (V := F i)
    (handleCutoff ε) (Real.sqrt ε) (2 * Real.sqrt ε) (2 * Real.sqrt ε)
    ha har ((handleCutoff_antitone ε).antitoneOn (Ici 0)) hs hcover k
  have hsq : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
  rw [hsq] at e₂
  exact e₁ ≪≫ e₂

/-- Actual critical-band relative homology for a finite family of disjoint
normal-form charts. The result follows from proved flow, excision, disjoint
union, and quadratic pair maps. No attachment equivalence is assumed. -/
def criticalLevelRelativeHomologyIsoDiskSum
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) {ε c : ℝ} (hε : 0 < ε)
    (hsub : ∀ i, coordinateBlock ε ⊆ (e i).target)
    (he : ∀ i, ContMDiffOn (model n) 𝓘(ℝ, E i × F i) ∞ (e i) (e i).source)
    (hei : ∀ i, ContMDiffOn 𝓘(ℝ, E i × F i) (model n) ∞ (e i).symm (e i).target)
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hdisj : Pairwise (fun i j ↦ Disjoint (e i).source (e j).source))
    (hform : ∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x))
    (hreg : ∀ x, f x ∈ Icc (c - ε) (c + ε) → (∀ i, x ∉ (e i).source) →
      mvfderiv (model n) f x ≠ 0) (k : ℕ) :
    relativeSingularHomology {x : M // f x ≤ c + ε}
      {x | f x.val ≤ c - ε} k ≅ diskHandleHomology E k := by
  classical
  let L : Set M := {x | f x ≤ c - ε}
  let U : Set M := {x | f x ≤ c + ε}
  let A : Set M := {x | finiteChartLowering e ε f x ≤ c - ε}
  let B : Set A := {x | f x.val ≤ c - ε}
  let S : ι → Set A := localLowerPiece e ε c f
  have hLA : L ⊆ A := fun x hx ↦ (finiteChartLowering_le e hε f x).trans hx
  have hLU : L ⊆ U := fun x hx ↦ by
    change f x ≤ c - ε at hx
    change f x ≤ c + ε
    linarith
  have hex := exists_criticalLevel_homotopyEquiv e hε
    (fun i ↦ (handleEllipsoid_subset_coordinateBlock hε).trans (hsub i)) he hei hf hdisj hform hreg
  let eh := Classical.choose hex
  have heh := Classical.choose_spec hex
  let e₁ := nestedPairRelativeHomologyIsoOfInclusionHomotopyEquiv hLA hLU eh heh k
  have hz : closure ((⋃ i, S i)ᶜ : Set A) ⊆ interior B := by
    have hZ : ((⋃ i, S i)ᶜ : Set A) =
        {x : A | x.val ∉ ⋃ i, chartBlock (e i) ε} := by
      ext x
      simp only [S, localLowerPiece, Set.mem_compl_iff,
        Set.mem_iUnion, Set.mem_setOf_eq]
      rfl
    rw [hZ]
    exact finiteChartLowering_excision_closure e hε hsub f
  let e₂ := relativeExcisionHomologyIso A B ((⋃ i, S i)ᶜ) hz k
  let eu : (((⋃ i, S i)ᶜ)ᶜ : Set A) ≃ₜ (⋃ i, S i : Set A) := Homeomorph.setCongr (compl_compl _)
  let e₃ := relativeSingularHomologyIsoOfHomeomorph (A := excisionSourceSubset A B ((⋃ i, S i)ᶜ))
    (B := Subtype.val ⁻¹' B) eu (fun _ ↦ Iff.rfl) k
  let hu := finiteDisjointClosedUnionHomeomorph S
    (isClosed_localLowerPiece e ε c f hsub)
    (pairwise_disjoint_localLowerPiece e ε c f hsub hdisj)
  let e₄ := finiteDisjointClosedUnionPairHomologyIso S
    (isClosed_localLowerPiece e ε c f hsub)
    (pairwise_disjoint_localLowerPiece e ε c f hsub hdisj) B k
  let e₅ := relativeFamilyHomologyIsoDiskSum E (fun i ↦ S i)
    (fun i ↦ Subtype.val ⁻¹' B) k
    (fun i ↦ localLowerPieceHomologyIsoDisk e hε f hsub hdisj hform i k)
  exact e₁.symm ≪≫ e₂.symm ≪≫ e₃ ≪≫ e₄.symm ≪≫ e₅

/-- The finite-dimensionality, vanishing, and Euler increment of an actual
critical band, now using the constructed relative comparison. -/
theorem criticalLevel_finiteHomology_euler
    (e : ∀ i, OpenPartialHomeomorph M (E i × F i)) {ε c : ℝ} (hε : 0 < ε)
    (hsub : ∀ i, coordinateBlock ε ⊆ (e i).target)
    (he : ∀ i, ContMDiffOn (model n) 𝓘(ℝ, E i × F i) ∞ (e i) (e i).source)
    (hei : ∀ i, ContMDiffOn 𝓘(ℝ, E i × F i) (model n) ∞ (e i).symm (e i).target)
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hdisj : Pairwise (fun i j ↦ Disjoint (e i).source (e j).source))
    (hform : ∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x))
    (hreg : ∀ x, f x ∈ Icc (c - ε) (c + ε) → (∀ i, x ∉ (e i).source) →
      mvfderiv (model n) f x ≠ 0)
    (N : ℕ) (hN : ∀ i, finrank ℝ (E i) ≤ N)
    (hA : FiniteSingularHomologyBound {x : M // f x ≤ c - ε} N) :
    FiniteSingularHomologyBound {x : M // f x ≤ c + ε} N ∧
      topologicalEulerCharacteristic {x : M // f x ≤ c + ε} =
        topologicalEulerCharacteristic {x : M // f x ≤ c - ε} +
          ∑ i, (-1 : ℤ) ^ finrank ℝ (E i) := by
  apply finiteNestedPair_step E (A := {x : M | f x ≤ c - ε})
    (B := {x : M | f x ≤ c + ε}) (fun x hx ↦ by dsimp at hx ⊢; linarith)
    (fun k ↦ criticalLevelRelativeHomologyIsoDiskSum e hε hsub he hei hf hdisj hform hreg k)
    N hN hA
end CriticalLevel
end GaussBonnetChern





noncomputable section
namespace GaussBonnetChern
open CategoryTheory CategoryTheory.Limits Module Set Bundle
open scoped Manifold ContDiff ContinuousMap BigOperators

theorem FiniteSingularHomologyBound.of_homotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {N : ℕ}
    (h : FiniteSingularHomologyBound Y N) (e : X ≃ₕ Y) :
    FiniteSingularHomologyBound X N := by
  refine ⟨fun k ↦ ?_, fun k hk ↦ (h.vanishing k hk).of_iso
    (singularHomologyIsoOfHomotopyEquiv e k)⟩
  letI := h.finite k
  exact singularHomology_finiteDimensional_of_homotopyEquiv e k

theorem topologicalEulerCharacteristic_eq_of_homotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    topologicalEulerCharacteristic X = topologicalEulerCharacteristic Y := by
  unfold topologicalEulerCharacteristic HomologicalComplex.homologyEulerChar GradedObject.eulerChar
  apply finsum_congr
  intro k
  rw [singularHomology_finrank_eq_of_homotopyEquiv e k]

section RegularBands
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

/-- A critical-band Euler step can be extended over adjoining regular bands
by the proved actual flow homotopy equivalences. -/
theorem sublevel_step_across_regular_bands
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    {a l h b : ℝ} (hal : a ≤ l) (hhb : h ≤ b)
    (hleft : ∀ x, f x ∈ Icc a l → mvfderiv (model n) f x ≠ 0)
    (hright : ∀ x, f x ∈ Icc h b → mvfderiv (model n) f x ≠ 0)
    (N : ℕ) (d : ℤ)
    (hstep : FiniteSingularHomologyBound {x : M // f x ≤ l} N →
      FiniteSingularHomologyBound {x : M // f x ≤ h} N ∧
        topologicalEulerCharacteristic {x : M // f x ≤ h} =
          topologicalEulerCharacteristic {x : M // f x ≤ l} + d)
    (hA : FiniteSingularHomologyBound {x : M // f x ≤ a} N) :
    FiniteSingularHomologyBound {x : M // f x ≤ b} N ∧
      topologicalEulerCharacteristic {x : M // f x ≤ b} =
        topologicalEulerCharacteristic {x : M // f x ≤ a} + d := by
  obtain ⟨el, hel⟩ := Morse.exists_sublevel_homotopyEquiv n M hf hal hleft
  obtain ⟨er, her⟩ := Morse.exists_sublevel_homotopyEquiv n M hf hhb hright
  obtain ⟨hH, he⟩ := hstep (hA.of_homotopyEquiv el.symm)
  refine ⟨hH.of_homotopyEquiv er.symm, ?_⟩
  rw [← topologicalEulerCharacteristic_eq_of_homotopyEquiv er, he,
    ← topologicalEulerCharacteristic_eq_of_homotopyEquiv el]
/-- The empty critical set forces the compact manifold itself to be empty,
by the actual regular-band deformation between empty and full sublevels. -/
theorem isEmpty_of_no_critical_points
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hcrit : ∀ x, mvfderiv (model n) f x ≠ 0) : IsEmpty M := by
  obtain ⟨a, b, hab, hempty, hfull⟩ := exists_empty_full_sublevels hf.continuous
  obtain ⟨e, he⟩ := Morse.exists_sublevel_homotopyEquiv n M hf hab.le (fun x _ ↦ hcrit x)
  refine ⟨fun x ↦ ?_⟩
  have hx : f x ≤ b := by
    have hh := congrArg (fun s : Set M ↦ x ∈ s) hfull
    exact hh.mpr trivial
  let y := e.invFun ⟨x, hx⟩
  exact Set.notMem_empty y.val
    ((congrArg (fun s : Set M ↦ y.val ∈ s) hempty).mp y.property)
end RegularBands

end GaussBonnetChern



noncomputable section
namespace GaussBonnetChern
open CategoryTheory CategoryTheory.Limits Module Set Bundle
open scoped Manifold ContDiff ContinuousMap BigOperators

section CriticalValueTelescoping
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

/-- The regular intervals between all distinct critical values and the actual
critical-band steps telescope. Equal-valued points remain in their full fiber.
The proof also propagates finite-dimensionality and genuine vanishing. -/
theorem finiteCriticalValues_sublevel_euler
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f) (N : ℕ) (w : ℝ → ℤ)
    (C : Finset ℝ)
    (hstep : ∀ c ∈ C, ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
      FiniteSingularHomologyBound {x : M // f x ≤ c - ε} N →
      FiniteSingularHomologyBound {x : M // f x ≤ c + ε} N ∧
        topologicalEulerCharacteristic {x : M // f x ≤ c + ε} =
          topologicalEulerCharacteristic {x : M // f x ≤ c - ε} + w c)
    {a b : ℝ} (hab : a < b) (hC : ∀ c ∈ C, a < c ∧ c < b)
    (hcover : ∀ x, f x ∈ Icc a b → mvfderiv (model n) f x = 0 → f x ∈ C)
    (hA : FiniteSingularHomologyBound {x : M // f x ≤ a} N) :
    FiniteSingularHomologyBound {x : M // f x ≤ b} N ∧
      topologicalEulerCharacteristic {x : M // f x ≤ b} =
        topologicalEulerCharacteristic {x : M // f x ≤ a} + ∑ c ∈ C, w c := by
  classical
  induction' C using Finset.strongInductionOn with C ih generalizing a b
  by_cases hne : C.Nonempty
  · let c := C.max' hne
    have hc : c ∈ C := C.max'_mem hne
    have hcmax : ∀ v ∈ C, v ≤ c := fun v hv ↦ C.le_max' v hv
    let T := insert a (C.erase c)
    have hT : T.Nonempty := Finset.insert_nonempty _ _
    let t := T.max' hT
    have hat : a ≤ t := T.le_max' a (Finset.mem_insert_self _ _)
    have htc : t < c := by
      have ht := T.max'_mem hT
      change t ∈ T at ht
      rcases Finset.mem_insert.mp ht with hta | ht
      · rw [hta]
        exact (hC c hc).1
      · exact C.lt_max'_of_mem_erase_max' hne ht
    obtain ⟨ρ, hρ, hs⟩ := hstep c hc
    let ε := min ρ (min ((c - t) / 2) ((b - c) / 2))
    have hε : 0 < ε := lt_min hρ (lt_min (by linarith) (by linarith [(hC c hc).2]))
    have hερ : ε ≤ ρ := min_le_left _ _
    have hεt : ε ≤ (c - t) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hεb : ε ≤ (b - c) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have htl : t < c - ε := by linarith
    have hub : c + ε < b := by linarith [(hC c hc).2]
    have hal : a < c - ε := hat.trans_lt htl
    have hCer : ∀ v ∈ C.erase c, a < v ∧ v < c - ε := by
      intro v hv
      exact ⟨(hC v (Finset.mem_of_mem_erase hv)).1,
        (T.le_max' v (Finset.mem_insert_of_mem hv)).trans_lt htl⟩
    have hcover' : ∀ x, f x ∈ Icc a (c - ε) →
        mvfderiv (model n) f x = 0 → f x ∈ C.erase c := by
      intro x hx hz
      apply Finset.mem_erase.mpr
      refine ⟨?_, hcover x ⟨hx.1, hx.2.trans (by linarith)⟩ hz⟩
      intro heq
      rw [heq] at hx
      linarith [hx.2]
    obtain ⟨hl, hel⟩ := ih (C.erase c) (Finset.erase_ssubset hc)
      (fun v hv ↦ hstep v (Finset.mem_of_mem_erase hv)) hal hCer hcover' hA
    obtain ⟨hu, heu⟩ := hs ε hε hερ hl
    have hregular : ∀ x, f x ∈ Icc (c + ε) b → mvfderiv (model n) f x ≠ 0 := by
      intro x hx hz
      have hv := hcmax (f x) (hcover x ⟨by linarith [(hC c hc).1, hx.1], hx.2⟩ hz)
      linarith [hx.1]
    obtain ⟨e, he⟩ := Morse.exists_sublevel_homotopyEquiv n M hf hub.le hregular
    refine ⟨hu.of_homotopyEquiv e.symm, ?_⟩
    rw [← topologicalEulerCharacteristic_eq_of_homotopyEquiv e, heu, hel]
    rw [← Finset.sum_erase_add _ _ hc]
    ring
  · have hzero : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst C
    have hregular : ∀ x, f x ∈ Icc a b → mvfderiv (model n) f x ≠ 0 := by
      intro x hx hz
      exact Finset.notMem_empty _ (hcover x hx hz)
    obtain ⟨e, he⟩ := Morse.exists_sublevel_homotopyEquiv n M hf hab.le hregular
    exact ⟨hA.of_homotopyEquiv e.symm,
      by simpa using (topologicalEulerCharacteristic_eq_of_homotopyEquiv e).symm⟩

end CriticalValueTelescoping
end GaussBonnetChern

noncomputable section
namespace GaussBonnetChern
open CategoryTheory CategoryTheory.Limits Module Set Bundle
open scoped Manifold ContDiff ContinuousMap BigOperators GaussBonnetChern.MorseCharts

section ActualMorseFunction
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

/-- Each actual critical-value fiber has a uniformly shrinkable homological
Euler increment. Its charts, regular complement, and relative homology map
are constructed from the actual smooth Morse function. -/
theorem actual_criticalValue_euler_step
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hfin : {p : M | mvfderiv (model n) f p = 0}.Finite)
    (hH : ∀ p, mvfderiv (model n) f p = 0 →
      Function.Injective (connection n M (gradient n M f) p)) (c : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
      FiniteSingularHomologyBound {x : M // f x ≤ c - ε} (2 * n) →
      FiniteSingularHomologyBound {x : M // f x ≤ c + ε} (2 * n) ∧
        topologicalEulerCharacteristic {x : M // f x ≤ c + ε} =
          topologicalEulerCharacteristic {x : M // f x ≤ c - ε} +
            ∑ p ∈ hfin.toFinset with f p = c, (-1 : ℤ) ^ morseIndex n M (hf p) := by
  classical
  letI := Morse.finite_criticalValueFiber n M hfin c
  letI : Fintype (Morse.CriticalValueFiber n M f c) := Fintype.ofFinite _
  obtain ⟨w, e, ρ, hρ, hpe, he0, he, hei, hform, hindex, hdis, hblock, hreg⟩ :=
    Morse.exists_criticalValueFiber_morse_charts n M hf hfin hH c
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ hA
  have hb : ∀ i, Morse.coordinateBlock ε ⊆ (e i).target :=
    fun i ↦ (MorseCharts.productBlock_mono hερ).trans (hblock i)
  have hr : ∀ x, f x ∈ Icc (c - ε) (c + ε) →
      (∀ i, x ∉ (e i).source) → mvfderiv (model n) f x ≠ 0 := by
    intro x hx hout
    exact hreg x ⟨by linarith [hx.1], by linarith [hx.2]⟩ hout
  have hN : ∀ i, finrank ℝ (MorseCharts.LiftedNegativeSpace.{u} (w i)) ≤ 2 * n := by
    intro i
    rw [hindex]
    exact morseIndex_le n M (hf i)
  obtain ⟨hbnd, hEuler⟩ := criticalLevel_finiteHomology_euler e hε hb he hei hf
    hdis hform hr (2 * n) hN hA
  refine ⟨hbnd, ?_⟩
  rw [hEuler]
  congr 1
  simp_rw [hindex]
  exact (Finset.sum_subtype (hfin.toFinset.filter (fun p ↦ f p = c))
    (fun p ↦ by simp) (fun p ↦ (-1 : ℤ) ^ morseIndex n M (hf p))).symm

/-- Morse theory computes the independently defined actual real singular
homology Euler characteristic. Finiteness and the common vanishing bound are
proved at the same time, without connectedness or nonemptiness assumptions. -/
theorem actual_morse_homology_and_euler
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hfin : {p : M | mvfderiv (model n) f p = 0}.Finite)
    (hH : ∀ p, mvfderiv (model n) f p = 0 →
      Function.Injective (connection n M (gradient n M f) p)) :
    FiniteSingularHomologyBound M (2 * n) ∧
      topologicalEulerCharacteristic M =
        ∑ p ∈ hfin.toFinset, (-1 : ℤ) ^ morseIndex n M (hf p) := by
  classical
  obtain ⟨a, b, hab, hempty, hfull⟩ := exists_empty_full_sublevels hf.continuous
  let C := finiteCriticalValues f hfin
  let w : ℝ → ℤ := fun c ↦
    ∑ p ∈ hfin.toFinset with f p = c, (-1 : ℤ) ^ morseIndex n M (hf p)
  have hC : ∀ c ∈ C, a < c ∧ c < b + 1 := by
    intro c hc
    obtain ⟨p, hp, hpc⟩ := (mem_finiteCriticalValues f hfin c).mp hc
    have hpa : a < f p := by
      by_contra h
      have hmem : p ∈ ({x : M | f x ≤ a} : Set M) := le_of_not_gt h
      rw [hempty] at hmem
      exact hmem
    have hpb : f p ≤ b := by
      have hmem : p ∈ ({x : M | f x ≤ b} : Set M) := by rw [hfull]; trivial
      exact hmem
    rw [← hpc]
    exact ⟨hpa, by linarith⟩
  have hcov : ∀ x, f x ∈ Icc a (b + 1) →
      mvfderiv (model n) f x = 0 → f x ∈ C := by
    intro x hx hz
    exact (mem_finiteCriticalValues f hfin (f x)).mpr ⟨x, hz, rfl⟩
  letI : IsEmpty {x : M // f x ≤ a} := ⟨fun x ↦ by
    have hx : x.val ∈ ({x : M | f x ≤ a} : Set M) := x.property
    rw [hempty] at hx
    exact hx⟩
  have hA : FiniteSingularHomologyBound {x : M // f x ≤ a} (2 * n) :=
    ⟨singularHomology_finiteDimensional_of_isEmpty _,
      fun k _ ↦ singularHomology_isZero_of_isEmpty _ k⟩
  obtain ⟨hB, heB⟩ := finiteCriticalValues_sublevel_euler hf (2 * n) w C
    (fun c _ ↦ actual_criticalValue_euler_step n M hf hfin hH c)
    (by linarith : a < b + 1) hC hcov hA
  have hwhole : {x : M | f x ≤ b + 1} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hx : x ∈ ({x : M | f x ≤ b} : Set M) := by rw [hfull]; trivial
    change f x ≤ b at hx
    linarith
  let e : {x : M // f x ≤ b + 1} ≃ₜ M := {
    toFun := Subtype.val
    invFun := fun x ↦ ⟨x, by
      have : x ∈ ({x : M | f x ≤ b + 1} : Set M) := by rw [hwhole]; trivial
      exact this⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by fun_prop }
  refine ⟨hB.of_homeomorph e.symm, ?_⟩
  rw [← topologicalEulerCharacteristic_eq_of_homeomorph e, heB,
    topologicalEulerCharacteristic_of_isEmpty, zero_add]
  exact criticalValue_fiber_sum f hfin (fun p ↦ (-1 : ℤ) ^ morseIndex n M (hf p))

/-- A Morse function exists whose actual gradient index sum equals the
Euler characteristic of actual singular homology in the full original scope. -/
theorem exists_morse_gradient_topological_index :
    ∃ (f : M → ℝ) (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
      (hfin : {p : M | mvfderiv (model n) f p = 0}.Finite),
      FiniteSingularHomologyBound M (2 * n) ∧
        (∀ p, mvfderiv (model n) f p = 0 →
          LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap ≠ 0) ∧
        (topologicalEulerCharacteristic M : ℝ) =
          ∑ p ∈ hfin.toFinset,
            Real.sign (LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap) := by
  obtain ⟨f, hf, hfin, hsign⟩ := exists_morse_function_with_index_sign n M
  have hH (p : M) (hp : mvfderiv (model n) f p = 0) :
      Function.Injective (connection n M (gradient n M f) p) :=
    Morse.connection_gradient_injective_of_linearization_det_ne_zero n M (hf p) hp (hsign p hp).1
  obtain ⟨hbnd, he⟩ := actual_morse_homology_and_euler n M hf hfin hH
  refine ⟨f, hf, hfin, hbnd, fun p hp ↦ (hsign p hp).1, ?_⟩
  rw [he]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  exact (hsign p (hfin.mem_toFinset.mp hp)).2.symm

end ActualMorseFunction
end GaussBonnetChern

