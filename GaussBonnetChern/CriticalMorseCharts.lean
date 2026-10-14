import GaussBonnetChern.MorseNormalForm
import GaussBonnetChern.ManifoldMorseNormalForm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Sets.Compacts

/-! # Genuine negative and positive blocks in Morse charts

The signed normal coordinates are split by their actual negative weights.
The two blocks carry their Euclidean inner products, including dimension zero.
The resulting coordinate map is a genuine continuous linear equivalence.
-/

noncomputable section
open Set Filter Module
open scoped Topology ContDiff BigOperators

namespace GaussBonnetChern.MorseCharts

abbrev NegativeIndex {d : ℕ} (w : Fin d → ℝ) := {i : Fin d // w i < 0}
abbrev PositiveIndex {d : ℕ} (w : Fin d → ℝ) := {i : Fin d // ¬w i < 0}
abbrev NegativeSpace {d : ℕ} (w : Fin d → ℝ) := EuclideanSpace ℝ (NegativeIndex w)
abbrev PositiveSpace {d : ℕ} (w : Fin d → ℝ) := EuclideanSpace ℝ (PositiveIndex w)

def signedCoordinateSplit {d : ℕ} (w : Fin d → ℝ) :
    (Fin d → ℝ) ≃L[ℝ] NegativeSpace w × PositiveSpace w := by
  classical
  let C : (Fin d → ℝ) ≃ₗ[ℝ] NegativeSpace w × PositiveSpace w :=
    { toFun := fun v ↦ (WithLp.toLp 2 (fun i : NegativeIndex w ↦ v i),
        WithLp.toLp 2 (fun i : PositiveIndex w ↦ v i))
      invFun := fun z i ↦ if h : w i < 0 then z.1 ⟨i, h⟩ else z.2 ⟨i, h⟩
      left_inv := by
        intro v
        funext i
        dsimp only
        split_ifs <;> rfl
      right_inv := by
        intro z
        apply Prod.ext
        · ext i
          simp [i.property]
        · ext i
          simp [i.property]
      map_add' := by intro v u; rfl
      map_smul' := by intro r v; rfl }
  exact C.toContinuousLinearEquiv

@[simp] theorem signedCoordinateSplit_fst_apply {d : ℕ} (w : Fin d → ℝ)
    (v : Fin d → ℝ) (i : NegativeIndex w) : (signedCoordinateSplit w v).1 i = v i := rfl

@[simp] theorem signedCoordinateSplit_snd_apply {d : ℕ} (w : Fin d → ℝ)
    (v : Fin d → ℝ) (i : PositiveIndex w) : (signedCoordinateSplit w v).2 i = v i := rfl

theorem negativeSpace_finrank {d : ℕ} (w : Fin d → ℝ) :
    Module.finrank ℝ (NegativeSpace w) = {i | w i < 0}.ncard := by
  classical
  rw [finrank_euclideanSpace]
  exact Set.fintypeCard_eq_ncard _

theorem signedSquares_eq_blocks {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (v : Fin d → ℝ) :
    (∑ i, w i * (v i)^2) =
      -‖(signedCoordinateSplit w v).1‖^2 + ‖(signedCoordinateSplit w v).2‖^2 := by
  classical
  have hn (i : NegativeIndex w) : w i = -1 := by
    rcases hw i with h | h
    · exact h
    · have := i.property; linarith
  have hp (i : PositiveIndex w) : w i = 1 := by
    rcases hw i with h | h
    · have := i.property; norm_num [h] at this
    · exact h
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i ↦ w i < 0) (fun i ↦ w i * (v i)^2)]
  simp_rw [hn, hp, neg_one_mul, one_mul]
  rw [Finset.sum_neg_distrib, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [signedCoordinateSplit_fst_apply, signedCoordinateSplit_snd_apply]


/-- The verified arbitrary-dimensional Morse normal form, expressed in
genuine negative/positive Euclidean blocks rather than signed scalar weights. -/
theorem morse_block_normal_form
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {s : Set E} {p : E}
    (hs : IsOpen s) (hps : p ∈ s) (hf : ContDiffOn ℝ ∞ f s)
    (hp : fderiv ℝ f p = 0) (hH : (fderiv ℝ (fderiv ℝ f) p).IsInvertible) :
    ∃ (w : Fin (Module.finrank ℝ E) → ℝ)
      (e : OpenPartialHomeomorph E (NegativeSpace w × PositiveSpace w)),
      (0 : E) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ v ∈ e.source, p + v ∈ s ∧
        f (p + v) = f p - ‖(e v).1‖^2 + ‖(e v).2‖^2) ∧
      Module.finrank ℝ (NegativeSpace w) =
        sigNeg (((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) p).toBilinForm.toQuadraticMap) := by
  obtain ⟨w, e0, hw, h0, he00, he, hei, hform, hindex⟩ :=
    MorseLocal.morse_normal_form hs hps hf hp hH
  let C := signedCoordinateSplit w
  let e := e0.trans C.toHomeomorph.toOpenPartialHomeomorph
  have hsource : e.source = e0.source := by simp [e, OpenPartialHomeomorph.trans_source]
  refine ⟨w, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hsource] using h0
  · change C (e0 0) = 0
    rw [he00, map_zero]
  · rw [hsource]
    exact C.contDiff.comp_contDiffOn he
  · exact hei.comp C.symm.contDiff.contDiffOn (fun y hy ↦ hy.2)
  · intro v hv
    obtain ⟨hvs, hfv⟩ := hform v (hsource ▸ hv)
    refine ⟨hvs, ?_⟩
    rw [hfv, signedSquares_eq_blocks w hw]
    change f p + (-‖(C (e0 v)).1‖^2 + ‖(C (e0 v)).2‖^2) =
      f p - ‖(C (e0 v)).1‖^2 + ‖(C (e0 v)).2‖^2
    ring
  · rw [negativeSpace_finrank, hindex]



open Bundle
open scoped Manifold

universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

/-- Every nondegenerate critical point of the actual metric gradient has
genuine smooth Morse coordinates on the manifold, with the original Morse index. -/
theorem exists_morse_chart_at_critical
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f) (p : M)
    (hcritical : mvfderiv (model n) f p = 0)
    (hH : Function.Injective (connection n M (gradient n M f) p)) :
    ∃ (w : Fin (Module.finrank ℝ (Model n)) → ℝ)
      (e : OpenPartialHomeomorph M (NegativeSpace w × PositiveSpace w)),
      p ∈ e.source ∧ e p = 0 ∧
      ContMDiffOn (model n) 𝓘(ℝ, NegativeSpace w × PositiveSpace w) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, NegativeSpace w × PositiveSpace w) (model n) ∞ e.symm e.target ∧
      (∀ x ∈ e.source, f x = f p - ‖(e x).1‖^2 + ‖(e x).2‖^2) ∧
      Module.finrank ℝ (NegativeSpace w) = morseIndex n M (hf p) := by
  let k := chartAt (Model n) p
  have hk : k ∈ IsManifold.maximalAtlas (model n) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hp : p ∈ k.source := mem_chart_source (Model n) p
  have hkp : k.symm (k p) = p := k.left_inv hp
  have hd : k.MDifferentiable (model n) (model n) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hk).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hk).mdifferentiableOn (by simp)⟩
  have hi : ∀ y ∈ k.target, (mfderiv (model n) (model n) k.symm y).IsInvertible := by
    intro y hy
    exact ⟨hd.symm.mfderiv hy, rfl⟩
  have hcrit' : mvfderiv (model n) f (k.symm (k p)) = 0 := by
    rw [hkp]
    exact hcritical
  have hH' : Function.Injective (connection n M (gradient n M f) (k.symm (k p))) := by
    rw [hkp]
    exact hH
  obtain ⟨w, e0, hw, h0, he00, he, hei, hform, hindex⟩ :=
    morse_normal_form_in_parametrization n M k.open_target (k.map_source hp)
      (contMDiffOn_symm_of_mem_maximalAtlas hk) hi hf hcrit' hH'
  let shift : OpenPartialHomeomorph (Model n) (Model n) :=
    (Homeomorph.subRight (k p)).toOpenPartialHomeomorph
  let c := k.trans shift
  have hcs : c.source = k.source := by simp [c, shift, OpenPartialHomeomorph.trans_source]
  have hc (x : M) : c x = k x - k p := rfl
  have hci (v : Model n) : c.symm v = k.symm (v + k p) := rfl
  have hce : ContMDiffOn (model n) (model n) ∞ c c.source := by
    rw [hcs]
    exact (contMDiffOn_of_mem_maximalAtlas hk).sub contMDiffOn_const
  have hcie : ContMDiffOn (model n) (model n) ∞ c.symm c.target := by
    apply (contMDiffOn_symm_of_mem_maximalAtlas hk).comp
      (contMDiffOn_id.add contMDiffOn_const)
    intro v hv
    exact hv.2
  let C := signedCoordinateSplit w
  let e1 := c.trans e0
  let e := e1.trans C.toHomeomorph.toOpenPartialHomeomorph
  have hes : e.source = e1.source := by simp [e, OpenPartialHomeomorph.trans_source]
  refine ⟨w, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hes]
    change p ∈ c.source ∧ c p ∈ e0.source
    constructor
    · rw [hcs]
      exact hp
    · rw [hc, sub_self]
      exact h0
  · change C (e0 (k p - k p)) = 0
    rw [sub_self, he00, map_zero]
  · rw [hes]
    apply C.contDiff.contMDiff.comp_contMDiffOn
    exact he.contMDiffOn.comp (hce.mono inter_subset_left) (fun x hx ↦ hx.2)
  · apply hcie.comp ?_ ?_
    · exact hei.contMDiffOn.comp C.symm.contDiff.contMDiff.contMDiffOn (fun v hv ↦ hv.2.1)
    · intro v hv
      exact hv.2.2
  · intro x hx
    have hx1 : x ∈ e1.source := hes ▸ hx
    have hxk : x ∈ k.source := hcs ▸ hx1.1
    have hcv : c x ∈ e0.source := hx1.2
    have hfv := (hform (c x) hcv).2
    have hshift : k p + (k x - k p) = k x := by abel
    rw [hc, hshift, k.left_inv hxk, hkp,
      signedSquares_eq_blocks w hw] at hfv
    change f x = f p - ‖(C (e0 (c x))).1‖^2 + ‖(C (e0 (c x))).2‖^2
    rw [hc]
    dsimp only [C]
    linarith
  · rw [negativeSpace_finrank]
    simpa only [hkp] using hindex.symm



section FiniteCharts

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  {ι : Type*} [Fintype ι]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]

/-- Finitely many distinct chart centers have pairwise disjoint chart
sources after restriction. The maps themselves are unchanged. -/
theorem exists_disjoint_restrictions
    (p : ι → X) (hp : Function.Injective p)
    (e : ∀ i, OpenPartialHomeomorph X (V i)) (he : ∀ i, p i ∈ (e i).source) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, p i ∈ U i) ∧
      Pairwise (fun i j ↦ Disjoint ((e i).source ∩ U i) ((e j).source ∩ U j)) := by
  classical
  obtain ⟨U, hU, hdis⟩ := (Set.finite_range p).t2_separation
  refine ⟨fun i ↦ U (p i), fun i ↦ (hU (p i)).2, fun i ↦ (hU (p i)).1, ?_⟩
  intro i j hij
  exact (hdis (Set.mem_range_self i) (Set.mem_range_self j) (fun h ↦ hij (hp h))).mono
    inter_subset_right inter_subset_right

omit [T2Space X] in
/-- A finite family of open target neighborhoods of zero contains a common
closed ball. This includes the empty family and zero-dimensional target spaces. -/
theorem exists_common_closedBall
    (e : ∀ i, OpenPartialHomeomorph X (V i))
    (h0 : ∀ i, (0 : V i) ∈ (e i).target) :
    ∃ R : ℝ, 0 < R ∧ ∀ i, Metric.closedBall (0 : V i) R ⊆ (e i).target := by
  classical
  have hi (i : ι) : ∃ R : ℝ, 0 < R ∧ Metric.closedBall (0 : V i) R ⊆ (e i).target :=
    Metric.nhds_basis_closedBall.mem_iff.mp ((e i).open_target.mem_nhds (h0 i))
  choose r hr hsub using hi
  have hfinite (s : Finset ι) : ∃ R : ℝ, 0 < R ∧ ∀ i ∈ s, R ≤ r i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s his ih =>
      obtain ⟨R, hR, hRs⟩ := ih
      refine ⟨min R (r i), lt_min hR (hr i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hRs j hj)
  obtain ⟨R, hR, hRi⟩ := hfinite Finset.univ
  exact ⟨R, hR, fun i ↦ (Metric.closedBall_subset_closedBall (hRi i (Finset.mem_univ i))).trans (hsub i)⟩

end FiniteCharts

section ProductBlocks

variable {X : Type*} [TopologicalSpace X]
  {ι : Type*} [Fintype ι]
  {E F : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]

/-- The compact product blocks of common radius `2 * sqrt ε` fit in all
finite target charts, with a strictly positive common `ε`. -/
theorem exists_common_productBlock
    (e : ∀ i, OpenPartialHomeomorph X (E i × F i))
    (h0 : ∀ i, (0 : E i × F i) ∈ (e i).target) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i,
      Metric.closedBall (0 : E i) (2 * Real.sqrt ε) ×ˢ
        Metric.closedBall (0 : F i) (2 * Real.sqrt ε) ⊆ (e i).target := by
  obtain ⟨R, hR, hsub⟩ := exists_common_closedBall e h0
  refine ⟨(R / 2)^2, sq_pos_of_pos (by positivity), ?_⟩
  intro i
  rw [Real.sqrt_sq (by positivity : 0 ≤ R / 2), show 2 * (R / 2) = R by ring]
  intro z hz
  apply hsub i
  simpa only [Set.mem_prod, Metric.mem_closedBall, Prod.dist_eq,
    Prod.fst_zero, Prod.snd_zero, max_le_iff] using hz

end ProductBlocks



/-- A finite family of distinct nondegenerate critical points has disjoint
actual smooth Morse charts and a single strictly positive product-block scale.
No distinctness of the critical values is assumed. -/
theorem exists_finite_disjoint_morse_charts [T2Space M]
    {ι : Type*} [Fintype ι] {f : M → ℝ}
    (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (p : ι → M) (hp : Function.Injective p)
    (hcritical : ∀ i, mvfderiv (model n) f (p i) = 0)
    (hH : ∀ i, Function.Injective (connection n M (gradient n M f) (p i))) :
    ∃ (w : ι → Fin (Module.finrank ℝ (Model n)) → ℝ)
      (e : ∀ i, OpenPartialHomeomorph M (NegativeSpace (w i) × PositiveSpace (w i)))
      (ε : ℝ),
      0 < ε ∧ (∀ i, p i ∈ (e i).source) ∧ (∀ i, e i (p i) = 0) ∧
      (∀ i, ContMDiffOn (model n) 𝓘(ℝ, NegativeSpace (w i) × PositiveSpace (w i)) ∞
        (e i) (e i).source) ∧
      (∀ i, ContMDiffOn 𝓘(ℝ, NegativeSpace (w i) × PositiveSpace (w i)) (model n) ∞
        (e i).symm (e i).target) ∧
      (∀ i x, x ∈ (e i).source → f x = f (p i) - ‖(e i x).1‖^2 + ‖(e i x).2‖^2) ∧
      (∀ i, Module.finrank ℝ (NegativeSpace (w i)) = morseIndex n M (hf (p i))) ∧
      Pairwise (fun i j ↦ Disjoint (e i).source (e j).source) ∧
      (∀ i, Metric.closedBall (0 : NegativeSpace (w i)) (2 * Real.sqrt ε) ×ˢ
        Metric.closedBall (0 : PositiveSpace (w i)) (2 * Real.sqrt ε) ⊆ (e i).target) := by
  classical
  choose w e hpe he0 hes hei hform hindex using
    (fun i ↦ exists_morse_chart_at_critical n M hf (p i) (hcritical i) (hH i))
  obtain ⟨U, hU, hpU, hdis⟩ := exists_disjoint_restrictions p hp e hpe
  let er := fun i ↦ (e i).restrOpen (U i) (hU i)
  have hper (i : ι) : p i ∈ (er i).source := ⟨hpe i, hpU i⟩
  have he0r (i : ι) : er i (p i) = 0 := he0 i
  have h0 (i : ι) : (0 : NegativeSpace (w i) × PositiveSpace (w i)) ∈ (er i).target := by
    rw [← he0r i]
    exact (er i).map_source (hper i)
  obtain ⟨ε, hε, hblock⟩ := exists_common_productBlock er h0
  refine ⟨w, er, ε, hε, hper, he0r, ?_, ?_, ?_, hindex, hdis, hblock⟩
  · intro i
    exact (hes i).mono inter_subset_left
  · intro i
    exact (hei i).mono inter_subset_left
  · intro i x hx
    exact hform i x hx.1



universe v

/-- The existing norm on `ULift` and the pulled-back real inner product agree.
The instance is scoped to the actual Morse-coordinate construction. -/
scoped instance liftedInnerProductSpace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : InnerProductSpace ℝ (ULift.{v} E) where
  toNormedSpace := inferInstance
  inner x y := inner ℝ x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y r := inner_smul_left x.down y.down (r := r)

abbrev LiftedNegativeSpace {d : ℕ} (w : Fin d → ℝ) := ULift.{v} (NegativeSpace w)
abbrev LiftedPositiveSpace {d : ℕ} (w : Fin d → ℝ) := ULift.{v} (PositiveSpace w)

def liftBlockCoordinates {d : ℕ} (w : Fin d → ℝ) :
    (NegativeSpace w × PositiveSpace w) ≃L[ℝ]
      (LiftedNegativeSpace.{v} w × LiftedPositiveSpace.{v} w) :=
  (ContinuousLinearEquiv.ulift : LiftedNegativeSpace.{v} w ≃L[ℝ] NegativeSpace w).symm.prodCongr
    (ContinuousLinearEquiv.ulift : LiftedPositiveSpace.{v} w ≃L[ℝ] PositiveSpace w).symm

theorem liftBlockCoordinates_norm_fst {d : ℕ} (w : Fin d → ℝ)
    (z : NegativeSpace w × PositiveSpace w) : ‖(liftBlockCoordinates.{v} w z).1‖ = ‖z.1‖ := rfl

theorem liftBlockCoordinates_norm_snd {d : ℕ} (w : Fin d → ℝ)
    (z : NegativeSpace w × PositiveSpace w) : ‖(liftBlockCoordinates.{v} w z).2‖ = ‖z.2‖ := rfl

theorem liftedNegativeSpace_finrank {d : ℕ} (w : Fin d → ℝ) :
    Module.finrank ℝ (LiftedNegativeSpace.{v} w) = {i | w i < 0}.ncard := by
  exact (ContinuousLinearEquiv.ulift : LiftedNegativeSpace.{v} w ≃L[ℝ]
    NegativeSpace w).toLinearEquiv.finrank_eq.trans (negativeSpace_finrank w)



theorem block_finrank_sum {d : ℕ} (w : Fin d → ℝ) :
    Module.finrank ℝ (NegativeSpace w) + Module.finrank ℝ (PositiveSpace w) = d := by
  classical
  have h := (signedCoordinateSplit w).toLinearEquiv.finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using h.symm

theorem lifted_block_finrank_sum {d : ℕ} (w : Fin d → ℝ) :
    Module.finrank ℝ (LiftedNegativeSpace.{v} w) +
      Module.finrank ℝ (LiftedPositiveSpace.{v} w) = d := by
  rw [(ContinuousLinearEquiv.ulift : LiftedNegativeSpace.{v} w ≃L[ℝ]
      NegativeSpace w).toLinearEquiv.finrank_eq,
    (ContinuousLinearEquiv.ulift : LiftedPositiveSpace.{v} w ≃L[ℝ]
      PositiveSpace w).toLinearEquiv.finrank_eq, block_finrank_sum]

/-- The chosen charts remain valid if the common critical-value radius is
shrunk later to separate neighboring critical values. -/
theorem productBlock_mono {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {δ ε : ℝ} (h : δ ≤ ε) :
    Metric.closedBall (0 : E) (2 * Real.sqrt δ) ×ˢ
      Metric.closedBall (0 : F) (2 * Real.sqrt δ) ⊆
    Metric.closedBall (0 : E) (2 * Real.sqrt ε) ×ˢ
      Metric.closedBall (0 : F) (2 * Real.sqrt ε) := by
  exact Set.prod_mono
    (Metric.closedBall_subset_closedBall (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (by norm_num)))
    (Metric.closedBall_subset_closedBall (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (by norm_num)))

theorem isCompact_productBlock {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [ProperSpace E] [ProperSpace F] (ε : ℝ) :
    IsCompact (Metric.closedBall (0 : E) (2 * Real.sqrt ε) ×ˢ
      Metric.closedBall (0 : F) (2 * Real.sqrt ε)) :=
  (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)



/-- The same actual chart family in the manifold's universe. Lifting changes
neither block norm, dimension, Morse index, nor any chart/domain property. -/
theorem exists_lifted_finite_disjoint_morse_charts [T2Space M]
    {ι : Type u} [Fintype ι] {f : M → ℝ}
    (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (p : ι → M) (hp : Function.Injective p)
    (hcritical : ∀ i, mvfderiv (model n) f (p i) = 0)
    (hH : ∀ i, Function.Injective (connection n M (gradient n M f) (p i))) :
    ∃ (w : ι → Fin (Module.finrank ℝ (Model n)) → ℝ)
      (e : ∀ i, OpenPartialHomeomorph M
        (LiftedNegativeSpace.{u} (w i) × LiftedPositiveSpace.{u} (w i)))
      (ε : ℝ),
      0 < ε ∧ (∀ i, p i ∈ (e i).source) ∧ (∀ i, e i (p i) = 0) ∧
      (∀ i, ContMDiffOn (model n)
        𝓘(ℝ, LiftedNegativeSpace.{u} (w i) × LiftedPositiveSpace.{u} (w i)) ∞
        (e i) (e i).source) ∧
      (∀ i, ContMDiffOn
        𝓘(ℝ, LiftedNegativeSpace.{u} (w i) × LiftedPositiveSpace.{u} (w i)) (model n) ∞
        (e i).symm (e i).target) ∧
      (∀ i x, x ∈ (e i).source → f x = f (p i) - ‖(e i x).1‖^2 + ‖(e i x).2‖^2) ∧
      (∀ i, Module.finrank ℝ (LiftedNegativeSpace.{u} (w i)) = morseIndex n M (hf (p i))) ∧
      Pairwise (fun i j ↦ Disjoint (e i).source (e j).source) ∧
      (∀ i, Metric.closedBall (0 : LiftedNegativeSpace.{u} (w i)) (2 * Real.sqrt ε) ×ˢ
        Metric.closedBall (0 : LiftedPositiveSpace.{u} (w i)) (2 * Real.sqrt ε) ⊆ (e i).target) := by
  classical
  obtain ⟨w, e, ε, hε, hpe, he0, hes, hei, hform, hindex, hdis, hblock⟩ :=
    exists_finite_disjoint_morse_charts n M hf p hp hcritical hH
  let C := fun i ↦ liftBlockCoordinates.{u} (w i)
  let el := fun i ↦ (e i).trans (C i).toHomeomorph.toOpenPartialHomeomorph
  have hsource (i : ι) : (el i).source = (e i).source := by
    simp [el, OpenPartialHomeomorph.trans_source]
  refine ⟨w, el, ε, hε, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hsource]
    exact hpe i
  · intro i
    change C i (e i (p i)) = 0
    rw [he0, map_zero]
  · intro i
    rw [hsource]
    exact (C i).contDiff.contMDiff.comp_contMDiffOn (hes i)
  · intro i
    exact (hei i).comp (C i).symm.contDiff.contMDiff.contMDiffOn (fun y hy ↦ hy.2)
  · intro i x hx
    have h := hform i x (hsource i ▸ hx)
    change f x = f (p i) - ‖(C i (e i x)).1‖^2 + ‖(C i (e i x)).2‖^2
    simpa only [C, liftBlockCoordinates_norm_fst, liftBlockCoordinates_norm_snd] using h
  · intro i
    exact (ContinuousLinearEquiv.ulift : LiftedNegativeSpace.{u} (w i) ≃L[ℝ]
      NegativeSpace (w i)).toLinearEquiv.finrank_eq.trans (hindex i)
  · intro i j hij
    rw [hsource, hsource]
    exact hdis hij
  · intro i z hz
    refine ⟨mem_univ _, ?_⟩
    apply hblock i
    change ‖z.1.down - (0 : NegativeSpace (w i))‖ ≤ 2 * Real.sqrt ε ∧
      ‖z.2.down - (0 : PositiveSpace (w i))‖ ≤ 2 * Real.sqrt ε
    simpa only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right, sub_zero,
      ULift.norm_down] using hz


end GaussBonnetChern.MorseCharts
