import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Compactness.Lindelof

/-! # Smooth graphs obtained from the inverse function theorem

The local graph coordinates here are constructed from the derivative of the
given map. In particular, a graph representation is a conclusion, not an
additional assumption on the immersion.
-/

noncomputable section

open Function Set Filter
open scoped Topology ContDiff Manifold

namespace GaussBonnetChern.Morse

variable {E B C A : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- The smooth inverse-function theorem on an open domain, with smoothness on
the entire resulting source and target. The domain is shrunk to where the
actual derivative remains a continuous linear equivalence. -/
theorem exists_smoothLocalInverse {f : E → B} {s : Set E} {a : E}
    (hs : IsOpen s) (ha : a ∈ s) (hf : ContDiffOn ℝ ∞ f s)
    (L : E ≃L[ℝ] B) (hL : HasFDerivAt f (L : E →L[ℝ] B) a) :
    ∃ c : OpenPartialHomeomorph E B,
      (c : E → B) = f ∧ a ∈ c.source ∧ c.source ⊆ s ∧
      ContDiffOn ℝ ∞ c c.source ∧ ContDiffOn ℝ ∞ c.symm c.target := by
  have hfa : ContDiffAt ℝ ∞ f a := (hf a ha).contDiffAt (hs.mem_nhds ha)
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hder : {x | ∃ e : E ≃L[ℝ] B, (e : E →L[ℝ] B) = fderiv ℝ f x} ∈ 𝓝 a := by
    have hnh := L.nhds
    rw [← hL.fderiv] at hnh
    exact (hfa.continuousAt_fderiv hne).preimage_mem_nhds hnh
  obtain ⟨t, hts, ht, hat⟩ := mem_nhds_iff.mp (inter_mem (hs.mem_nhds ha) hder)
  let c₀ := hfa.toOpenPartialHomeomorph f hL hne
  let c := c₀.restrOpen t ht
  have hc : (c : E → B) = f := rfl
  have hcs : c.source ⊆ s := fun x hx => (hts hx.2).1
  refine ⟨c, hc, ⟨hfa.mem_toOpenPartialHomeomorph_source hL hne, hat⟩, hcs,
    ?_, ?_⟩
  · exact hc ▸ hf.mono hcs
  · intro y hy
    have hx := c.map_target hy
    obtain ⟨e, he⟩ := (hts hx.2).2
    have hfx : ContDiffAt ℝ ∞ f (c.symm y) :=
      (hf _ (hcs hx)).contDiffAt (hs.mem_nhds (hcs hx))
    apply ContDiffAt.contDiffWithinAt
    apply c.contDiffAt_symm hy (f₀' := e)
    · rw [hc, he]
      exact (hfx.differentiableAt (by simp)).hasFDerivAt
    · exact hc ▸ hfx

/-- A graph over the first factor of a fixed ambient splitting, obtained from
an invertible derivative of the first projection. -/
theorem exists_smoothGraph_of_projection {f : E → A} {s : Set E} {a : E}
    (hs : IsOpen s) (ha : a ∈ s) (hf : ContDiffOn ℝ ∞ f s)
    (r : A ≃L[ℝ] B × C) (L : E ≃L[ℝ] B)
    (hL : HasFDerivAt (fun x => (r (f x)).1) (L : E →L[ℝ] B) a) :
    ∃ (c : OpenPartialHomeomorph E B) (g : B → C),
      (c : E → B) = (fun x => (r (f x)).1) ∧ a ∈ c.source ∧ c.source ⊆ s ∧
      ContDiffOn ℝ ∞ c c.source ∧ ContDiffOn ℝ ∞ c.symm c.target ∧
      ContDiffOn ℝ ∞ g c.target ∧
      ∀ u ∈ c.target, r (f (c.symm u)) = (u, g u) := by
  have hp : ContDiffOn ℝ ∞ (fun x => (r (f x)).1) s :=
    (r.contDiff.comp_contDiffOn hf).fst
  obtain ⟨c, hc, hac, hcs, hcf, hci⟩ := exists_smoothLocalInverse hs ha hp L hL
  let g : B → C := fun u => (r (f (c.symm u))).2
  refine ⟨c, g, hc, hac, hcs, hcf, hci, ?_, ?_⟩
  · exact ((r.contDiff.comp_contDiffOn hf).comp hci
      (fun u hu => hcs (c.map_target hu))).snd
  · intro u hu
    apply Prod.ext
    · change (r (f (c.symm u))).1 = u
      rw [← congrFun hc]
      exact c.right_inv hu
    · rfl


section Orthogonal

variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ E]

/-- Every smooth map with injective derivative has a smooth local graph over
the actual derivative image, after the canonical ambient orthogonal isometry. -/
theorem exists_smoothGraph_of_injective_fderiv {f : E → A} {s : Set E} {a : E}
    (hs : IsOpen s) (ha : a ∈ s) (hf : ContDiffOn ℝ ∞ f s)
    (hi : Injective (fderiv ℝ f a)) :
    let K : Submodule ℝ A := (fderiv ℝ f a).range
    ∃ (c : OpenPartialHomeomorph E K) (g : K → ↥(Submodule.orthogonal K)),
      (c : E → K) = (fun x => K.orthogonalProjectionOnto (f x)) ∧
      a ∈ c.source ∧ c.source ⊆ s ∧
      ContDiffOn ℝ ∞ c c.source ∧ ContDiffOn ℝ ∞ c.symm c.target ∧
      ContDiffOn ℝ ∞ g c.target ∧
      ∀ u ∈ c.target,
        (Submodule.orthogonalDecomposition K) (f (c.symm u)) = WithLp.toLp 2 (u, g u) := by
  let D := fderiv ℝ f a
  let K : Submodule ℝ A := D.range
  let L : E ≃L[ℝ] K := (LinearEquiv.ofInjective D.toLinearMap hi).toContinuousLinearEquiv
  have hfa := (hf a ha).contDiffAt (hs.mem_nhds ha)
  have hproj : K.orthogonalProjectionOnto.comp D = (L : E →L[ℝ] K) := by
    apply ContinuousLinearMap.ext
    intro v
    exact K.orthogonalProjectionOnto_mem_subspace_eq_self ⟨D v, ⟨v, rfl⟩⟩
  have hp : HasFDerivAt (fun x => K.orthogonalProjectionOnto (f x))
      (L : E →L[ℝ] K) a := by
    rw [← hproj]
    exact K.orthogonalProjectionOnto.hasFDerivAt.comp a
      (hfa.differentiableAt (by simp)).hasFDerivAt
  have hps : ContDiffOn ℝ ∞ (fun x => K.orthogonalProjectionOnto (f x)) s :=
    K.orthogonalProjectionOnto.contDiff.comp_contDiffOn hf
  obtain ⟨c, hc, hac, hcs, hcf, hci⟩ := exists_smoothLocalInverse hs ha hps L hp
  let g : K → Kᗮ := fun u => Kᗮ.orthogonalProjectionOnto (f (c.symm u))
  refine ⟨c, g, hc, hac, hcs, hcf, hci, ?_, ?_⟩
  · exact (Kᗮ.orthogonalProjectionOnto.contDiff.comp_contDiffOn hf).comp hci
      (fun u hu => hcs (c.map_target hu))
  · intro u hu
    rw [Submodule.orthogonalDecomposition_apply]
    congr 1
    apply Prod.ext
    · change K.orthogonalProjectionOnto (f (c.symm u)) = u
      rw [← congrFun hc]
      exact c.right_inv hu
    · rfl

end Orthogonal


section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ E]

/-- An actual smooth local chart in which the given map is a graph after an
ambient orthogonal isometry. Existence is proved from derivative injectivity. -/
structure OrthogonalGraphChart (f : M → A) where
  tangent : Submodule ℝ A
  chart : OpenPartialHomeomorph M tangent
  graph : tangent → tangentᗮ
  smooth_chart : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, tangent) ∞ chart chart.source
  smooth_inverse : ContMDiffOn 𝓘(ℝ, tangent) 𝓘(ℝ, E) ∞ chart.symm chart.target
  smooth_graph : ContDiffOn ℝ ∞ graph chart.target
  graph_eq : ∀ u ∈ chart.target,
    tangent.orthogonalDecomposition (f (chart.symm u)) = WithLp.toLp 2 (u, graph u)

/-- A smooth finite-dimensional immersion admits genuine orthogonal graph
charts around every point. No preexisting graph atlas is assumed. -/
theorem exists_orthogonalGraphChart {f : M → A}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, A) ∞ f)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, A) f x)) (x : M) :
    ∃ q : OrthogonalGraphChart (E := E) f, x ∈ q.chart.source := by
  let φ := chartAt E x
  have hφf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ φ.source := contMDiffOn_chart
  have hφi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ.symm φ.target := contMDiffOn_chart_symm
  have hφd : φ.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨hφf.mdifferentiableOn (by simp), hφi.mdifferentiableOn (by simp)⟩
  have hx : x ∈ φ.source := mem_chart_source E x
  have hfx : ContDiffOn ℝ ∞ (f ∘ φ.symm) φ.target :=
    (hf.comp_contMDiffOn hφi).contDiffOn
  have hdx : Injective (fderiv ℝ (f ∘ φ.symm) (φ x)) := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (φ x) ((hf _).mdifferentiableAt (by simp))
        (hφd.mdifferentiableAt_symm (φ.map_source hx))]
    exact (hi _).comp (hφd.symm.mfderiv_injective (φ.map_source hx))
  obtain ⟨c, g, hc, hac, hcs, hcf, hci, hgs, hge⟩ :=
    exists_smoothGraph_of_injective_fderiv φ.open_target (φ.map_source hx) hfx hdx
  let q := φ.trans c
  refine ⟨{
    tangent := (fderiv ℝ (f ∘ φ.symm) (φ x)).range
    chart := q
    graph := g
    smooth_chart := ?_
    smooth_inverse := ?_
    smooth_graph := ?_
    graph_eq := ?_ }, ?_⟩
  · exact hcf.contMDiffOn.comp (hφf.mono inter_subset_left) (fun z hz => hz.2)
  · exact hφi.comp (hci.contMDiffOn.mono inter_subset_left) (fun z hz => hz.2)
  · exact hgs.mono inter_subset_left
  · intro u hu
    exact hge u hu.1
  · exact ⟨hx, hac⟩

/-- Second countability reduces the constructed graph atlas to countably many
genuine charts. This allows one exceptional-null-set argument in the ambient
Euclidean parameter space. -/
theorem exists_countable_orthogonalGraphCharts [SecondCountableTopology M]
    {f : M → A} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, A) ∞ f)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, A) f x)) :
    ∃ Γ : Set (OrthogonalGraphChart (E := E) f), Γ.Countable ∧
      ∀ x : M, ∃ q ∈ Γ, x ∈ q.chart.source := by
  have hcover : (Set.univ : Set M) ⊆
      ⋃ q : OrthogonalGraphChart (E := E) f, q.chart.source := by
    intro x _
    obtain ⟨q, hq⟩ := exists_orthogonalGraphChart hf hi x
    exact Set.mem_iUnion.mpr ⟨q, hq⟩
  obtain ⟨Γ, hΓ, hΓcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun q : OrthogonalGraphChart (E := E) f => q.chart.source)
    (fun q => q.chart.open_source) hcover
  refine ⟨Γ, hΓ, ?_⟩
  intro x
  simpa only [Set.mem_iUnion, exists_prop] using hΓcover (Set.mem_univ x)

/-- In the compact case, the actual graph chart cover can be chosen finite,
including the empty manifold. -/
theorem exists_finite_orthogonalGraphCharts [CompactSpace M]
    {f : M → A} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, A) ∞ f)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, A) f x)) :
    ∃ Γ : Finset (OrthogonalGraphChart (E := E) f),
      ∀ x : M, ∃ q ∈ Γ, x ∈ q.chart.source := by
  have hcover : (Set.univ : Set M) ⊆
      ⋃ q : OrthogonalGraphChart (E := E) f, q.chart.source := by
    intro x _
    obtain ⟨q, hq⟩ := exists_orthogonalGraphChart hf hi x
    exact Set.mem_iUnion.mpr ⟨q, hq⟩
  obtain ⟨Γ, hΓ⟩ := isCompact_univ.elim_finite_subcover
    (fun q : OrthogonalGraphChart (E := E) f => q.chart.source)
    (fun q => q.chart.open_source) hcover
  refine ⟨Γ, ?_⟩
  intro x
  simpa only [Set.mem_iUnion, exists_prop] using hΓ (Set.mem_univ x)

end Manifold

end GaussBonnetChern.Morse
