import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! # The actual domain obtained by removing coordinate balls

The sets below are defined using actual partial homeomorphisms and metric
balls. In a compact ambient space their complement is compact. When the
closed coordinate balls stay inside the chart targets, the boundary of the
punctured domain is contained in the finite union of coordinate spheres.
Smooth boundary charts, the reverse boundary inclusion, and the induced
orientation are further obligations, not fields or assumptions of a Stokes
interface.
-/

open Set Metric
namespace GaussBonnetChern.PuncturedManifold

variable {E M : Type*} [MetricSpace E] [TopologicalSpace M]

def coordinateBall (e : OpenPartialHomeomorph M E) (c : E) (r : ℝ) : Set M :=
  e.source ∩ e ⁻¹' ball c r

def coordinateClosedBall (e : OpenPartialHomeomorph M E) (c : E) (r : ℝ) : Set M :=
  e.source ∩ e ⁻¹' closedBall c r

def coordinateSphere (e : OpenPartialHomeomorph M E) (c : E) (r : ℝ) : Set M :=
  e.source ∩ e ⁻¹' sphere c r

theorem isOpen_coordinateBall (e : OpenPartialHomeomorph M E) (c : E) (r : ℝ) :
    IsOpen (coordinateBall e c r) := e.isOpen_inter_preimage isOpen_ball

theorem coordinateClosedBall_eq_image (e : OpenPartialHomeomorph M E) (c : E) (r : ℝ)
    (hcover : closedBall c r ⊆ e.target) :
    coordinateClosedBall e c r = e.symm '' closedBall c r := by
  ext x
  constructor
  · intro hx
    exact ⟨e x, hx.2, e.left_inv hx.1⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e.map_target (hcover hy), ?_⟩
    change e (e.symm y) ∈ closedBall c r
    rw [e.right_inv (hcover hy)]
    exact hy

theorem isCompact_coordinateClosedBall [ProperSpace E]
    (e : OpenPartialHomeomorph M E) (c : E) (r : ℝ)
    (hcover : closedBall c r ⊆ e.target) :
    IsCompact (coordinateClosedBall e c r) := by
  rw [coordinateClosedBall_eq_image e c r hcover]
  exact (isCompact_closedBall c r).image_of_continuousOn (e.symm.continuousOn.mono hcover)

theorem closure_coordinateBall_subset [ProperSpace E] [T2Space M]
    (e : OpenPartialHomeomorph M E) (c : E) (r : ℝ)
    (hcover : closedBall c r ⊆ e.target) :
    closure (coordinateBall e c r) ⊆ coordinateClosedBall e c r := by
  refine closure_minimal ?_ (isCompact_coordinateClosedBall e c r hcover).isClosed
  intro x hx
  exact ⟨hx.1, ball_subset_closedBall hx.2⟩

theorem frontier_coordinateBall_subset_coordinateSphere [ProperSpace E] [T2Space M]
    (e : OpenPartialHomeomorph M E) (c : E) (r : ℝ)
    (hcover : closedBall c r ⊆ e.target) :
    frontier (coordinateBall e c r) ⊆ coordinateSphere e c r := by
  intro x hx
  have hcx := closure_coordinateBall_subset e c r hcover (frontier_subset_closure hx)
  have hnot : x ∉ coordinateBall e c r := by
    simpa only [(isOpen_coordinateBall e c r).interior_eq] using hx.2
  refine ⟨hcx.1, ?_⟩
  change dist (e x) c = r
  exact le_antisymm hcx.2 (le_of_not_gt (fun hlt ↦ hnot ⟨hcx.1, hlt⟩))

/-- Delete exactly the indicated open coordinate balls. -/
def puncturedDomain {ι : Type*} (e : ι → OpenPartialHomeomorph M E)
    (c : ι → E) (r : ι → ℝ) : Set M :=
  (⋃ i, coordinateBall (e i) (c i) (r i))ᶜ

theorem isClosed_puncturedDomain {ι : Type*} (e : ι → OpenPartialHomeomorph M E)
    (c : ι → E) (r : ι → ℝ) : IsClosed (puncturedDomain e c r) :=
  (isOpen_iUnion (fun i ↦ isOpen_coordinateBall (e i) (c i) (r i))).isClosed_compl

theorem isCompact_puncturedDomain [CompactSpace M] {ι : Type*}
    (e : ι → OpenPartialHomeomorph M E) (c : ι → E) (r : ι → ℝ) :
    IsCompact (puncturedDomain e c r) := (isClosed_puncturedDomain e c r).isCompact

@[simp] theorem puncturedDomain_empty {ι : Type*} [IsEmpty ι]
    (e : ι → OpenPartialHomeomorph M E) (c : ι → E) (r : ι → ℝ) :
    puncturedDomain e c r = univ := by simp [puncturedDomain]

theorem frontier_puncturedDomain_subset [ProperSpace E] [T2Space M]
    {ι : Type*} [Fintype ι] (e : ι → OpenPartialHomeomorph M E)
    (c : ι → E) (r : ι → ℝ) (hcover : ∀ i, closedBall (c i) (r i) ⊆ (e i).target) :
    frontier (puncturedDomain e c r) ⊆ ⋃ i, coordinateSphere (e i) (c i) (r i) := by
  rw [puncturedDomain, frontier_compl]
  have hf : frontier (⋃ i, coordinateBall (e i) (c i) (r i)) ⊆
      ⋃ i, frontier (coordinateBall (e i) (c i) (r i)) := by
    simpa only [Finset.mem_univ, iUnion_true] using
      Finset.univ.frontier_biUnion_subset (fun i ↦ coordinateBall (e i) (c i) (r i))
  exact hf.trans (iUnion_mono (fun i ↦
    frontier_coordinateBall_subset_coordinateSphere (e i) (c i) (r i) (hcover i)))

theorem isCompact_frontier_puncturedDomain [CompactSpace M] {ι : Type*}
    (e : ι → OpenPartialHomeomorph M E) (c : ι → E) (r : ι → ℝ) :
    IsCompact (frontier (puncturedDomain e c r)) := isClosed_frontier.isCompact

/-- Every finite family of distinct points admits positive radii in the
given charts with closed coordinate balls contained in their targets and
pairwise disjoint in the manifold. These choices are proved to exist. -/
theorem exists_disjoint_coordinateBalls [T2Space M] {ι : Type*} [Fintype ι]
    (p : ι → M) (hp : Function.Injective p)
    (e : ι → OpenPartialHomeomorph M E) (he : ∀ i, p i ∈ (e i).source) :
    ∃ r : ι → ℝ, (∀ i, 0 < r i) ∧
      (∀ i, closedBall (e i (p i)) (r i) ⊆ (e i).target) ∧
      Pairwise (fun i j ↦ Disjoint (coordinateClosedBall (e i) (e i (p i)) (r i))
        (coordinateClosedBall (e j) (e j (p j)) (r j))) := by
  classical
  obtain ⟨U, hU, hdis⟩ := (finite_range p).t2_separation
  have hrad (i : ι) : ∃ r : ℝ, 0 < r ∧
      closedBall (e i (p i)) r ⊆ (e i).target ∩ (e i).symm ⁻¹' U (p i) := by
    apply Metric.nhds_basis_closedBall.mem_iff.mp
    apply ((e i).symm.isOpen_inter_preimage (hU (p i)).2).mem_nhds
    refine ⟨(e i).map_source (he i), ?_⟩
    change (e i).symm (e i (p i)) ∈ U (p i)
    rw [(e i).left_inv (he i)]
    exact (hU (p i)).1
  choose r hr hsub using hrad
  refine ⟨r, hr, fun i ↦ (hsub i).trans inter_subset_left, ?_⟩
  have hcb (i : ι) : coordinateClosedBall (e i) (e i (p i)) (r i) ⊆ U (p i) := by
    intro x hx
    have h := (hsub i hx.2).2
    change (e i).symm (e i x) ∈ U (p i) at h
    rwa [(e i).left_inv hx.1] at h
  intro i j hij
  exact (hdis (mem_range_self i) (mem_range_self j) (fun h ↦ hij (hp h))).mono (hcb i) (hcb j)

section Normed
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [ProperSpace V] [T2Space M]

theorem frontier_coordinateBall (e : OpenPartialHomeomorph M V) (c : V) (r : ℝ)
    (hr : r ≠ 0) (hcover : closedBall c r ⊆ e.target) :
    frontier (coordinateBall e c r) = coordinateSphere e c r := by
  apply subset_antisymm (frontier_coordinateBall_subset_coordinateSphere e c r hcover)
  have himg : e.IsImage (coordinateBall e c r) (ball c r) := by
    intro x hx
    change e x ∈ ball c r ↔ x ∈ e.source ∩ e ⁻¹' ball c r
    simp only [mem_inter_iff, mem_preimage, hx, true_and]
  intro x hx
  apply (himg.frontier hx.1).mp
  rw [_root_.frontier_ball c hr]
  exact hx.2

/-- For finitely many balls with disjoint closed balls, the boundary is
exactly the union of their coordinate spheres. -/
theorem frontier_puncturedDomain {ι : Type*} [Fintype ι]
    (e : ι → OpenPartialHomeomorph M V) (c : ι → V) (r : ι → ℝ)
    (hr : ∀ i, r i ≠ 0)
    (hcover : ∀ i, closedBall (c i) (r i) ⊆ (e i).target)
    (hdis : Pairwise (fun i j ↦ Disjoint (coordinateClosedBall (e i) (c i) (r i))
      (coordinateClosedBall (e j) (c j) (r j)))) :
    frontier (puncturedDomain e c r) = ⋃ i, coordinateSphere (e i) (c i) (r i) := by
  apply subset_antisymm (frontier_puncturedDomain_subset e c r hcover)
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  have hfi : x ∈ frontier (coordinateBall (e i) (c i) (r i)) := by
    rw [frontier_coordinateBall (e i) (c i) (r i) (hr i) (hcover i)]
    exact hi
  rw [puncturedDomain, frontier_compl,
    (isOpen_iUnion (fun j ↦ isOpen_coordinateBall (e j) (c j) (r j))).frontier_eq]
  refine ⟨closure_mono (subset_iUnion (fun j ↦ coordinateBall (e j) (c j) (r j)) i)
    (frontier_subset_closure hfi), ?_⟩
  intro hxU
  obtain ⟨j, hj⟩ := mem_iUnion.mp hxU
  by_cases hji : j = i
  · subst j
    exact ((isOpen_coordinateBall (e i) (c i) (r i)).frontier_eq ▸ hfi).2 hj
  · exact Set.disjoint_left.mp (hdis (Ne.symm hji))
      (closure_coordinateBall_subset (e i) (c i) (r i) (hcover i)
        (frontier_subset_closure hfi)) ⟨hj.1, ball_subset_closedBall hj.2⟩

end Normed

end GaussBonnetChern.PuncturedManifold
