import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

/-! # Disjoint bands around finitely many critical values

The construction groups points with the same value before choosing intervals.
It imposes no distinct-critical-points or distinct-critical-values hypothesis.
-/

noncomputable section
open Set Metric
open scoped Topology
namespace GaussBonnetChern

theorem exists_disjoint_criticalValueBands (C : Finset ℝ) (a b : ℝ)
    (hC : ∀ c ∈ C, a < c ∧ c < b) (ρ : C → ℝ) (hρ : ∀ c, 0 < ρ c) :
    ∃ ε : C → ℝ, (∀ c : C, 0 < ε c ∧ ε c < ρ c) ∧
      (∀ c : C, a < (c : ℝ) - ε c ∧ (c : ℝ) + ε c < b) ∧
      Pairwise (fun c d : C ↦
        Disjoint (Icc ((c : ℝ) - ε c) ((c : ℝ) + ε c))
          (Icc ((d : ℝ) - ε d) ((d : ℝ) + ε d))) := by
  classical
  obtain ⟨U, hU, hdis⟩ := C.finite_toSet.t2_separation
  have hrad (c : C) : ∃ r : ℝ, 0 < r ∧ closedBall (c : ℝ) r ⊆ U c ∩ Ioo a b := by
    apply Metric.nhds_basis_closedBall.mem_iff.mp
    exact ((hU c).2.inter isOpen_Ioo).mem_nhds ⟨(hU c).1, hC c c.property⟩
  choose r hr hsub using hrad
  let ε : C → ℝ := fun c ↦ min (r c / 2) (ρ c / 2)
  have hε c : 0 < ε c := lt_min (half_pos (hr c)) (half_pos (hρ c))
  have hεr c : ε c ≤ r c := le_trans (min_le_left _ _) (by linarith [hr c])
  have hερ c : ε c < ρ c := lt_of_le_of_lt (min_le_right _ _) (by linarith [hρ c])
  have hinterval (c : C) : Icc ((c : ℝ) - ε c) ((c : ℝ) + ε c) ⊆ closedBall (c : ℝ) (r c) := by
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hεr c, hx.1, hx.2]
  refine ⟨ε, fun c ↦ ⟨hε c, hερ c⟩, ?_, ?_⟩
  · intro c
    have horder : (c : ℝ) - ε c ≤ (c : ℝ) + ε c := by linarith [hε c]
    exact ⟨(hsub c (hinterval c ⟨le_rfl, horder⟩)).2.1,
      (hsub c (hinterval c ⟨horder, le_rfl⟩)).2.2⟩
  · intro c d hcd
    apply (hdis c.property d.property (fun h ↦ hcd (Subtype.ext h))).mono
    · exact (hinterval c).trans ((hsub c).trans inter_subset_left)
    · exact (hinterval d).trans ((hsub d).trans inter_subset_left)

end GaussBonnetChern
