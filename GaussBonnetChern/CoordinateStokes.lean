import GaussBonnetChern.ExteriorDerivative
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! # Stokes on coordinate boxes

The boundary is the actual sum of Lebesgue integrals over coordinate faces.
The factor `(-1)^i` on the upper face and its negative on the lower face
are the outward-normal-first orientation signs. This follows from Mathlib's
proved Bochner divergence theorem applied to the coefficients of a genuine
alternating form; no Stokes assumption is introduced.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff Manifold BigOperators

namespace GaussBonnetChern.CoordinateStokes

abbrev CoordinateSpace (d : ℕ) := Fin d → ℝ

def coordinateBasis (d : ℕ) (i : Fin d) : CoordinateSpace d := Pi.single i 1

variable {n : ℕ}

/-- The ordered tangent tuple to the face obtained by omitting coordinate `i`. -/
def faceBasis (i : Fin (n + 1)) : Fin n → CoordinateSpace (n + 1) :=
  i.removeNth (coordinateBasis (n + 1))

/-- The signed coordinate coefficient whose derivative contributes to `dα`. -/
def signedFaceCoefficient
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n))
    (i : Fin (n + 1)) (x : CoordinateSpace (n + 1)) : ℝ :=
  (-1 : ℝ)^i.val * α x (faceBasis i)

theorem extDeriv_coordinateBasis
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n))
    (x : CoordinateSpace (n + 1)) (hα : DifferentiableAt ℝ α x) :
    extDeriv α x (coordinateBasis (n + 1)) =
      ∑ i, fderiv ℝ (signedFaceCoefficient α i) x (coordinateBasis (n + 1) i) := by
  rw [extDeriv_apply hα]
  apply Finset.sum_congr rfl
  intro i _
  rw [show signedFaceCoefficient α i =
      fun y ↦ (-1 : ℝ)^i.val * α y (faceBasis i) from rfl,
    fderiv_const_mul (hα.continuousAlternatingMap_apply_const (faceBasis i))]
  simp only [faceBasis, smul_apply, smul_eq_mul, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]

theorem contDiffAt_signedFaceCoefficient
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n))
    (i : Fin (n + 1)) (x : CoordinateSpace (n + 1))
    (hα : ContDiffAt ℝ ∞ α x) :
    ContDiffAt ℝ ∞ (signedFaceCoefficient α i) x :=
  contDiffAt_const.mul
    ((ContinuousAlternatingMap.apply ℝ _ ℝ (faceBasis i)).contDiff.contDiffAt.comp x hα)

/-- All face integrals in the box formula are Bochner integrable. -/
theorem integrableOn_signedFaceCoefficient (a b : CoordinateSpace (n + 1))
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n))
    (hα : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ α x)
    (i : Fin (n + 1)) (t : ℝ) (ht : t ∈ Icc (a i) (b i)) :
    IntegrableOn (fun y ↦ signedFaceCoefficient α i (i.insertNth t y))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  have hc : ContinuousOn (signedFaceCoefficient α i) (Icc a b) := fun x hx ↦
    (contDiffAt_signedFaceCoefficient α i x (hα x hx)).continuousAt.continuousWithinAt
  have hinc : Continuous (fun y : CoordinateSpace n ↦
      Fin.insertNth (α := fun _ ↦ ℝ) i t y) := by
    exact (continuous_const (y := t)).finInsertNth i continuous_id
  refine hc.comp hinc.continuousOn ?_
  intro y hy
  exact Fin.insertNth_mem_Icc.mpr ⟨ht, hy⟩

/-- Actual oriented boundary integral on a coordinate box. Lower and upper
faces use the increasing order of the remaining coordinates. -/
def boundaryIntegral (a b : CoordinateSpace (n + 1))
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n)) : ℝ :=
  ∑ i : Fin (n + 1),
    ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        signedFaceCoefficient α i (i.insertNth (b i) y)) -
      ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        signedFaceCoefficient α i (i.insertNth (a i) y))

/-- Stokes for every positive dimension, including degenerate coordinate boxes.
Smoothness is needed only in a neighborhood of each point of the closed box.
Integrability of the differentiated form is proved from this hypothesis. -/
theorem stokes_box (a b : CoordinateSpace (n + 1)) (hab : a ≤ b)
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n))
    (hα : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ α x) :
    (∫ x in Icc a b, extDeriv α x (coordinateBasis (n + 1))) =
      boundaryIntegral a b α := by
  have hc (i : Fin (n + 1)) (x) (hx : x ∈ Icc a b) :
      ContDiffAt ℝ ∞ (signedFaceCoefficient α i) x :=
    contDiffAt_signedFaceCoefficient α i x (hα x hx)
  have hi : IntegrableOn
      (fun x ↦ ∑ i, fderiv ℝ (signedFaceCoefficient α i) x
        (coordinateBasis (n + 1) i)) (Icc a b) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply continuousOn_finsetSum
    intro i _ x hx
    exact (((hc i x hx).fderiv_right (m := ∞) (by simp)).continuousAt.clm_apply
      continuousAt_const).continuousWithinAt
  have heq : (fun x ↦ extDeriv α x (coordinateBasis (n + 1))) =ᶠ[
      ae (volume.restrict (Icc a b))]
      (fun x ↦ ∑ i, fderiv ℝ (signedFaceCoefficient α i) x
        (coordinateBasis (n + 1) i)) := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro x hx
    exact extDeriv_coordinateBasis α x ((hα x hx).differentiableAt (by simp))
  rw [integral_congr_ae heq]
  exact integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (signedFaceCoefficient α) (fun i x ↦ fderiv ℝ (signedFaceCoefficient α i) x)
    ∅ countable_empty
    (fun i x hx ↦ (hc i x hx).continuousAt.continuousWithinAt)
    (by
      intro x hx i
      have hxab : x ∈ Icc a b := by
        constructor <;> intro j
        · exact (hx.1 j (mem_univ j)).1.le
        · exact (hx.1 j (mem_univ j)).2.le
      exact ((hc i x hxab).differentiableAt (by simp)).hasFDerivAt)
    hi

/-- Coordinate Stokes is compatible with the project's actual manifold
exterior derivative. The box lies in a smooth chart, and no global extension
of its local coefficients is assumed smooth outside that chart. -/
theorem stokes_chart_box {M : Type*} [TopologicalSpace M]
    [ChartedSpace (CoordinateSpace (n + 1)) M]
    [IsManifold 𝓘(ℝ, CoordinateSpace (n + 1)) ∞ M]
    (e : OpenPartialHomeomorph M (CoordinateSpace (n + 1)))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace (n + 1)) ∞ M)
    (α : DifferentialForm.Form 𝓘(ℝ, CoordinateSpace (n + 1)) M n)
    (hα : DifferentialForm.IsSmooth α)
    (a b : CoordinateSpace (n + 1)) (hab : a ≤ b) (hbox : Icc a b ⊆ e.target) :
    (∫ x in Icc a b,
      DifferentialForm.chartRepresentation e (DifferentialForm.exteriorDerivative α) x
        (coordinateBasis (n + 1))) =
      boundaryIntegral a b (DifferentialForm.chartRepresentation e α) := by
  calc
    _ = ∫ x in Icc a b,
        extDeriv (DifferentialForm.chartRepresentation e α) x
          (coordinateBasis (n + 1)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      dsimp only
      rw [DifferentialForm.chartRepresentation_exteriorDerivative e he α hα x (hbox hx)]
    _ = _ := stokes_box a b hab _ (fun x hx ↦
      (hα e he).contDiffAt (e.open_target.mem_nhds (hbox hx)))

theorem integrable_extDeriv_coordinateBasis
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n))
    (hα : ContDiff ℝ ∞ α) (hcompact : HasCompactSupport α) :
    Integrable (fun x ↦ extDeriv α x (coordinateBasis (n + 1))) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (ContinuousAlternatingMap.apply ℝ _ ℝ (coordinateBasis (n + 1))).continuous.comp
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ).continuous.comp
        (hα.continuous_fderiv (by simp)))
  · apply hcompact.mono'
    intro x hx
    by_contra hnot
    exact hx (by simp [extDeriv, fderiv_of_notMem_tsupport ℝ hnot,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply])

theorem integrable_signedFaceCoefficient
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n))
    (hα : ContDiff ℝ ∞ α) (hcompact : HasCompactSupport α)
    (i : Fin (n + 1)) (t : ℝ) :
    Integrable (fun y : CoordinateSpace n ↦ signedFaceCoefficient α i (i.insertNth t y)) := by
  have hinc : Isometry (fun y : CoordinateSpace n ↦
      Fin.insertNth (α := fun _ ↦ ℝ) i t y) := by
    apply isometry_iff_dist_eq.mpr
    intro y z
    simp [Fin.dist_insertNth_insertNth]
  have hc : Continuous (signedFaceCoefficient α i) :=
    continuous_iff_continuousAt.mpr (fun x ↦
      (contDiffAt_signedFaceCoefficient α i x hα.contDiffAt).continuousAt)
  have hs : HasCompactSupport (signedFaceCoefficient α i) :=
    hcompact.comp_left (g := fun η : ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n) ↦ (-1 : ℝ)^i.val * η (faceBasis i)) (by simp)
  exact (hc.comp hinc.continuous).integrable_of_hasCompactSupport
    (hs.comp_isClosedEmbedding hinc.isClosedEmbedding)
/-- Stokes on a closed coordinate half-space for a compactly supported smooth form. -/
theorem stokes_halfspace
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n))
    (hα : ContDiff ℝ ∞ α) (hcompact : HasCompactSupport α) (i : Fin (n + 1)) :
    (∫ x in {x : CoordinateSpace (n + 1) | 0 ≤ x i},
      extDeriv α x (coordinateBasis (n + 1))) =
      -(∫ y : CoordinateSpace n, signedFaceCoefficient α i (i.insertNth 0 y)) := by
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.subset_ball_lt 0 (0 : CoordinateSpace (n + 1))
  have hcoord (x : CoordinateSpace (n + 1)) (hx : x ∈ tsupport α) (j : Fin (n + 1)) :
      -R < x j ∧ x j < R := by
    have hn : ‖x‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hbound hx
    have habs : |x j| < R := lt_of_le_of_lt (norm_le_pi_norm x j) hn
    exact abs_lt.mp habs
  let a : CoordinateSpace (n + 1) := fun j ↦ if j = i then 0 else -R
  let b : CoordinateSpace (n + 1) := fun _ ↦ R
  have hab : a ≤ b := by
    intro j
    dsimp [a, b]
    split_ifs <;> linarith
  have hs : Icc a b ⊆ {x : CoordinateSpace (n + 1) | 0 ≤ x i} := by
    intro x hx
    simpa [a] using hx.1 i
  have hbox (x : CoordinateSpace (n + 1)) (hx : 0 ≤ x i) (hxα : x ∈ tsupport α) :
      x ∈ Icc a b := by
    constructor
    · intro j
      dsimp [a]
      split_ifs with hji
      · simpa [hji] using hx
      · exact (hcoord x hxα j).1.le
    · intro j
      exact (hcoord x hxα j).2.le
  have hzero (x : CoordinateSpace (n + 1)) (hx : x ∉ tsupport α) :
      extDeriv α x (coordinateBasis (n + 1)) = 0 := by
    simp [extDeriv, fderiv_of_notMem_tsupport ℝ hx, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (isClosed_le continuous_const (continuous_apply i)).measurableSet hs
    (fun x hx ↦ hzero x (fun hxα ↦ hx.2 (hbox x hx.1 hxα)))]
  rw [stokes_box a b hab α (fun x _ ↦ hα.contDiffAt), boundaryIntegral]
  have hu (j : Fin (n + 1)) (y : CoordinateSpace n) :
      signedFaceCoefficient α j (j.insertNth (b j) y) = 0 := by
    have hz : α (j.insertNth (b j) y) = 0 := image_eq_zero_of_notMem_tsupport (by
      intro hx
      have h := (hcoord (j.insertNth (b j) y) hx j).2
      simpa [b] using h)
    simp [signedFaceCoefficient, hz]
  have hl (j : Fin (n + 1)) (hji : j ≠ i) (y : CoordinateSpace n) :
      signedFaceCoefficient α j (j.insertNth (a j) y) = 0 := by
    have hz : α (j.insertNth (a j) y) = 0 := image_eq_zero_of_notMem_tsupport (by
      intro hx
      have h := (hcoord (j.insertNth (a j) y) hx j).1
      simpa [a, hji] using h)
    simp [signedFaceCoefficient, hz]
  simp_rw [hu, integral_zero, zero_sub]
  rw [Finset.sum_eq_single i]
  · congr 1
    have ha : a i = 0 := by simp [a]
    rw [ha]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hz : α (i.insertNth 0 y) = 0 := image_eq_zero_of_notMem_tsupport (by
      intro hx
      apply hy
      constructor <;> intro j
      · have h := (hcoord (i.insertNth 0 y) hx (i.succAbove j)).1.le
        simpa [a, Fin.succAbove_ne] using h
      · have h := (hcoord (i.insertNth 0 y) hx (i.succAbove j)).2.le
        simpa [b] using h)
    simp [signedFaceCoefficient, hz]
  · intro j _ hji
    simp [hl j hji]
  · simp


/-- A compactly supported smooth exact top form has zero integral on the whole
coordinate space, in every positive dimension. -/
theorem stokes_univ
    (α : CoordinateSpace (n + 1) →
      ContinuousAlternatingMap ℝ (CoordinateSpace (n + 1)) ℝ (Fin n))
    (hα : ContDiff ℝ ∞ α) (hcompact : HasCompactSupport α) :
    (∫ x, extDeriv α x (coordinateBasis (n + 1))) = 0 := by
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.subset_ball_lt 0 (0 : CoordinateSpace (n + 1))
  have hcoord (x : CoordinateSpace (n + 1)) (hx : x ∈ tsupport α) (j : Fin (n + 1)) :
      -R < x j ∧ x j < R := by
    have hn : ‖x‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hbound hx
    have habs : |x j| < R := lt_of_le_of_lt (norm_le_pi_norm x j) hn
    exact abs_lt.mp habs
  let a : CoordinateSpace (n + 1) := fun _ ↦ -R
  let b : CoordinateSpace (n + 1) := fun _ ↦ R
  have hab : a ≤ b := fun _ ↦ le_trans (neg_nonpos.mpr hR.le) hR.le
  have hbox (x : CoordinateSpace (n + 1)) (hxα : x ∈ tsupport α) : x ∈ Icc a b :=
    ⟨fun j ↦ (hcoord x hxα j).1.le, fun j ↦ (hcoord x hxα j).2.le⟩
  have hloc : (∫ x in Icc a b, extDeriv α x (coordinateBasis (n + 1))) =
      ∫ x, extDeriv α x (coordinateBasis (n + 1)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      have hxα : x ∉ tsupport α := fun hxα ↦ hx (hbox x hxα)
      simp [extDeriv, fderiv_of_notMem_tsupport ℝ hxα, ContinuousAlternatingMap.alternatizeUncurryFin_apply])
  rw [← hloc, stokes_box a b hab α (fun x _ ↦ hα.contDiffAt), boundaryIntegral]
  apply Finset.sum_eq_zero
  intro i _
  have hu (y : CoordinateSpace n) : signedFaceCoefficient α i (i.insertNth (b i) y) = 0 := by
    have hz : α (i.insertNth (b i) y) = 0 := image_eq_zero_of_notMem_tsupport (by
      intro hx
      have h := (hcoord (i.insertNth (b i) y) hx i).2
      simpa [b] using h)
    simp [signedFaceCoefficient, hz]
  have hl (y : CoordinateSpace n) : signedFaceCoefficient α i (i.insertNth (a i) y) = 0 := by
    have hz : α (i.insertNth (a i) y) = 0 := image_eq_zero_of_notMem_tsupport (by
      intro hx
      have h := (hcoord (i.insertNth (a i) y) hx i).1
      simpa [a] using h)
    simp [signedFaceCoefficient, hz]
  simp [hu, hl]


end GaussBonnetChern.CoordinateStokes
