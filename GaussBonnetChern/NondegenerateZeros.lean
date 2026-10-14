import GaussBonnetChern.GradientLinearization
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.DiscreteSubset

/-! # Isolated nondegenerate zeros of the actual tangent field

The local scalar coefficients are transported into one fixed tangent fiber.
The derivative of this actual map is exactly `fieldLinearization`; the inverse
function theorem then isolates its zero. Compactness yields finiteness without
connectedness or a nonempty-space assumption.
-/

noncomputable section

open Bundle FiberBundle Module Filter Set
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

/-- Actual local coefficients with their values transported to the fixed fiber at `p`. -/
def fieldInFiber (p : M) (X : (y : M) → TangentSpace (model n) y) :
    M → TangentSpace (model n) p :=
  fun y ↦ ∑ i, fieldCoordinate n M p X i y • coordinateFrame n M p i p

theorem fieldInFiber_self (p : M) (X : (y : M) → TangentSpace (model n) y) :
    fieldInFiber n M p X p = X p := by
  exact (Trivialization.eq_sum_localFrameCoeff_smul
    (I := model n)
    (e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p)
    (b := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis)
    (s := X) (mem_baseSet_trivializationAt' p)).symm

theorem fieldInFiber_of_zero (p : M) {X : (y : M) → TangentSpace (model n) y}
    {y : M} (hy : X y = 0) : fieldInFiber n M p X y = 0 := by
  simp [fieldInFiber, fieldCoordinate, hy]

theorem contMDiffAt_fieldInFiber {p : M} {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) p) :
    ContMDiffAt (model n) 𝓘(ℝ, TangentSpace (model n) p) ∞ (fieldInFiber n M p X) p := by
  apply contMDiffAt_finsetSum
  intro i hi
  exact (contMDiffAt_fieldCoordinate n M hX i).smul contMDiffAt_const

theorem mvfderiv_fieldInFiber {p : M} {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) p) :
    mvfderiv (model n) (fieldInFiber n M p X) p = fieldLinearization n M p X := by
  classical
  have hsum (s : Finset (Fin (2 * n))) :
      mvfderiv (model n) (fun y ↦ ∑ i ∈ s,
        fieldCoordinate n M p X i y • coordinateFrame n M p i p) p =
        ∑ i ∈ s, (mvfderiv (model n) (fieldCoordinate n M p X i) p).smulRight
          (coordinateFrame n M p i p) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, mvfderiv_const]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mvfderiv_fun_add, ih]
      · congr 1
        rw [mvfderiv_fun_smul]
        · simp only [mvfderiv_const, smul_zero, zero_add]
        · exact (contMDiffAt_fieldCoordinate n M hX i).mdifferentiableAt (by simp)
        · exact mdifferentiableAt_const
      · exact ((contMDiffAt_fieldCoordinate n M hX i).smul
          (contMDiffAt_const (c := coordinateFrame n M p i p))).mdifferentiableAt (by simp)
      · exact (contMDiffAt_finsetSum (fun j hj ↦
          (contMDiffAt_fieldCoordinate n M hX j).smul
            (contMDiffAt_const (c := coordinateFrame n M p j p)))).mdifferentiableAt (by simp)
  exact hsum Finset.univ

omit [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)] in
/-- Local injectivity at a point from the actual manifold derivative, by the chart IFT. -/
theorem eventually_eq_of_mvfderiv_isInvertible {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : M → F} {p : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ, F) ∞ f p)
    (hinv : (mvfderiv (model n) f p).IsInvertible) :
    ∀ᶠ y in 𝓝 p, f y = f p → y = p := by
  let c := chartAt (Model n) p
  let g := f ∘ c.symm
  have hg : ContDiffAt ℝ ∞ g (c p) := by
    simpa [g, c, model, mfld_simps, chartAt_self_eq, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp hf).2
  have hd : mvfderiv (model n) f p = fderiv ℝ g (c p) := by
    simpa [g, c, model, writtenInExtChartAt, mfld_simps, chartAt_self_eq] using
      (hf.mdifferentiableAt (by simp)).mvfderiv
  obtain ⟨e, he⟩ := hinv
  let e' : Model n ≃L[ℝ] F := e
  have hge : HasFDerivAt g (e' : Model n →L[ℝ] F) (c p) := by
    change HasFDerivAt g (e : TangentSpace (model n) p →L[ℝ] F) (c p)
    rw [he, hd]
    exact (hg.differentiableAt (by simp)).hasFDerivAt
  let U := hg.toOpenPartialHomeomorph g hge (by simp)
  have hcp : c p ∈ U.source := hg.mem_toOpenPartialHomeomorph_source hge (by simp)
  have hnhds : ∀ᶠ y in 𝓝 p, c y ∈ U.source :=
    (c.continuousAt (mem_chart_source (Model n) p)).eventually (U.open_source.mem_nhds hcp)
  filter_upwards [hnhds, c.open_source.mem_nhds (mem_chart_source (Model n) p)] with y hy hys hfy
  apply c.injOn hys (mem_chart_source (Model n) p)
  apply U.injOn hy hcp
  change g (c y) = g (c p)
  simpa only [g, Function.comp_apply, c.left_inv hys,
    c.left_inv (mem_chart_source (Model n) p)] using hfy

/-- Every zero with invertible actual linearization is isolated. -/
theorem eventually_eq_of_nondegenerate_zero {p : M}
    {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) p)
    (hp : X p = 0) (hinv : (fieldLinearization n M p X).IsInvertible) :
    ∀ᶠ y in 𝓝 p, X y = 0 → y = p := by
  have hinv' : (mvfderiv (model n) (fieldInFiber n M p X) p).IsInvertible := by
    rwa [mvfderiv_fieldInFiber n M hX]
  filter_upwards [eventually_eq_of_mvfderiv_isInvertible n M
    (contMDiffAt_fieldInFiber n M hX) hinv'] with y hy hzero
  apply hy
  rw [fieldInFiber_of_zero n M p hzero, fieldInFiber_self, hp]

/-- Closedness is proved from the actual local coefficients, with no global trivialization. -/
theorem isClosed_field_zeroSet {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X)) :
    IsClosed {p : M | X p = 0} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hne : fieldInFiber n M p X p ≠ 0 := by
    rwa [fieldInFiber_self]
  have hnear := (ContinuousAt.ne_iff_eventually_ne
    (contMDiffAt_fieldInFiber n M (hX p)).continuousAt continuousAt_const).mp hne
  filter_upwards [hnear] with y hy
  exact fun hyzero ↦ hy (fieldInFiber_of_zero n M p hyzero)

theorem isDiscrete_field_zeroSet {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X))
    (hinv : ∀ p, X p = 0 → (fieldLinearization n M p X).IsInvertible) :
    IsDiscrete {p : M | X p = 0} := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro p hp
  obtain ⟨U, hU, hUopen, hpU⟩ := eventually_nhds_iff.mp
    (eventually_eq_of_nondegenerate_zero n M (hX p) hp (hinv p hp))
  refine ⟨U, hUopen, ?_⟩
  ext y
  constructor
  · rintro ⟨hyU, hyzero⟩
    exact hU y hyU hyzero
  · rintro rfl
    exact ⟨hpU, hp⟩

/-- A compact manifold has finitely many zeros when all of them are nondegenerate. -/
theorem finite_field_zeroSet [CompactSpace M]
    {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X))
    (hinv : ∀ p, X p = 0 → (fieldLinearization n M p X).IsInvertible) :
    {p : M | X p = 0}.Finite :=
  (isClosed_field_zeroSet n M hX).isCompact.finite (isDiscrete_field_zeroSet n M hX hinv)

theorem finite_field_zeroSet_of_det_ne_zero [CompactSpace M]
    {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X))
    (hdet : ∀ p, X p = 0 → LinearMap.det (fieldLinearization n M p X).toLinearMap ≠ 0) :
    {p : M | X p = 0}.Finite := by
  apply finite_field_zeroSet n M hX
  intro p hp
  exact ⟨(fieldLinearization n M p X).toContinuousLinearEquivOfDetNeZero (hdet p hp),
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _⟩

/-- Injectivity of the actual square linearization suffices in every finite dimension. -/
theorem finite_field_zeroSet_of_injective [CompactSpace M]
    {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X))
    (hinj : ∀ p, X p = 0 → Function.Injective (fieldLinearization n M p X)) :
    {p : M | X p = 0}.Finite := by
  apply finite_field_zeroSet_of_det_ne_zero n M hX
  intro p hp
  intro hzero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero)
    (LinearMap.ker_eq_bot.mpr (hinj p hp))

theorem finite_field_zeroSet_of_connection_det_ne_zero [CompactSpace M]
    {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X))
    (hdet : ∀ p, X p = 0 → LinearMap.det (connection n M X p).toLinearMap ≠ 0) :
    {p : M | X p = 0}.Finite := by
  apply finite_field_zeroSet_of_det_ne_zero n M hX
  intro p hp
  rw [fieldLinearization_eq_connection n M (hX p) hp]
  exact hdet p hp

/-- Actual nondegenerate critical points are finite on a compact manifold. -/
theorem finite_criticalSet_of_hessian_det_ne_zero [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hdet : ∀ p, mvfderiv (model n) f p = 0 → (hessianMatrix n M f p).det ≠ 0) :
    {p : M | mvfderiv (model n) f p = 0}.Finite := by
  have h := finite_field_zeroSet_of_connection_det_ne_zero n M
    (contMDiff_gradient n M hf) (by
      intro p hp
      rw [← hessianMatrix_det]
      exact hdet p ((gradient_eq_zero_iff n M f p).mp hp))
  simpa only [gradient_eq_zero_iff] using h

end GaussBonnetChern
