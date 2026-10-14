import GaussBonnetChern.EulerForm
import GaussBonnetChern.AtlasInvariance
import Mathlib.Analysis.InnerProductSpace.Orientation

/-! # The actual Euler form and chartwise Riemannian density

The Gram determinant identity below connects the project's square-root volume
density with the determinant of any orthonormal frame. This retains the exact
curvature convention and normalization of the frozen main statement.
-/

noncomputable section
open Bundle Module MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace GaussBonnetChern

open DifferentialForm

theorem gram_det_eq_sq_basis_det {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin d) ℝ E) (v : Fin d → E) :
    (Matrix.gram ℝ v).det = (b.toBasis.det v) ^ 2 := by
  rw [Matrix.gram_eq_conjTranspose_mul b, Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [starRingEnd_apply, star_trivial]
  have hm : (Matrix.of (fun i j ↦ b.repr (v j) i)).det = b.toBasis.det v := by
    rw [Basis.det_apply]
    congr 1
  rw [hm]
  ring

universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

theorem chartVolumeDensity_eq_abs_det
    (e : OpenPartialHomeomorph M (Model n)) (y : Model n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) (e.symm y))) :
    chartVolumeDensity n M e y = |b.toBasis.det (coordinateVector n M e y)| := by
  unfold chartVolumeDensity
  change Real.sqrt ((Matrix.gram ℝ (coordinateVector n M e y)).det) = _
  rw [gram_det_eq_sq_basis_det b, Real.sqrt_sq_eq_abs]

/-- In a chart-positive orthonormal frame the Euler form coefficient agrees
with the frozen Euler density times the actual Riemannian volume density. -/
theorem frameEulerForm_coordinateVectors
    (e : OpenPartialHomeomorph M (Model n)) (y : Model n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) (e.symm y)))
    (hb : 0 ≤ b.toBasis.det (coordinateVector n M e y)) :
    frameEulerForm n M (e.symm y) b (coordinateVector n M e y) =
      eulerDensity n M (e.symm y) * chartVolumeDensity n M e y := by
  rw [frameEulerForm_eq_density_mul_det, chartVolumeDensity_eq_abs_det,
    abs_of_nonneg hb]

theorem contMDiffAt_coordinateVector
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (y : Model n) (hy : y ∈ e.target) (i : Fin (2 * n)) :
    ContMDiffAt (model n) (model n).tangent ∞
      (fun z ↦ (⟨e.symm z, coordinateVector n M e z i⟩ : TangentBundle (model n) M)) y := by
  have hf := contMDiffAt_symm_of_mem_maximalAtlas he hy
  have hd := hf.mfderiv_const (m := ∞) (by simp)
  have hV : ContMDiffAt (model n) (model n).tangent ∞
      (fun z : Model n ↦ (⟨z, EuclideanSpace.basisFun (Fin (2 * n)) ℝ i⟩ :
        TangentBundle (model n) (Model n))) y :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  exact hd.clm_apply_of_inCoordinates hV hf

theorem contDiffOn_chartMetric_entry
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (i j : Fin (2 * n)) :
    ContDiffOn ℝ ∞ (fun y ↦ chartMetric n M e y i j) e.target := by
  intro y hy
  exact ((contMDiffAt_coordinateVector n M e he y hy i).inner_bundle
    (contMDiffAt_coordinateVector n M e he y hy j)).contDiffAt.contDiffWithinAt

theorem contDiffOn_chartMetric_det
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) :
    ContDiffOn ℝ ∞ (fun y ↦ (chartMetric n M e y).det) e.target := by
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply ContDiffOn.mul contDiffOn_const
  apply contDiffOn_prod
  intro i _
  exact contDiffOn_chartMetric_entry n M e he _ _

theorem contDiffOn_chartVolumeDensity
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) :
    ContDiffOn ℝ ∞ (chartVolumeDensity n M e) e.target := by
  intro y hy
  exact (Real.contDiffAt_sqrt (ne_of_gt (chartMetric_det_pos e he y hy))).comp_contDiffWithinAt y
    (contDiffOn_chartMetric_det n M e he y hy)

theorem continuousOn_chartIntegrand
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (i : Fin a.card) :
    ContinuousOn (chartIntegrand n M a ρ i) (a.chart i).target :=
  (((ρ i).contMDiff.continuous.comp_continuousOn (a.chart i).continuousOn_symm).mul
    ((contMDiff_eulerDensity n M).continuous.comp_continuousOn (a.chart i).continuousOn_symm)).mul
    (contDiffOn_chartVolumeDensity n M (a.chart i) (a.smooth i)).continuousOn

/-- The frozen curvature integral has genuinely integrable summands; no
default value for a nonintegrable Bochner integral is used. -/
theorem integrableOn_chartIntegrand [CompactSpace M]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source)) (i : Fin a.card) :
    IntegrableOn (chartIntegrand n M a ρ i) (a.chart i).target volume := by
  let e := a.chart i
  let K := e '' tsupport (ρ i)
  have hK : IsCompact K := (isClosed_tsupport (ρ i)).isCompact.image_of_continuousOn
    (e.continuousOn.mono (hρ i))
  have hKt : K ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hρ i hx)
  apply (((continuousOn_chartIntegrand n M a ρ i).mono hKt).integrableOn_compact hK).of_forall_sdiff_eq_zero
    e.open_target.measurableSet
  intro y hy
  have hz : ρ i (e.symm y) = 0 := by
    by_contra hz
    exact hy.2 ⟨e.symm y, subset_tsupport (ρ i) hz, e.right_inv hy.1⟩
  simp only [chartIntegrand, show ρ i ((a.chart i).symm y) = 0 from hz, zero_mul]

/-- The actual coordinate basis in a source tangent fiber. -/
def sourceCoordinateBasis (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (x : M) (hx : x ∈ e.source) :
    Basis (Fin (2 * n)) ℝ (TangentSpace (model n) x) :=
  let hd : e.MDifferentiable (model n) (model n) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis.map (hd.mfderiv hx).symm.toLinearEquiv

theorem sourceCoordinateBasis_apply (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (x : M) (hx : x ∈ e.source)
    (i : Fin (2 * n)) :
    sourceCoordinateBasis n M e he x hx i =
      mfderiv (model n) (model n) e.symm (e x) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem sourceCoordinateBasis_det_transition
    (e e' : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (x : M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    (sourceCoordinateBasis n M e' he' x hx').det (sourceCoordinateBasis n M e he x hx) =
      LinearMap.det (fderiv ℝ (e' ∘ e.symm) (e x)).toLinearMap := by
  dsimp only [sourceCoordinateBasis]
  simp only [Basis.det_map]
  let b := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
  let T := (fderiv ℝ (e' ∘ e.symm) (e x)).toLinearMap
  have hv : (fun i ↦ mfderiv (model n) (model n) e' x
      (mfderiv (model n) (model n) e.symm (e x) (b i))) = T ∘ b := by
    funext i
    have htrans := transition_fderiv e e' he he' (e x) (e.map_source hx)
      (by simpa only [e.left_inv hx] using hx')
    have h := congrArg (fun L ↦ L (b i)) htrans
    change fderiv ℝ (e' ∘ e.symm) (e x) (b i) =
      mfderiv (model n) (model n) e' (e.symm (e x))
        (mfderiv (model n) (model n) e.symm (e x) (b i)) at h
    rw [e.left_inv hx] at h
    exact h.symm
  change b.det (fun i ↦ mfderiv (model n) (model n) e' x
      (mfderiv (model n) (model n) e.symm (e x) (b i))) = LinearMap.det T
  rw [hv, Basis.det_comp, Basis.det_self, mul_one]

/-- The orientation in each tangent space selected by the finite positive atlas. -/
def atlasOrientation (a : FiniteOrientedAtlas n M) (x : M) :
    Orientation ℝ (TangentSpace (model n) x) (Fin (2 * n)) :=
  let i := (a.covers x).choose
  (sourceCoordinateBasis n M (a.chart i) (a.smooth i) x (a.covers x).choose_spec).orientation

theorem atlasOrientation_eq_chart (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (x : M) (hx : x ∈ (a.chart i).source) :
    atlasOrientation n M a x =
      (sourceCoordinateBasis n M (a.chart i) (a.smooth i) x hx).orientation := by
  unfold atlasOrientation
  rw [Basis.orientation_eq_iff_det_pos, sourceCoordinateBasis_det_transition]
  exact a.positive_transition i (a.covers x).choose x hx (a.covers x).choose_spec

/-- A pointwise orthonormal basis aligned with the atlas orientation. The
orientation choice does not impose a global smooth frame. -/
def atlasOrthonormalFrame (a : FiniteOrientedAtlas n M) (hn : 0 < n) (x : M) :
    OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x) := by
  letI : Nonempty (Fin (2 * n)) := Fin.pos_iff_nonempty.mp (by omega)
  exact (orthonormalFrame n M x).adjustToOrientation (atlasOrientation n M a x)

theorem atlasOrthonormalFrame_orientation (a : FiniteOrientedAtlas n M)
    (hn : 0 < n) (x : M) :
    (atlasOrthonormalFrame n M a hn x).toBasis.orientation = atlasOrientation n M a x := by
  letI : Nonempty (Fin (2 * n)) := Fin.pos_iff_nonempty.mp (by omega)
  exact (orthonormalFrame n M x).orientation_adjustToOrientation _

def atlasEulerForm (a : FiniteOrientedAtlas n M) (hn : 0 < n) :
    Form (model n) M (2 * n) :=
  fun x ↦ frameEulerForm n M x (atlasOrthonormalFrame n M a hn x)

theorem topFormCoefficient_atlasEulerForm (a : FiniteOrientedAtlas n M)
    (hn : 0 < n) (i : Fin a.card) (y : Model n) (hy : y ∈ (a.chart i).target) :
    topFormCoefficient (a.chart i) (atlasEulerForm n M a hn) y =
      eulerDensity n M ((a.chart i).symm y) * chartVolumeDensity n M (a.chart i) y := by
  let e := a.chart i
  let x := e.symm y
  have hx : x ∈ e.source := e.map_target hy
  have hor : (atlasOrthonormalFrame n M a hn x).toBasis.orientation =
      (sourceCoordinateBasis n M e (a.smooth i) x hx).orientation :=
    (atlasOrthonormalFrame_orientation n M a hn x).trans (atlasOrientation_eq_chart n M a i x hx)
  have hpos := (Basis.orientation_eq_iff_det_pos _ _).mp hor
  have hc : (sourceCoordinateBasis n M e (a.smooth i) x hx : Fin (2 * n) → TangentSpace (model n) x) =
      coordinateVector n M e y := by
    funext j
    simp only [sourceCoordinateBasis_apply, x, coordinateVector]
    rw [e.right_inv hy]
  rw [hc] at hpos
  exact frameEulerForm_coordinateVectors n M e y (atlasOrthonormalFrame n M a hn x) hpos.le

theorem integralTopForm_atlasEulerForm (a : FiniteOrientedAtlas n M) (hn : 0 < n)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ) :
    integralTopForm a ρ (atlasEulerForm n M a hn) = curvatureIntegral n M a ρ := by
  unfold integralTopForm curvatureIntegral
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun (a.chart i).open_target.measurableSet
  intro y hy
  simp only [topFormIntegrand, chartIntegrand, topFormCoefficient_atlasEulerForm n M a hn i y hy]
  ring


/-- The canonical coordinate determinant, as a genuine bounded top form. -/
def modelTopForm : Model n [⋀^Fin (2 * n)]→L[ℝ] ℝ where
  toAlternatingMap := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis.det
  cont := by
    change Continuous (fun v ↦ (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis.det v)
    simp_rw [Basis.det_apply]
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun v : Fin (2 * n) → Model n ↦
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis.repr (v j) i)
    simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply] using
      (continuous_const.inner (continuous_apply j))

theorem chartRepresentation_eq_coefficient (e : OpenPartialHomeomorph M (Model n))
    (α : Form (model n) M (2 * n)) (y : Model n) :
    chartRepresentation e α y = topFormCoefficient e α y • modelTopForm n := by
  ext v
  exact congrArg (fun a : Model n [⋀^Fin (2 * n)]→ₗ[ℝ] ℝ ↦ a v)
    ((chartRepresentation e α y).toAlternatingMap.eq_smul_basis_det
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis)

theorem isSmooth_of_topFormCoefficient
    (α : Form (model n) M (2 * n))
    (h : ∀ e ∈ IsManifold.maximalAtlas (model n) ∞ M,
      ContDiffOn ℝ ∞ (topFormCoefficient e α) e.target) : IsSmooth α := by
  intro e he
  have heq : chartRepresentation e α = fun y ↦ topFormCoefficient e α y • modelTopForm n :=
    funext (chartRepresentation_eq_coefficient n M e α)
  rw [heq]
  exact (h e he).smul contDiffOn_const

set_option backward.isDefEq.respectTransparency false in
theorem contDiffAt_det_fderiv {f : Model n → Model n} {y : Model n}
    (hf : ContDiffAt ℝ ∞ f y) :
    ContDiffAt ℝ ∞ (fun z ↦ LinearMap.det (fderiv ℝ f z).toLinearMap) y := by
  let b := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
  have hd := hf.fderiv_right (m := ∞) (by simp)
  simp_rw [← LinearMap.det_toMatrix b, Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply ContDiffAt.mul contDiffAt_const
  apply contDiffAt_prod
  intro i _
  simp only [LinearMap.toMatrix_apply]
  let L : Model n →L[ℝ] ℝ := (EuclideanSpace.proj (σ i)).comp
    (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).repr.toContinuousLinearMap
  have h := L.contDiff.contDiffAt.comp y (hd.clm_apply (contDiffAt_const (c := b i)))
  change ContDiffAt ℝ ∞ (fun z ↦ (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).repr
    (fderiv ℝ f z (b i)) (σ i)) y at h
  simpa only [b, OrthonormalBasis.coe_toBasis_repr_apply] using! h

theorem isSmooth_atlasEulerForm (a : FiniteOrientedAtlas n M) (hn : 0 < n) :
    IsSmooth (atlasEulerForm n M a hn) := by
  apply isSmooth_of_topFormCoefficient n M
  intro e he y hy
  obtain ⟨i, hi⟩ := a.covers (e.symm y)
  let τ := (a.chart i) ∘ e.symm
  have hτ : ContDiffAt ℝ ∞ τ y :=
    ((contMDiffAt_of_mem_maximalAtlas (a.smooth i) hi).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas he hy)).contDiffAt
  have hφ : ContDiffAt ℝ ∞
      (fun z ↦ eulerDensity n M ((a.chart i).symm z) *
        chartVolumeDensity n M (a.chart i) z) (τ y) :=
    (((contMDiff_eulerDensity n M).contMDiffAt.comp (τ y)
      (contMDiffAt_symm_of_mem_maximalAtlas (a.smooth i) ((a.chart i).map_source hi))).contDiffAt).mul
      ((contDiffOn_chartVolumeDensity n M (a.chart i) (a.smooth i)).contDiffAt
        ((a.chart i).open_target.mem_nhds ((a.chart i).map_source hi)))
  have hproduct := (contDiffAt_det_fderiv n hτ).mul (hφ.comp y hτ)
  apply (hproduct.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [e.open_target.mem_nhds hy,
    (e.continuousAt_symm hy).preimage_mem_nhds ((a.chart i).open_source.mem_nhds hi)]
    with z hz hzi
  rw [topFormCoefficient_transition e (a.chart i) he (a.smooth i)
    (atlasEulerForm n M a hn) z hz hzi]
  simp only [τ, Function.comp_apply]
  rw [topFormCoefficient_atlasEulerForm n M a hn i ((a.chart i) (e.symm z))
      ((a.chart i).map_source hzi)]



set_option backward.isDefEq.respectTransparency false in
theorem chartVolumeDensity_sourceCoordinateBasis
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (x : M) (hx : x ∈ e.source)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x)) :
    chartVolumeDensity n M e (e x) =
      |b.toBasis.det (sourceCoordinateBasis n M e he x hx)| := by
  have hm : chartMetric n M e (e x) =
      Matrix.gram ℝ (sourceCoordinateBasis n M e he x hx) := by
    ext i j
    simp only [chartMetric, coordinateVector, Matrix.gram_apply,
      sourceCoordinateBasis_apply]
    rw [e.left_inv hx]
  rw [chartVolumeDensity, hm, gram_det_eq_sq_basis_det, Real.sqrt_sq_eq_abs]

/-- Riemannian density transforms by the absolute Jacobian, including between
charts of opposite orientations. -/
theorem chartVolumeDensity_transition_source
    (e e' : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (x : M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    chartVolumeDensity n M e (e x) =
      |LinearMap.det (fderiv ℝ (e' ∘ e.symm) (e x)).toLinearMap| *
        chartVolumeDensity n M e' (e' x) := by
  let b := orthonormalFrame n M x
  rw [chartVolumeDensity_sourceCoordinateBasis n M e he x hx b,
    chartVolumeDensity_sourceCoordinateBasis n M e' he' x hx' b,
    ← sourceCoordinateBasis_det_transition n M e e' he he' x hx hx']
  rw [← (b.toBasis.det_mul_det (sourceCoordinateBasis n M e' he' x hx')
    (sourceCoordinateBasis n M e he x hx)), abs_mul, mul_comm]

theorem chartVolumeDensity_transition
    (e e' : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (y : Model n) (hy : y ∈ e.target) (hy' : e.symm y ∈ e'.source) :
    chartVolumeDensity n M e y =
      |LinearMap.det (fderiv ℝ (e' ∘ e.symm) y).toLinearMap| *
        chartVolumeDensity n M e' (e' (e.symm y)) := by
  simpa only [e.right_inv hy] using chartVolumeDensity_transition_source n M e e' he he'
    (e.symm y) (e.map_target hy) hy'

/-- Density integration uses absolute Jacobians, hence needs no common
orientation between its two charts. -/
theorem weighted_densityIntegral_change_chart
    (e e' : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (φ : M → ℝ)
    (hs : Function.support φ ⊆ e.source) (hs' : Function.support φ ⊆ e'.source) :
    (∫ y in e.target, φ (e.symm y) * chartVolumeDensity n M e y ∂volume) =
      ∫ y in e'.target, φ (e'.symm y) * chartVolumeDensity n M e' y ∂volume := by
  let t := e.symm.trans e'
  have hl : (∫ y in e.target, φ (e.symm y) * chartVolumeDensity n M e y ∂volume) =
      ∫ y in t.source, φ (e.symm y) * chartVolumeDensity n M e y ∂volume := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e.open_target.measurableSet
      Set.inter_subset_left
    intro y hy
    have hz : φ (e.symm y) = 0 := by
      by_contra hz
      exact hy.2 ⟨hy.1, hs' hz⟩
    simp [hz]
  have hr : (∫ y in e'.target, φ (e'.symm y) * chartVolumeDensity n M e' y ∂volume) =
      ∫ y in t.target, φ (e'.symm y) * chartVolumeDensity n M e' y ∂volume := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e'.open_target.measurableSet
      Set.inter_subset_left
    intro y hy
    have hz : φ (e'.symm y) = 0 := by
      by_contra hz
      exact hy.2 ⟨hy.1, hs hz⟩
    simp [hz]
  rw [hl, hr]
  have hd : ∀ y ∈ t.source, HasFDerivAt t (fderiv ℝ (e' ∘ e.symm) y) y := by
    intro y hy
    have ht : ContDiffAt ℝ ∞ (e' ∘ e.symm) y :=
      ((contMDiffAt_of_mem_maximalAtlas he' hy.2).comp y
        (contMDiffAt_symm_of_mem_maximalAtlas he hy.1)).contDiffAt
    exact (ht.differentiableAt (by simp)).hasFDerivAt
  rw [integral_target_eq_integral_abs_det_fderiv_smul volume hd]
  apply setIntegral_congr_fun t.open_source.measurableSet
  intro y hy
  have hy0 : y ∈ e.target := hy.1
  have hy1 : e.symm y ∈ e'.source := hy.2
  change φ (e.symm y) * chartVolumeDensity n M e y =
    |LinearMap.det (fderiv ℝ (e' ∘ e.symm) y).toLinearMap| •
      (φ (e'.symm (e' (e.symm y))) * chartVolumeDensity n M e' (e' (e.symm y)))
  rw [e'.left_inv hy1, chartVolumeDensity_transition n M e e' he he' y hy0 hy1,
    smul_eq_mul]
  ring



theorem curvatureIntegral_partition_refinement [CompactSpace M]
    (hn : 0 < n) (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    {ι : Type*} [Fintype ι] (τ : SmoothPartitionOfUnity ι (model n) M Set.univ) :
    curvatureIntegral n M a ρ = ∑ i, ∑ j,
      ∫ y in (a.chart i).target,
        ((ρ i ((a.chart i).symm y) * τ j ((a.chart i).symm y)) *
          eulerDensity n M ((a.chart i).symm y)) *
            chartVolumeDensity n M (a.chart i) y ∂volume := by
  rw [← integralTopForm_atlasEulerForm n M a hn ρ,
    integralTopForm_partition_refinement a ρ hρ τ (atlasEulerForm n M a hn)
      (isSmooth_atlasEulerForm n M a hn)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply setIntegral_congr_fun (a.chart i).open_target.measurableSet
  intro y hy
  dsimp only
  rw [topFormCoefficient_atlasEulerForm n M a hn i y hy]
  ring

/-- The exact scalar curvature integral from the main statement is independent
of both atlas and subordinate partition, even if the atlases choose opposite
orientations on any collection of connected components. -/
theorem curvatureIntegral_independent [CompactSpace M]
    (hn : 0 < n) (a b : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (τ : SmoothPartitionOfUnity (Fin b.card) (model n) M Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (hτ : τ.IsSubordinate (fun j ↦ (b.chart j).source)) :
    curvatureIntegral n M a ρ = curvatureIntegral n M b τ := by
  classical
  rw [curvatureIntegral_partition_refinement n M hn a ρ hρ τ,
    curvatureIntegral_partition_refinement n M hn b τ hτ ρ, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have h := weighted_densityIntegral_change_chart n M (a.chart i) (b.chart j)
    (a.smooth i) (b.smooth j) (fun x ↦ (ρ i x * τ j x) * eulerDensity n M x)
    ((Function.support_mul_subset_left _ _).trans
      ((Function.support_mul_subset_left _ _).trans ((subset_tsupport _).trans (hρ i))))
    ((Function.support_mul_subset_left _ _).trans
      ((Function.support_mul_subset_right _ _).trans ((subset_tsupport _).trans (hτ j))))
  simpa only [mul_comm (ρ i _) (τ j _)] using h



theorem atlasOrientation_eq_of_compatible (a b : FiniteOrientedAtlas n M)
    (hab : a.Compatible b) (x : M) :
    atlasOrientation n M a x = atlasOrientation n M b x := by
  obtain ⟨i, hi⟩ := a.covers x
  obtain ⟨j, hj⟩ := b.covers x
  rw [atlasOrientation_eq_chart n M a i x hi, atlasOrientation_eq_chart n M b j x hj]
  apply Eq.symm
  rw [Basis.orientation_eq_iff_det_pos, sourceCoordinateBasis_det_transition]
  exact hab i j x hi hj

theorem atlasEulerForm_eq_of_compatible (a b : FiniteOrientedAtlas n M)
    (hab : a.Compatible b) (hn : 0 < n) :
    atlasEulerForm n M a hn = atlasEulerForm n M b hn := by
  funext x
  have ho : (atlasOrthonormalFrame n M a hn x).toBasis.orientation =
      (atlasOrthonormalFrame n M b hn x).toBasis.orientation := by
    rw [atlasOrthonormalFrame_orientation, atlasOrthonormalFrame_orientation]
    exact atlasOrientation_eq_of_compatible n M a b hab x
  exact (frameEulerForm_eq_of_positive n M x (atlasOrthonormalFrame n M b hn x)
    (atlasOrthonormalFrame n M a hn x) ((Basis.orientation_eq_iff_det_pos _ _).mp ho.symm))

variable {n M} in
/-- Opposite atlases have negative cross-transition determinants at all
overlaps. For disconnected manifolds this requires reversal on every component. -/
def FiniteOrientedAtlas.Opposite (a b : FiniteOrientedAtlas n M) : Prop :=
  ∀ i j (x : M), x ∈ (a.chart i).source → x ∈ (b.chart j).source →
    LinearMap.det (fderiv ℝ ((b.chart j) ∘ (a.chart i).symm)
      ((a.chart i) x)).toLinearMap < 0

theorem atlasOrientation_ne_of_opposite (a b : FiniteOrientedAtlas n M)
    (hab : a.Opposite b) (x : M) :
    atlasOrientation n M a x ≠ atlasOrientation n M b x := by
  obtain ⟨i, hi⟩ := a.covers x
  obtain ⟨j, hj⟩ := b.covers x
  rw [atlasOrientation_eq_chart n M a i x hi, atlasOrientation_eq_chart n M b j x hj]
  intro h
  have hp := (Basis.orientation_eq_iff_det_pos _ _).mp h.symm
  rw [sourceCoordinateBasis_det_transition] at hp
  exact (not_lt_of_ge (le_of_lt hp)) (hab i j x hi hj)

theorem atlasEulerForm_neg_of_opposite (a b : FiniteOrientedAtlas n M)
    (hab : a.Opposite b) (hn : 0 < n) :
    atlasEulerForm n M a hn = -atlasEulerForm n M b hn := by
  funext x
  have ho : (atlasOrthonormalFrame n M b hn x).toBasis.orientation ≠
      (atlasOrthonormalFrame n M a hn x).toBasis.orientation := by
    rw [atlasOrthonormalFrame_orientation, atlasOrthonormalFrame_orientation]
    exact (atlasOrientation_ne_of_opposite n M a b hab x).symm
  have hd := (atlasOrthonormalFrame n M b hn x).det_to_matrix_orthonormalBasis_of_opposite_orientation
    (atlasOrthonormalFrame n M a hn x) ho
  have h := frameEulerForm_change_frame n M x
    (atlasOrthonormalFrame n M b hn x).toBasis (atlasOrthonormalFrame n M a hn x).toBasis
  ext v
  have hv := congrArg (fun (formValue : ContinuousAlternatingMap ℝ
    (TangentSpace (model n) x) ℝ (Fin (2 * n))) ↦ formValue v) h
  change frameEulerForm n M x (atlasOrthonormalFrame n M a hn x) v =
    (atlasOrthonormalFrame n M b hn x).toBasis.det (atlasOrthonormalFrame n M a hn x) *
      frameEulerForm n M x (atlasOrthonormalFrame n M b hn x) v at hv
  rw [hd, neg_one_mul] at hv
  exact hv


theorem weighted_topFormIntegral_reverse_chart
    (e e' : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (α : Form (model n) M (2 * n)) (φ : M → ℝ)
    (hs : Function.support φ ⊆ e.source) (hs' : Function.support φ ⊆ e'.source)
    (hp : ∀ x ∈ e.source, x ∈ e'.source →
      LinearMap.det (fderiv ℝ (e' ∘ e.symm) (e x)).toLinearMap < 0) :
    (∫ y in e.target, φ (e.symm y) * topFormCoefficient e α y ∂volume) =
      -(∫ y in e'.target, φ (e'.symm y) * topFormCoefficient e' α y ∂volume) := by
  let t := e.symm.trans e'
  have hl : (∫ y in e.target, φ (e.symm y) * topFormCoefficient e α y ∂volume) =
      ∫ y in t.source, φ (e.symm y) * topFormCoefficient e α y ∂volume := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e.open_target.measurableSet
      Set.inter_subset_left
    intro y hy
    have hz : φ (e.symm y) = 0 := by
      by_contra hz
      exact hy.2 ⟨hy.1, hs' hz⟩
    simp [hz]
  have hr : (∫ y in e'.target, φ (e'.symm y) * topFormCoefficient e' α y ∂volume) =
      ∫ y in t.target, φ (e'.symm y) * topFormCoefficient e' α y ∂volume := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e'.open_target.measurableSet
      Set.inter_subset_left
    intro y hy
    have hz : φ (e'.symm y) = 0 := by
      by_contra hz
      exact hy.2 ⟨hy.1, hs hz⟩
    simp [hz]
  rw [hl, hr]
  have hd : ∀ y ∈ t.source, HasFDerivAt t (fderiv ℝ (e' ∘ e.symm) y) y := by
    intro y hy
    have ht : ContDiffAt ℝ ∞ (e' ∘ e.symm) y :=
      ((contMDiffAt_of_mem_maximalAtlas he' hy.2).comp y
        (contMDiffAt_symm_of_mem_maximalAtlas he hy.1)).contDiffAt
    exact (ht.differentiableAt (by simp)).hasFDerivAt
  rw [integral_target_eq_integral_abs_det_fderiv_smul volume hd, ← integral_neg]
  apply setIntegral_congr_fun t.open_source.measurableSet
  intro y hy
  have hy0 : y ∈ e.target := hy.1
  have hy1 : e.symm y ∈ e'.source := hy.2
  change φ (e.symm y) * topFormCoefficient e α y =
    -(|LinearMap.det (fderiv ℝ (e' ∘ e.symm) y).toLinearMap| •
      (φ (e'.symm (e' (e.symm y))) * topFormCoefficient e' α (e' (e.symm y))))
  rw [e'.left_inv hy1, topFormCoefficient_transition e e' he he' α y hy0 hy1]
  have hpos : LinearMap.det (fderiv ℝ (e' ∘ e.symm) y).toLinearMap < 0 := by
    simpa only [e.right_inv hy0] using hp (e.symm y) (e.map_target hy0) hy1
  rw [abs_of_neg hpos, smul_eq_mul]
  simp only [Function.comp_apply]
  ring



/-- Reversing the atlas orientation negates the integral of any fixed smooth
top form. This is distinct from the invariant scalar Riemannian integral. -/
theorem integralTopForm_neg_of_opposite [CompactSpace M]
    (a b : FiniteOrientedAtlas n M) (hab : a.Opposite b)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (τ : SmoothPartitionOfUnity (Fin b.card) (model n) M Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (hτ : τ.IsSubordinate (fun j ↦ (b.chart j).source))
    (α : Form (model n) M (2 * n)) (hα : IsSmooth α) :
    integralTopForm a ρ α = -integralTopForm b τ α := by
  classical
  rw [integralTopForm_partition_refinement a ρ hρ τ α hα,
    integralTopForm_partition_refinement b τ hτ ρ α hα]
  simp only [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have h := weighted_topFormIntegral_reverse_chart n M (a.chart i) (b.chart j)
    (a.smooth i) (b.smooth j) α (fun x ↦ ρ i x * τ j x)
    ((Function.support_mul_subset_left _ _).trans ((subset_tsupport _).trans (hρ i)))
    ((Function.support_mul_subset_right _ _).trans ((subset_tsupport _).trans (hτ j)))
    (hab i j)
  simpa only [mul_comm (ρ i _) (τ j _)] using h



theorem curvatureIntegral_eq_zero_of_isEmpty [IsEmpty M]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ) :
    curvatureIntegral n M a ρ = 0 := by
  letI : IsEmpty (Fin a.card) := ⟨fun i ↦ isEmptyElim ((a.chart i).symm 0)⟩
  simp [curvatureIntegral]

theorem integralTopForm_eq_zero_of_isEmpty [IsEmpty M]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (α : Form (model n) M (2 * n)) : integralTopForm a ρ α = 0 := by
  letI : IsEmpty (Fin a.card) := ⟨fun i ↦ isEmptyElim ((a.chart i).symm 0)⟩
  simp [integralTopForm]


end GaussBonnetChern
