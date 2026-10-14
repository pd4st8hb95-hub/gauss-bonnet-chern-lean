import GaussBonnetChern.AngularVerticalDeterminant
import GaussBonnetChern.FieldChartScaling
import GaussBonnetChern.ChernLocalTransgression
import GaussBonnetChern.ChernAngularForm

/-! # Local integrability and the actual radial angular limit

The integral limit below derives its integrability from local regularity of
the actual inputs. No smoothness premise for a rescaled sphere form and no
extra uniform estimate is supplied to the theorem. The identification with
the geometric frame pullback is a separate pointwise identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Bundle

namespace GaussBonnetChern.ChernLocalIndex
open DifferentialForm AngularPolynomial AngularBoundary AngularVertical
open Module Metric Set Filter MeasureTheory

section Ambient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (finrank ℝ E = d+1)]

/-- Actual inverse-chart coefficient of an ambient restricted form. -/
theorem chartRepresentation_ambientSphereRestriction
    (β : E → Fiber (E := E) d)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ e.target) :
    chartRepresentation e (ambientSphereRestriction (fun u => β u)) y =
      (β (e.symm y : E)).compContinuousLinearMap
        (fderiv ℝ (fun z => (e.symm z : E)) y) := by
  have hc := mvfderiv_comp y
    ((contMDiff_coe_sphere (n := d) (m := ∞) (e.symm y)).mdifferentiableAt (by simp))
    ((contMDiffAt_symm_of_mem_maximalAtlas he hy).mdifferentiableAt (by simp))
  rw [mvfderiv_eq_fderiv] at hc
  ext v
  change β (e.symm y : E)
      (fun j => mvfderiv (𝓡 d) ((↑) : sphere (0:E) 1 → E) (e.symm y)
        (mfderiv (𝓡 d) (𝓡 d) e.symm y (v j))) =
    β (e.symm y : E) (fun j => fderiv ℝ (fun z => (e.symm z : E)) y (v j))
  congr 1
  funext j
  exact (congrArg (fun D => D (v j)) hc).symm

/-- Local continuity of the ambient coefficient gives continuity of the
unique intrinsic sphere coefficient; the chart tangent basis is eliminated
by its actual ratio characterization. -/
theorem continuous_sphereFormCoefficient_ambient
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) {β : E → Fiber (E := E) d}
    (hβ : ∀ u ∈ sphere (0:E) 1, ContinuousAt β u) :
    Continuous (sphereFormCoefficient b (ambientSphereRestriction (fun u => β u))) := by
  rw [continuous_iff_continuousAt]
  intro u
  let e := chartAt (EuclideanSpace ℝ (Fin d)) u
  have he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1) :=
    IsManifold.chart_mem_maximalAtlas u
  have hu : u ∈ e.source := mem_chart_source _ _
  have hy := e.map_source hu
  have hf : ContDiffAt ℝ ∞ (fun z => (e.symm z : E)) (e u) :=
    ((contMDiff_coe_sphere (n := d) (m := ∞) (e.symm (e u))).comp (e u)
      (contMDiffAt_symm_of_mem_maximalAtlas he hy)).contDiffAt
  have ha : ContinuousAt (fun z => β (e.symm z : E)) (e u) := by
    have hβu : ContinuousAt β (e.symm (e u) : E) := by
      simpa only [e.left_inv hu] using hβ u u.property
    simpa only [Function.comp_def] using
      ContinuousAt.comp (f := fun z : EuclideanSpace ℝ (Fin d) => (e.symm z : E))
        (x := e u) hβu hf.continuousAt
  have hd := (hf.fderiv_right (m := ∞) (by simp)).continuousAt
  have hp : ContinuousAt (fun z => (β (e.symm z : E)).compContinuousLinearMap
      (fderiv ℝ (fun w => (e.symm w : E)) z)) (e u) := by
    convert (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.continuousAt.comp hd).clm_apply ha using 1
    rfl
  have hn : ContinuousAt (sphereCoordinateCoefficient e
      (ambientSphereRestriction (fun v => β v))) (e u) := by
    have hx := (ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℝ (Fin d)) ℝ
      (EuclideanSpace.basisFun (Fin d) ℝ)).continuous.continuousAt.comp hp
    apply hx.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hy] with y hy
    exact congrArg (fun A => A (EuclideanSpace.basisFun (Fin d) ℝ))
      (chartRepresentation_ambientSphereRestriction β e he hy)
  have hden := (contDiffOn_sphereChartDensity b e he).contDiffAt (e.open_target.mem_nhds hy)
  have hquot := hn.div hden.continuousAt (sphereChartDensity_ne_zero b e he (e u) hy)
  have hc := hquot.comp ((contMDiffAt_of_mem_maximalAtlas he hu).continuousAt)
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hu] with x hx
  simpa only [e.left_inv hx, Function.comp_apply, Pi.div_apply] using
    sphereFormCoefficient_chart_ratio b e he (ambientSphereRestriction (fun v => β v))
      (e x) (e.map_source hx)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_sphereFormCoefficient_ambient
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) {β : E → Fiber (E := E) d}
    (hβ : ∀ u ∈ sphere (0:E) 1, ContinuousAt β u) :
    Integrable (sphereFormCoefficient b (ambientSphereRestriction (fun u => β u)))
      (volume : Measure E).toSphere := by
  letI : CompactSpace (sphere (0:E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  simpa only [integrableOn_univ] using
    (continuous_sphereFormCoefficient_ambient b hβ).continuousOn.integrableOn_compact
      isCompact_univ

end Ambient

section Model
variable (n : ℕ) [Fact (0 < n)]

local instance evenSphereDimension : Fact (finrank ℝ (Model n) = (2*n-1)+1) :=
  ⟨by
    simp only [Model, finrank_euclideanSpace, Fintype.card_fin]
    have hn : 0 < n := Fact.out
    omega⟩

/-- The actual radial input is continuous at every unit-sphere point for
all sufficiently small positive radii. Two derivatives of the original
field suffice; the Chern polynomial itself is finite and continuous. -/
theorem eventually_continuousAt_radialAngularFiber
    (b : OrthonormalBasis (Fin (2*n)) ℝ (Model n))
    {f : Model n → Model n} (L : Model n ≃L[ℝ] Model n)
    (hf : ContDiffAt ℝ 2 f 0) (hL : fderiv ℝ f 0 = L.toContinuousLinearMap)
    (hzero : f 0 = 0)
    {A : Model n → Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 1}
    {B : Model n → Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 2}
    (hA : ContDiffAt ℝ 1 A 0) (hB : ContDiffAt ℝ 1 B 0) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ u ∈ sphere (0:Model n) 1,
      ContinuousAt (fun v => angularFormFiber n
        (radialAngularInput n b (rawRadialInput n f A B r v))) u := by
  have hF1 : ContDiffAt ℝ 1 f 0 := hf.of_le (by norm_num)
  have hd : HasFDerivAt f L.toContinuousLinearMap 0 :=
    hL ▸ (hF1.differentiableAt (by norm_num)).hasFDerivAt
  filter_upwards [LocalIndex.eventually_sphere_smul (hf.eventually (by norm_num)),
    LocalIndex.eventually_sphere_smul (hA.eventually (by norm_num)),
    LocalIndex.eventually_sphere_smul (hB.eventually (by norm_num)),
    LocalIndex.eventually_rescale_ne_zero L hd hzero] with r hr ha hb hne
  intro u hu
  have hNorm : ContDiffAt ℝ 2 (LocalIndex.normalize (E := Model n)) (f (r • u)) :=
    (LocalIndex.contDiffAt_normalize (E := Model n) (hne u hu)).of_le (by simp)
  have hDil : ContDiffAt ℝ 2 (fun v : Model n => r • v) u := contDiffAt_id.const_smul r
  have hRescale : ContDiffAt ℝ 2 (fun v : Model n => f (r • v)) u := by
    simpa only [Function.comp_def] using (hr u hu).comp u hDil
  have hN : ContDiffAt ℝ 2 (fun v => LocalIndex.normalize (f (r • v))) u := by
    simpa only [Function.comp_def] using hNorm.comp u hRescale
  have hD : ContinuousAt (fderiv ℝ (fun v => LocalIndex.normalize (f (r • v)))) u :=
    (hN.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hAC := (ha u hu).continuousAt.comp (continuousAt_id.const_smul r)
  have hBC := (hb u hu).continuousAt.comp (continuousAt_id.const_smul r)
  have hraw : ContinuousAt (rawRadialInput n f A B r) u :=
    continuousAt_const.prodMk (hN.continuousAt.prodMk (hD.prodMk (hAC.prodMk hBC)))
  simpa only [Function.comp_def] using
    ((continuous_angularFormFiber n).comp (continuous_radialAngularInput n b)).continuousAt.comp hraw

/-- The genuine finite Chern radial polynomial has boundary integral tending
to the local determinant sign. Integrability and uniform estimates are
derived from actual local regularity, with no sphere-form smoothness input. -/
theorem tendsto_radialBoundaryModelIntegral
    (b : OrthonormalBasis (Fin (2*n)) ℝ (Model n))
    {f : Model n → Model n} (L : Model n ≃L[ℝ] Model n)
    (hf : ContDiffAt ℝ 2 f 0) (hL : fderiv ℝ f 0 = L.toContinuousLinearMap)
    (hzero : f 0 = 0)
    {A : Model n → Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 1}
    {B : Model n → Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 2}
    (hA : ContDiffAt ℝ 1 A 0) (hB : ContDiffAt ℝ 1 B 0) :
    Tendsto (fun r => sphereFormIntegral (b.reindex (evenSuccEquiv n Fact.out).symm)
      (radialBoundaryModelForm n b f A B r)) (𝓝[>] (0:ℝ))
      (𝓝 (Real.sign (LinearMap.det L.toLinearMap))) := by
  let γ : sphere (0:Model n) 1 → Fiber (E := Model n) (2*n-1) := fun u =>
    Chern.angularCoefficient n 0 • angularTermFiber n ⟨0, Fact.out⟩
      (fun i => inner ℝ (b i) (LocalIndex.normalize (L u)),
       fun i => componentDifferential b i
         (fderiv ℝ (fun v => LocalIndex.normalize (L v)) u), fun _ _ => 0)
  have hγ : ambientSphereRestriction γ =
      Chern.angularCoefficient n 0 • verticalLinearSphereForm n Fact.out b L := by
    funext u
    ext v
    rfl
  have hγSmooth : IsSmooth (ambientSphereRestriction γ) := by
    rw [hγ, verticalLinearSphereForm_eq_pullback]
    exact (((isSmooth_sphereVolumeForm _).pullback (sphereNormalizedLinearMap L)
      (contMDiff_sphereNormalizedLinearMap L)).const_smul _).const_smul _
  have hi := (eventually_continuousAt_radialAngularFiber n b L hf hL hzero hA hB).mono
    (fun r hr => integrable_sphereFormCoefficient_ambient
      (b.reindex (evenSuccEquiv n Fact.out).symm) hr)
  have hconv := uniform_radial_angularForm n Fact.out b L (hf.of_le (by norm_num))
    hL hzero hA.continuousAt hB.continuousAt
  have hsphere : TendstoUniformlyOn
      (fun r (u : sphere (0:Model n) 1) => angularFormFiber n
        (radialAngularInput n b (rawRadialInput n f A B r (u : Model n)))) γ
      (𝓝[>] (0:ℝ)) univ :=
    (hconv.comp ((↑) : sphere (0:Model n) 1 → Model n)).mono (fun u hu => u.property)
  have ht := tendsto_integral_of_uniform (volume : Measure (Model n)).toSphere hi
    (integrable_sphereFormCoefficient _ _ hγSmooth)
    (uniform_sphereFormCoefficient_of_ambient _ hsphere)
  change Tendsto (fun r => sphereFormIntegral _ (radialBoundaryModelForm n b f A B r))
    _ (𝓝 (sphereFormIntegral _ (ambientSphereRestriction γ))) at ht
  rw [hγ, normalized_verticalLinearSphereForm_integral] at ht
  exact ht

end Model

section OriginalGeometry
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] [Fact (0 < n)]

local instance originalGeometrySphereDimension : Fact (finrank ℝ (Model n) = (2*n-1)+1) :=
  ⟨by
    simp only [Model, finrank_euclideanSpace, Fintype.card_fin]
    have hn : 0 < n := Fact.out
    omega⟩

local instance modelTangentNormedAddCommGroup (x : Model n) :
    NormedAddCommGroup (TangentSpace (model n) x) :=
  inferInstanceAs (NormedAddCommGroup (Model n))

local instance modelTangentNormedSpace (x : Model n) :
    NormedSpace ℝ (TangentSpace (model n) x) :=
  inferInstanceAs (NormedSpace ℝ (Model n))

local instance modelTangentInnerProductSpace (x : Model n) :
    InnerProductSpace ℝ (TangentSpace (model n) x) :=
  inferInstanceAs (InnerProductSpace ℝ (Model n))

/-- The coefficients are the original Levi-Civita connection in the actual
positive frame, pulled into the centered inverse chart. -/
def positiveChartConnectionCoefficients (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (p : M) (z : Model n) :
    Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 1 :=
  fun j k => smoothFrameCoordinateConnection n M
    (chartOrthonormalBasis n M (a.chart i)) (a.chart i) j k ((a.chart i) p + z)

/-- Actual curvature coefficients, with the same convention as the genuine
frame angular form. They are evaluated after differentiating the frame. -/
def positiveChartCurvatureCoefficients (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (p : M) (z : Model n) :
    Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 2 :=
  fun j k => smoothFrameCoordinateCurvature n M
    (chartOrthonormalBasis n M (a.chart i)) (a.chart i) j k ((a.chart i) p + z)

theorem pullback_centeredInverseChart_at (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (p : M)
    {z : Model n} (hz : e p + z ∈ e.target) {k : ℕ} (α : Form (model n) M k) :
    pullback (I := model n) (centeredInverseChart n M e p) α z =
      chartRepresentation e α (e p + z) := by
  have ht : MDifferentiableAt (model n) (model n) (fun w : Model n => e p + w) z :=
    mdifferentiableAt_const.add mdifferentiableAt_id
  have hg := (contMDiffAt_symm_of_mem_maximalAtlas he hz).mdifferentiableAt (by simp)
  have hd := mfderiv_comp z hg ht
  change mfderiv (model n) (model n) (centeredInverseChart n M e p) z = _ at hd
  have hs : mfderiv (model n) (model n) (fun w : Model n => e p + w) z =
      ContinuousLinearMap.id ℝ (Model n) := by
    rw [mfderiv_eq_fderiv, fderiv_const_add, fderiv_fun_id]
  ext v
  simp only [pullback_apply, hd, hs, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rfl

def fieldParametrization (X : (y : M) → TangentSpace (model n) y)
    (g : Model n → M) : Model n → TangentBundle (model n) M :=
  (T% X) ∘ g

theorem frameDirectionCoordinate_fieldParametrization
    (b : ∀ y : M, OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y))
    (X : (y : M) → TangentSpace (model n) y) (g : Model n → M)
    (i : Fin (2*n)) (z : Model n) :
    frameDirectionCoordinate n M b i (fieldParametrization n M X g z) =
      inner ℝ (EuclideanSpace.basisFun (Fin (2*n)) ℝ i)
        (LocalIndex.normalize (chartFieldCoordinates n M b X g z)) := by
  simp only [fieldParametrization, Function.comp_apply, frameDirectionCoordinate,
    EuclideanSpace.basisFun_inner, LocalIndex.normalize, chartFieldCoordinates,
    orthonormalFieldCoordinates, (b (g z)).repr.norm_map,
    PiLp.smul_apply, smul_eq_mul, OrthonormalBasis.repr_apply_apply]

theorem scalarDifferential_component_at {q : Model n → Model n} {z : Model n}
    (hq : DifferentiableAt ℝ q z) (i : Fin (2*n)) :
    scalarDifferential (fun w => inner ℝ (EuclideanSpace.basisFun (Fin (2*n)) ℝ i) (q w)) z =
      componentDifferential (EuclideanSpace.basisFun (Fin (2*n)) ℝ) i (fderiv ℝ q z) := by
  ext v
  have hd := ((innerSL ℝ (EuclideanSpace.basisFun (Fin (2*n)) ℝ i)).hasFDerivAt.comp z
    hq.hasFDerivAt).fderiv
  simp only [scalarDifferential_apply, mvfderiv_eq_fderiv, componentDifferential,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]
  exact congrArg (fun D => D (v 0)) hd

theorem normalize_idempotent {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : V) : LocalIndex.normalize (LocalIndex.normalize v) = LocalIndex.normalize v := by
  by_cases hv : v = 0
  · simp [hv, LocalIndex.normalize]
  · exact LocalIndex.normalize_pos_smul v (inv_pos.mpr (norm_pos_iff.mpr hv))

set_option maxHeartbeats 800000 in
/-- Pointwise identification of the actual tangent angular-form pullback
with the radial Chern polynomial. Both powers of the radius are the actual
differential-form pullback powers, and the direction derivative is actual. -/
theorem pullback_frameTangentAngularForm_radial_at
    (b : ∀ y : M, OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y))
    (X : (y : M) → TangentSpace (model n) y) (g : Model n → M)
    (r : ℝ) (u : Model n)
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun y => b y i)) (g (r • u)))
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g (r • u)))
    (hg : ContMDiffAt (model n) (model n) ∞ g (r • u))
    (hne : X (g (r • u)) ≠ 0) :
    pullback (I := model n) (fun w => fieldParametrization n M X g (r • w))
      (frameTangentAngularForm n M b) u =
    angularFormFiber n (radialAngularInput n (EuclideanSpace.basisFun (Fin (2*n)) ℝ)
      (rawRadialInput n (chartFieldCoordinates n M b X g)
        (fun z i j => pullback (I := model n) g (smoothFrameConnectionOneForm n M b i j) z)
        (fun z i j => pullback (I := model n) g (smoothFrameCurvatureTwoForm n M b i j) z) r u)) := by
  let dil : Model n → Model n := fun w => r • w
  let φ : Model n → TangentBundle (model n) M := fun w => fieldParametrization n M X g (r • w)
  let q : Model n → Model n := fun w => LocalIndex.normalize (chartFieldCoordinates n M b X g (r • w))
  let A : Model n → Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 1 :=
    fun z i j => (show Fiber (E := Model n) 1 from
      pullback (I := model n) g (smoothFrameConnectionOneForm n M b i j) z)
  let B : Model n → Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 2 :=
    fun z i j => (show Fiber (E := Model n) 2 from
      pullback (I := model n) g (smoothFrameCurvatureTwoForm n M b i j) z)
  have hdil : ContMDiffAt (model n) (model n) ∞ dil u :=
    (show ContDiffAt ℝ ∞ dil u from contDiffAt_id.const_smul r).contMDiffAt
  have hφ : ContMDiffAt (model n) (model n).tangent ∞ φ u := (hX.comp (r • u) hg).comp u hdil
  have hF := (contDiffAt_chartFieldCoordinates n M hb hX hg).comp u (contDiffAt_id.const_smul r)
  have hFne : chartFieldCoordinates n M b X g (r • u) ≠ 0 := by
    intro hz
    apply hne
    apply (b (g (r • u))).repr.injective
    simpa only [chartFieldCoordinates, orthonormalFieldCoordinates,
      Function.comp_apply, map_zero] using hz
  have hNorm : ContDiffAt ℝ ∞ (LocalIndex.normalize (E := Model n))
      (chartFieldCoordinates n M b X g (r • u)) :=
    LocalIndex.contDiffAt_normalize (E := Model n) hFne
  have hqCD : ContDiffAt ℝ ∞ q u := by
    simpa only [q, Function.comp_def] using hNorm.comp u hF
  have hq : DifferentiableAt ℝ q u := hqCD.differentiableAt (by simp)
  have hcoord (i : Fin (2*n)) :
      (frameDirectionCoordinate n M b i) ∘ φ =
        (fun w => inner ℝ (EuclideanSpace.basisFun (Fin (2*n)) ℝ i) (q w)) := by
    funext w
    exact frameDirectionCoordinate_fieldParametrization n M b X g i (r • w)
  have hbase : (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) ∘ φ = g ∘ dil := rfl
  have hπ : MDifferentiableAt (model n).tangent (model n)
      (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) (φ u) :=
    (contMDiffAt_proj (n := ∞) (TangentSpace (model n) : M → Type _)).mdifferentiableAt (by simp)
  have hc (i j : Fin (2*n)) :
      (show Fiber (E := Model n) 1 from
        pullback (I := model n) (g ∘ dil) (smoothFrameConnectionOneForm n M b i j) u) =
        r • A (r • u) i j := by
    rw [pullback_comp_at dil g _ u (hdil.mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp)), AngularScaling.pullback_dilation]
    simp only [pow_one]
    rfl
  have hcurv (i j : Fin (2*n)) :
      (show Fiber (E := Model n) 2 from
        pullback (I := model n) φ (frameTangentCurvatureForm n M b i j) u) =
        r^2 • B (r • u) i j := by
    rw [frameTangentCurvatureForm,
      ← pullback_comp_at φ (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) _ u
        (hφ.mdifferentiableAt (by simp))
        hπ, hbase]
    rw [pullback_comp_at dil g _ u (hdil.mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp)), AngularScaling.pullback_dilation]
  have hθ (i : Fin (2*n)) :
      (show Fiber (E := Model n) 1 from pullback (I := model n) φ (frameTangentDirectionForm n M b i) u) =
      componentDifferential (EuclideanSpace.basisFun (Fin (2*n)) ℝ) i (fderiv ℝ q u) +
        r • ∑ j, inner ℝ (EuclideanSpace.basisFun (Fin (2*n)) ℝ j) (q u) •
          A (r • u) i j := by
    rw [pullback_frameTangentDirectionForm_at n M b φ u (hφ.mdifferentiableAt (by simp)) hb hne i,
      hcoord, scalarDifferential_component_at n hq i, hbase]
    simp_rw [hc, show ∀ j, frameDirectionCoordinate n M b j (φ u) =
      inner ℝ (EuclideanSpace.basisFun (Fin (2*n)) ℝ j) (q u) from
        fun j => congrFun (hcoord j) u]
    simp only [Finset.smul_sum, smul_smul, mul_comm]
  have hpoly := congrFun (Chern.pullback_angularForm
    (E := Model n) (F := Model n × Model n) (P := Model n) (Q := TangentBundle (model n) M) φ n
    (frameDirectionCoordinate n M b) (frameTangentDirectionForm n M b)
    (frameTangentCurvatureForm n M b)) u
  have hpoly' : (show Fiber (E := Model n) (2*n-1) from
      pullback (I := model n) φ (frameTangentAngularForm n M b) u) =
      angularFormFiber n (radialAngularInput n (EuclideanSpace.basisFun (Fin (2*n)) ℝ)
        (rawRadialInput n (chartFieldCoordinates n M b X g) A B r u)) := by
    change pullback (I := model n) φ
        (Chern.angularForm n (frameDirectionCoordinate n M b) (frameTangentDirectionForm n M b)
          (frameTangentCurvatureForm n M b)) u = _
    rw [hpoly, angularForm_evaluation]
    apply congrArg (angularFormFiber (E := Model n) n)
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      change frameDirectionCoordinate n M b i (φ u) =
        inner ℝ (EuclideanSpace.basisFun (Fin (2*n)) ℝ i) (q u)
      exact congrFun (hcoord i) u
    · funext i
      change (show Fiber (E := Model n) 1 from
        pullback (I := model n) φ (frameTangentDirectionForm n M b i) u) =
        componentDifferential (EuclideanSpace.basisFun (Fin (2*n)) ℝ) i (fderiv ℝ q u) +
          r • ∑ j, inner ℝ (EuclideanSpace.basisFun (Fin (2*n)) ℝ j) (q u) • A (r • u) i j
      exact hθ i
    · funext i j
      change (show Fiber (E := Model n) 2 from
        pullback (I := model n) φ (frameTangentCurvatureForm n M b i j) u) =
        r^2 • B (r • u) i j
      exact hcurv i j
  exact hpoly'

/-- The actual normalized field section over a centered coordinate sphere.
The nonzero proof is supplied only for the radius at which it is defined. -/
def positiveChartNormalizedSphereMap (a : FiniteOrientedAtlas n M) (i : Fin a.card)
    (X : (y : M) → TangentSpace (model n) y) (p : M) (r : ℝ)
    (H : ∀ u : sphere (0:Model n) 1,
      X (centeredInverseChart n M (a.chart i) p (r • (u:Model n))) ≠ 0) :
    sphere (0:Model n) 1 → UnitTangentSphere n M :=
  fun u => UnitTangentSphere.ofNonzero n M
    (centeredInverseChart n M (a.chart i) p (r • (u:Model n)))
    (X (centeredInverseChart n M (a.chart i) p (r • (u:Model n)))) (H u)

/-- Totalized boundary form; the zero branch is never used for sufficiently
small positive radii at a nondegenerate zero, as proved below. -/
def positiveChartAngularBoundary (a : FiniteOrientedAtlas n M) (i : Fin a.card)
    (X : (y : M) → TangentSpace (model n) y) (p : M) (r : ℝ) :
    Form (𝓡 (2*n-1)) (sphere (0:Model n) 1) (2*n-1) := by
  classical
  exact if H : ∀ u : sphere (0:Model n) 1,
      X (centeredInverseChart n M (a.chart i) p (r • (u:Model n))) ≠ 0 then
    pullback (I := 𝓡 (2*n-1)) (positiveChartNormalizedSphereMap n M a i X p r H)
      (atlasSphereAngularForm n M a)
  else 0

/-- The genuine normalized section pullback is exactly the radial polynomial
in the genuine centered chart and positive frame, on every valid sphere. -/
theorem positiveChartAngularBoundary_eq_model (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (X : (y : M) → TangentSpace (model n) y)
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X)) (p : M) (r : ℝ)
    (H : ∀ u : sphere (0:Model n) 1,
      X (centeredInverseChart n M (a.chart i) p (r • (u:Model n))) ≠ 0)
    (hdom : ∀ u : sphere (0:Model n) 1, (a.chart i) p + r • (u:Model n) ∈ (a.chart i).target) :
    positiveChartAngularBoundary n M a i X p r =
      radialBoundaryModelForm n (EuclideanSpace.basisFun (Fin (2*n)) ℝ)
        (positiveChartField n M a i X p)
        (positiveChartConnectionCoefficients n M a i p)
        (positiveChartCurvatureCoefficients n M a i p) r := by
  classical
  rw [positiveChartAngularBoundary, dif_pos H]
  let e := a.chart i
  let b := chartOrthonormalBasis n M e
  let g := centeredInverseChart n M e p
  let Y := normalizedVectorField n M X
  let φ : Model n → TangentBundle (model n) M := fun z => fieldParametrization n M Y g (r • z)
  let S := positiveChartNormalizedSphereMap n M a i X p r H
  funext u
  have hu : e p + r • (u:Model n) ∈ e.target := hdom u
  have hs : g (r • (u:Model n)) ∈ e.source := e.map_target hu
  have hb : ∀ j, ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun y => b y j)) (g (r • (u:Model n))) :=
    fun j => contMDiffAt_chartOrthonormalBasis n M e (a.smooth i) j hs
  have hg : ContMDiffAt (model n) (model n) ∞ g (r • (u:Model n)) :=
    (contMDiffAt_symm_of_mem_maximalAtlas (a.smooth i) hu).comp (r • (u:Model n))
      (contMDiffAt_const.add contMDiffAt_id)
  have hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) (g (r • (u:Model n))) :=
    contMDiffAt_normalizedVectorField n M (hX _) (H u)
  have hYne : Y (g (r • (u:Model n))) ≠ 0 := by
    have hn : ‖Y (g (r • (u:Model n)))‖ = 1 := norm_normalizedVectorField n M (H u)
    intro hz
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hDil : ContMDiffAt (model n) (model n) ∞
      (fun z : Model n => r • z) (u:Model n) :=
    (show ContDiffAt ℝ ∞ (fun z : Model n => r • z) (u:Model n) from
      contDiffAt_id.const_smul r).contMDiffAt
  have hφ : ContMDiffAt (model n) (model n).tangent ∞ φ (u:Model n) :=
    (hY.comp (r • (u:Model n)) hg).comp (u:Model n) hDil
  have hS : ContMDiffAt (𝓡 (2*n-1)) (sphereBundleModel n) ∞ S u := by
    apply contMDiffAt_to_unitTangentSphere_of_ambient n M
    exact hφ.comp u (contMDiff_coe_sphere (n := 2*n-1) (m := ∞) u)
  have hcoord : chartFieldCoordinates n M b Y g =
      LocalIndex.normalize ∘ chartFieldCoordinates n M b X g := by
    funext z
    exact normalized_field_coordinates n M b X (g z)
  have hpoly := pullback_frameTangentAngularForm_radial_at n M b Y g r (u:Model n)
    hb hY hg hYne
  simp only [rawRadialInput, hcoord, Function.comp_apply, normalize_idempotent] at hpoly
  have hA (j k : Fin (2*n)) :
      pullback (I := model n) g (smoothFrameConnectionOneForm n M b j k) (r • (u:Model n)) =
        positiveChartConnectionCoefficients n M a i p (r • (u:Model n)) j k :=
    pullback_centeredInverseChart_at n M e (a.smooth i) p hu _
  have hB (j k : Fin (2*n)) :
      pullback (I := model n) g (smoothFrameCurvatureTwoForm n M b j k) (r • (u:Model n)) =
        positiveChartCurvatureCoefficients n M a i p (r • (u:Model n)) j k :=
    pullback_centeredInverseChart_at n M e (a.smooth i) p hu _
  simp_rw [hA, hB] at hpoly
  ext v
  change atlasSphereAngularForm n M a (S u)
      (fun j => mfderiv (𝓡 (2*n-1)) (sphereBundleModel n) S u (v j)) = _
  rw [atlasSphereAngularForm_eq_chart n M a i (S u) hs]
  change frameTangentAngularForm n M b (φ (u:Model n))
      (fun j => mfderiv (sphereBundleModel n) 𝓘(ℝ,Model n × Model n)
        ((↑) : UnitTangentSphere n M → TangentBundle (model n) M) (S u)
        (mfderiv (𝓡 (2*n-1)) (sphereBundleModel n) S u (v j))) = _
  have hchain := mfderiv_comp u
    ((contMDiff_sphereInclusion n M (S u)).mdifferentiableAt (by simp))
    (hS.mdifferentiableAt (by simp))
  have hchain' := mfderiv_comp u (hφ.mdifferentiableAt (by simp))
    ((contMDiff_coe_sphere (n := 2*n-1) (m := ∞) u).mdifferentiableAt (by simp))
  have heq : (fun z => (S z).1) = φ ∘ ((↑) : sphere (0:Model n) 1 → Model n) := rfl
  change mfderiv (𝓡 (2*n-1)) (model n).tangent (fun z => (S z).1) u = _ at hchain
  rw [heq, hchain'] at hchain
  have heval := congrArg (fun A => A (fun j =>
    mvfderiv (𝓡 (2*n-1)) ((↑) : sphere (0:Model n) 1 → Model n) u (v j))) hpoly
  change frameTangentAngularForm n M b (φ (u:Model n))
      (fun j => mfderiv (model n) 𝓘(ℝ,Model n × Model n) φ (u:Model n)
        (mvfderiv (𝓡 (2*n-1)) ((↑) : sphere (0:Model n) 1 → Model n) u (v j))) = _ at heval
  convert heval using 1 <;> try rfl
  congr 1
  funext j
  exact (congrArg (fun D => D (v j)) hchain).symm

theorem contDiffAt_positiveChartConnectionCoefficients (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) {p : M} (hp : p ∈ (a.chart i).source) :
    ContDiffAt ℝ ∞ (positiveChartConnectionCoefficients n M a i p) 0 := by
  apply contDiffAt_pi.mpr
  intro j
  apply contDiffAt_pi.mpr
  intro k
  have h := contDiffAt_chartRepresentation_smoothFrameConnection n M
    (chartOrthonormalBasis n M (a.chart i)) j k (a.chart i) (a.smooth i)
    ((a.chart i).map_source hp)
    (fun q => by
      rw [(a.chart i).left_inv hp]
      exact contMDiffAt_chartOrthonormalBasis n M (a.chart i) (a.smooth i) q hp)
  have ht : ContDiffAt ℝ ∞ (fun z : Model n => (a.chart i) p + z) 0 :=
    contDiffAt_const.add contDiffAt_id
  have h' : ContDiffAt ℝ ∞
      (chartRepresentation (a.chart i) (smoothFrameConnectionOneForm n M
        (chartOrthonormalBasis n M (a.chart i)) j k)) ((a.chart i) p + 0) := by
    simpa only [add_zero] using h
  simpa only [positiveChartConnectionCoefficients, smoothFrameCoordinateConnection, Function.comp_def] using
    h'.comp 0 ht

theorem contDiffAt_positiveChartCurvatureCoefficients (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) {p : M} (hp : p ∈ (a.chart i).source) :
    ContDiffAt ℝ ∞ (positiveChartCurvatureCoefficients n M a i p) 0 := by
  apply contDiffAt_pi.mpr
  intro j
  apply contDiffAt_pi.mpr
  intro k
  have h := contDiffAt_smoothFrameCoordinateCurvature n M
    (chartOrthonormalBasis n M (a.chart i)) (a.chart i).open_source
    (fun q => contMDiffOn_chartOrthonormalBasis n M (a.chart i) (a.smooth i) q)
    (a.chart i) (a.smooth i) j k ((a.chart i).map_source hp)
    (by simpa only [(a.chart i).left_inv hp] using hp)
  have ht : ContDiffAt ℝ ∞ (fun z : Model n => (a.chart i) p + z) 0 :=
    contDiffAt_const.add contDiffAt_id
  have h' : ContDiffAt ℝ ∞ (smoothFrameCoordinateCurvature n M
      (chartOrthonormalBasis n M (a.chart i)) (a.chart i) j k) ((a.chart i) p + 0) := by
    simpa only [add_zero] using h
  simpa only [positiveChartCurvatureCoefficients, Function.comp_def] using h'.comp 0 ht

/-- All local analytic inputs are obtained from the user's actual smooth
field, its zero and its nondegenerate linearization, in a chart selected
from the original positive atlas. No coefficient estimate is a premise. -/
theorem exists_positiveChartBoundaryModelIntegral_limit
    (a : FiniteOrientedAtlas n M) {p : M}
    {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) p)
    (hzero : X p = 0) (hi : Function.Injective (fieldLinearization n M p X)) :
    ∃ i : Fin a.card, p ∈ (a.chart i).source ∧
      Tendsto (fun r => sphereFormIntegral
        ((EuclideanSpace.basisFun (Fin (2*n)) ℝ).reindex (evenSuccEquiv n Fact.out).symm)
        (radialBoundaryModelForm n (EuclideanSpace.basisFun (Fin (2*n)) ℝ)
          (positiveChartField n M a i X p)
          (positiveChartConnectionCoefficients n M a i p)
          (positiveChartCurvatureCoefficients n M a i p) r))
        (𝓝[>] (0:ℝ)) (𝓝 (Real.sign (fieldLinearization n M p X).det)) := by
  obtain ⟨i, L, hp, hL, hsign, hC, hD⟩ :=
    exists_positive_normalized_field_limit n M a hX hzero hi
  let e := a.chart i
  let b := chartOrthonormalBasis n M e
  let g := centeredInverseChart n M e p
  have hgp : g 0 = p := centeredInverseChart_zero n M e hp
  have hb : ∀ j, ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun y => b y j)) (g 0) := by
    intro j
    rw [hgp]
    exact contMDiffAt_chartOrthonormalBasis n M e (a.smooth i) j hp
  have hXp : ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g 0) := by rwa [hgp]
  have hF : ContDiffAt ℝ 2 (positiveChartField n M a i X p) 0 :=
    (contDiffAt_chartFieldCoordinates n M hb hXp
      (contMDiffAt_centeredInverseChart n M e (a.smooth i) hp)).of_le (by simp)
  have hz : positiveChartField n M a i X p 0 = 0 := by
    apply chartFieldCoordinates_zero n M b g
    rwa [hgp]
  have ht := tendsto_radialBoundaryModelIntegral n (EuclideanSpace.basisFun (Fin (2*n)) ℝ)
    L hF hL hz
    ((contDiffAt_positiveChartConnectionCoefficients n M a i hp).of_le (by simp))
    ((contDiffAt_positiveChartCurvatureCoefficients n M a i hp).of_le (by simp))
  change Real.sign (LinearMap.det L.toLinearMap) = _ at hsign
  rw [hsign] at ht
  exact ⟨i, hp, ht⟩

/-- Genuine local boundary-index limit. The chart is selected from the
original positive atlas. Its angular form is pulled back by the actual
metric-normalized field section over small coordinate spheres. Its limit
is the determinant sign of the original field linearization. -/
theorem exists_positiveChartAngularBoundaryIntegral_limit
    (a : FiniteOrientedAtlas n M) {p : M}
    {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X))
    (hzero : X p = 0) (hi : Function.Injective (fieldLinearization n M p X)) :
    ∃ i : Fin a.card, p ∈ (a.chart i).source ∧
      (∀ᶠ r in 𝓝[>] (0:ℝ), ∀ u : sphere (0:Model n) 1,
        X (centeredInverseChart n M (a.chart i) p (r • (u:Model n))) ≠ 0) ∧
      Tendsto (fun r => sphereFormIntegral
        ((EuclideanSpace.basisFun (Fin (2*n)) ℝ).reindex (evenSuccEquiv n Fact.out).symm)
        (positiveChartAngularBoundary n M a i X p r))
        (𝓝[>] (0:ℝ)) (𝓝 (Real.sign (fieldLinearization n M p X).det)) := by
  obtain ⟨i, hp, hmodel⟩ :=
    exists_positiveChartBoundaryModelIntegral_limit n M a (hX p) hzero hi
  let e := a.chart i
  let b := chartOrthonormalBasis n M e
  let g := centeredInverseChart n M e p
  have hgp : g 0 = p := centeredInverseChart_zero n M e hp
  have hb : ∀ j, ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun y => b y j)) (g 0) := by
    intro j
    rw [hgp]
    exact contMDiffAt_chartOrthonormalBasis n M e (a.smooth i) j hp
  have hXp : ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g 0) := hX _
  have hz : X (g 0) = 0 := by rwa [hgp]
  have hii : Function.Injective (fieldLinearization n M (g 0) X) := by rwa [hgp]
  have hg := contMDiffAt_centeredInverseChart n M e (a.smooth i) hp
  obtain ⟨L, hL, hC, hD⟩ := exists_normalizedChartField_limit n M hb hXp hg hz hii
    (injective_parametrizationDerivative_centeredInverseChart n M e (a.smooth i) hp)
  have hF : ContDiffAt ℝ 1 (chartFieldCoordinates n M b X g) 0 :=
    (contDiffAt_chartFieldCoordinates n M hb hXp hg).of_le (by simp)
  have hFz : chartFieldCoordinates n M b X g 0 = 0 := chartFieldCoordinates_zero n M b g hz
  have hd : HasFDerivAt (chartFieldCoordinates n M b X g) L.toContinuousLinearMap 0 :=
    hL ▸ (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hnz : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ u : sphere (0:Model n) 1,
      X (g (r • (u:Model n))) ≠ 0 := by
    filter_upwards [LocalIndex.eventually_rescale_ne_zero L hd hFz] with r hr
    intro u hx
    apply hr (u:Model n) u.property
    simp only [chartFieldCoordinates, orthonormalFieldCoordinates,
      Function.comp_apply, hx, map_zero]
  have htarget : ∀ᶠ z in 𝓝 (0:Model n), e p + z ∈ e.target := by
    have ht : ContinuousAt (fun z : Model n => e p + z) 0 := continuousAt_const.add continuousAt_id
    exact ht (by simpa only [add_zero] using e.open_target.mem_nhds (e.map_source hp))
  have hdom : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ u : sphere (0:Model n) 1,
      e p + r • (u:Model n) ∈ e.target := by
    filter_upwards [LocalIndex.eventually_sphere_smul htarget] with r hr
    intro u
    exact hr (u:Model n) u.property
  have heq : (fun r => positiveChartAngularBoundary n M a i X p r) =ᶠ[𝓝[>] (0:ℝ)]
      (fun r => radialBoundaryModelForm n (EuclideanSpace.basisFun (Fin (2*n)) ℝ)
        (positiveChartField n M a i X p)
        (positiveChartConnectionCoefficients n M a i p)
        (positiveChartCurvatureCoefficients n M a i p) r) := by
    filter_upwards [hnz, hdom] with r hr hrd
    exact positiveChartAngularBoundary_eq_model n M a i X hX p r hr hrd
  refine ⟨i, hp, hnz, ?_⟩
  exact hmodel.congr' (heq.mono (fun r hr => congrArg
    (sphereFormIntegral ((EuclideanSpace.basisFun (Fin (2*n)) ℝ).reindex
      (evenSuccEquiv n Fact.out).symm)) hr.symm))

end OriginalGeometry
end GaussBonnetChern.ChernLocalIndex
