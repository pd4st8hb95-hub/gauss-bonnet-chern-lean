import GaussBonnetChern.UnitTangentSphere
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! # Local product coordinates for the actual unit tangent sphere

Local orthonormal frames identify norm-one tangent vectors with the standard
unit sphere. These maps use the actual metric frame constructed earlier.
They are not asserted to be globally continuous: only the frame's genuine
open domain is used. These maps support the subsequent smooth-atlas assembly.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern
universe u

/-- Pointwise smoothness into the standard sphere follows from smoothness
of its actual ambient vector. This local version does not assume global
smoothness of a frame extension outside its domain. -/
theorem contMDiffAt_sphere_of_ambient
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {d : ℕ} [Fact (Module.finrank ℝ V = d+1)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H P]
    {f : P → Metric.sphere (0:V) 1} {x : P}
    (hf : ContMDiffAt I 𝓘(ℝ,V) ∞ (fun y ↦ (f y : V)) x) :
    ContMDiffAt I (𝓡 d) ∞ f x := by
  rw [contMDiffAt_iff_target]
  refine ⟨tendsto_subtype_rng.mpr hf.continuousAt, ?_⟩
  let v : Metric.sphere (0:V) 1 := -(f x)
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) d
    (ne_zero_of_mem_unit_sphere v)).repr
  have hv : inner ℝ (v:V) (f x:V) ≠ 1 := by
    have hn : ‖(f x:V)‖ = 1 := by simpa using (f x).2
    norm_num [v, inner_neg_left, real_inner_self_eq_norm_sq, hn]
  have hopen : IsOpen {z : V | innerSL ℝ (v:V) z ≠ (1:ℝ)} :=
    isOpen_ne.preimage (innerSL ℝ (v:V)).continuous
  have hs : ContDiffAt ℝ ∞ (stereoToFun (v:V)) (f x:V) :=
    contDiffOn_stereoToFun.contDiffAt (hopen.mem_nhds hv)
  have hh := (U.contDiff.contMDiff.contMDiffAt.comp (f x:V) hs.contMDiffAt).comp x hf
  convert hh using 1
  funext y
  rfl

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

theorem normalizedDirection_differential_orthogonal (p : M)
    (v : TangentBundle (model n) M)
    (hv : v.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (hv0 : v.2 ≠ 0) (w : TangentSpace (model n).tangent v) :
    ∑ i, normalizedDirectionCoordinate n M p i v *
      mvfderiv (model n).tangent (normalizedDirectionCoordinate n M p i) v w = 0 := by
  let U := normalizedDirectionCoordinate n M p
  have hU (i : Fin (2*n)) : MDifferentiableAt (model n).tangent 𝓘(ℝ) (U i) v :=
    (contMDiffAt_normalizedDirectionCoordinate n M p i v hv hv0).mdifferentiableAt (by simp)
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p
  have hbase : ∀ᶠ q : TangentBundle (model n) M in 𝓝 v, q.1 ∈ e.baseSet :=
    (FiberBundle.continuous_proj (Model n) (TangentSpace (model n) : M → Type _)).continuousAt
      (e.open_baseSet.mem_nhds hv)
  have hzero : ∀ᶠ q : TangentBundle (model n) M in 𝓝 v, q.2 ≠ 0 :=
    (isOpen_nonzeroTangentBundle n M).mem_nhds hv0
  have heq : (fun q ↦ ∑ i, U i q * U i q) =ᶠ[𝓝 v] (fun _ ↦ (1:ℝ)) := by
    filter_upwards [hbase, hzero] with q hq hq0
    simpa only [U, ← pow_two] using sum_sq_normalizedDirectionCoordinate n M p q hq hq0
  have hderivZero : mvfderiv (model n).tangent (fun q ↦ ∑ i, U i q * U i q) v = 0 := by
    calc
      _ = mvfderiv (model n).tangent (fun _ : TangentBundle (model n) M ↦ (1:ℝ)) v :=
        heq.mfderiv_eq
      _ = 0 := mvfderiv_const _
  have hsum : mvfderiv (model n).tangent (fun q ↦ ∑ i, U i q * U i q) v =
      ∑ i, mvfderiv (model n).tangent (fun q ↦ U i q * U i q) v := by
    have h := (HasMFDerivAt.sum (t := Finset.univ)
      (fun i _ ↦ ((hU i).mul (hU i)).hasMFDerivAt)).mfderiv
    have hfun : (fun q ↦ ∑ i, U i q * U i q) = (∑ i, U i * U i) := by
      funext q
      simp
    rw [hfun]
    ext z
    simp only [ContinuousLinearMap.sum_apply]
    change mfderiv (model n).tangent 𝓘(ℝ) (∑ i, U i * U i) v z =
      ∑ i, mfderiv (model n).tangent 𝓘(ℝ) (U i * U i) v z
    rw [h]
    simp only [ContinuousLinearMap.sum_apply]
    rfl
  have hsumw := congrArg (fun L ↦ L w) hsum
  rw [hderivZero] at hsumw
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.sum_apply,
    mvfderiv_fun_mul (hU _) (hU _), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hsumw
  have hdouble : (2:ℝ) * (∑ i, U i v * mvfderiv (model n).tangent (U i) v w) = 0 := by
    rw [Finset.mul_sum]
    convert hsumw.symm using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  change ∑ i, U i v * mvfderiv (model n).tangent (U i) v w = 0
  linarith


abbrev ModelUnitSphere := Metric.sphere (0 : Model n) 1

/-- Actual coordinates of a tangent vector in the local orthonormal basis.
The basis has total values; smoothness is proved only on its local domain. -/
def localFrameCoordinates (p : M) (v : TangentBundle (model n) M) : Model n :=
  (localOrthonormalBasis n M p v.1).repr v.2

theorem localFrameCoordinates_apply (p : M) (v : TangentBundle (model n) M)
    (hv : v.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (i : Fin (2*n)) :
    localFrameCoordinates n M p v i = localDirectionCoordinate n M p i v := by
  simp only [localFrameCoordinates, OrthonormalBasis.repr_apply_apply,
    localOrthonormalBasis_apply n M p hv, localDirectionCoordinate]

@[simp] theorem norm_localFrameCoordinates (p : M) (v : TangentBundle (model n) M) :
    ‖localFrameCoordinates n M p v‖ = ‖v.2‖ :=
  (localOrthonormalBasis n M p v.1).repr.norm_map _

theorem contMDiffAt_localFrameCoordinates (p : M) (v : TangentBundle (model n) M)
    (hv : v.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ContMDiffAt (model n).tangent (model n) ∞ (localFrameCoordinates n M p) v := by
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p
  have heq : localFrameCoordinates n M p =ᶠ[𝓝 v]
      (fun q ↦ WithLp.toLp 2 (fun i ↦ localDirectionCoordinate n M p i q)) := by
    have hbase : ∀ᶠ q : TangentBundle (model n) M in 𝓝 v, q.1 ∈ e.baseSet :=
      (FiberBundle.continuous_proj (Model n) (TangentSpace (model n) : M → Type _)).continuousAt
        (e.open_baseSet.mem_nhds hv)
    filter_upwards [hbase] with q hq
    ext i
    exact localFrameCoordinates_apply n M p q hq i
  have hpi : ContMDiffAt (model n).tangent 𝓘(ℝ, Fin (2*n) → ℝ) ∞
      (fun q : TangentBundle (model n) M ↦ fun i ↦ localDirectionCoordinate n M p i q) v :=
    contMDiffAt_pi_space.mpr (fun i ↦ contMDiffAt_localDirectionCoordinate n M p i v hv)
  have h := (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (n := ∞)).contMDiff.contMDiffAt.comp v hpi
  exact h.congr_of_eventuallyEq heq

/-- Reconstruction by the actual orthonormal basis. -/
def localFrameReconstruct (p : M) (q : M × Model n) : TangentBundle (model n) M :=
  ⟨q.1, (localOrthonormalBasis n M p q.1).repr.symm q.2⟩

theorem contMDiffAt_localFrameReconstruct (p : M) (q : M × Model n)
    (hq : q.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ContMDiffAt ((model n).prod (model n)) (model n).tangent ∞
      (localFrameReconstruct n M p) q := by
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p
  let e₀ := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) q.1
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_fst, ?_⟩
  have hi (i : Fin (2*n)) :
      ContMDiffAt ((model n).prod (model n)) (model n) ∞
        (fun z : M × Model n ↦ z.2 i • (e₀ ⟨z.1, localOrthonormalFrame n M p i z.1⟩).2) q := by
    have hframe := (contMDiffAt_totalSpace.mp
      (contMDiffAt_localOrthonormalFrame n M p i hq)).2
    have hc : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ) ∞
        (fun z : M × Model n ↦ z.2 i) q :=
      (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin (2*n) ↦ ℝ) i).contMDiff.contMDiffAt.comp
        q contMDiffAt_snd
    exact hc.smul (hframe.comp q contMDiffAt_fst)
  have hsum : ContMDiffAt ((model n).prod (model n)) (model n) ∞
      (fun z : M × Model n ↦ ∑ i, z.2 i •
        (e₀ ⟨z.1, localOrthonormalFrame n M p i z.1⟩).2) q := by
    simpa only [Finset.sum_apply] using ContMDiffAt.sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)
  apply hsum.congr_of_eventuallyEq
  have hp : ∀ᶠ z : M × Model n in 𝓝 q, z.1 ∈ e.baseSet :=
    continuous_fst.continuousAt (e.open_baseSet.mem_nhds hq)
  have hq₀ : ∀ᶠ z : M × Model n in 𝓝 q, z.1 ∈ e₀.baseSet :=
    continuous_fst.continuousAt (e₀.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' q.1))
  filter_upwards [hp, hq₀] with z hz hz₀
  change (e₀ ⟨z.1, (localOrthonormalBasis n M p z.1).repr.symm z.2⟩).2 = _
  rw [← e₀.continuousLinearMapAt_apply_of_mem ℝ hz₀,
    ← (localOrthonormalBasis n M p z.1).sum_repr_symm z.2, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, e₀.continuousLinearMapAt_apply_of_mem ℝ hz₀,
    localOrthonormalBasis_apply n M p hz]

/-- Set-theoretic frame coordinates, globally defined to provide the total
functions of a local trivialization. Continuity is local, not postulated. -/
def sphereFrameEquiv (p : M) : UnitTangentSphere n M ≃ M × ModelUnitSphere n where
  toFun v := (v.1.1, ⟨localFrameCoordinates n M p v.1, by
    simpa only [mem_sphere_zero_iff_norm, norm_localFrameCoordinates] using v.2⟩)
  invFun q := ⟨⟨q.1, (localOrthonormalBasis n M p q.1).repr.symm q.2.1⟩, by
    simpa only [LinearIsometryEquiv.norm_map, mem_sphere_zero_iff_norm] using q.2.2⟩
  left_inv v := by
    apply Subtype.ext
    cases v with
    | mk v hv =>
      cases v with
      | mk x w =>
        simp [localFrameCoordinates]
  right_inv q := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [localFrameCoordinates]

@[simp] theorem sphereFrameEquiv_fst (p : M) (v : UnitTangentSphere n M) :
    (sphereFrameEquiv n M p v).1 = UnitTangentSphere.proj n M v := rfl

@[simp] theorem sphereFrameEquiv_symm_proj (p : M) (q : M × ModelUnitSphere n) :
    UnitTangentSphere.proj n M ((sphereFrameEquiv n M p).symm q) = q.1 := rfl

theorem continuousAt_sphereFrameEquiv (p : M) (v : UnitTangentSphere n M)
    (hv : v.1.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ContinuousAt (sphereFrameEquiv n M p) v := by
  refine (UnitTangentSphere.continuous_proj n M).continuousAt.prodMk ?_
  apply tendsto_subtype_rng.mpr
  exact (contMDiffAt_localFrameCoordinates n M p v.1 hv).continuousAt.comp
    continuous_subtype_val.continuousAt

theorem continuousAt_sphereFrameEquiv_symm (p : M) (q : M × ModelUnitSphere n)
    (hq : q.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ContinuousAt (sphereFrameEquiv n M p).symm q := by
  apply tendsto_subtype_rng.mpr
  have hi : ContinuousAt (fun y : M × ModelUnitSphere n ↦ (y.1, y.2.1)) q :=
    continuous_fst.continuousAt.prodMk (continuous_subtype_val.comp continuous_snd).continuousAt
  have hc := (contMDiffAt_localFrameReconstruct n M p (q.1, q.2.1) hq).continuousAt.comp
    (f := fun y : M × ModelUnitSphere n ↦ (y.1, y.2.1)) hi
  exact hc

/-- The actual sphere bundle's local product chart. Its topology is the
subspace topology of the original tangent bundle, not a newly chosen topology. -/
def sphereLocalProduct (p : M) :
    OpenPartialHomeomorph (UnitTangentSphere n M) (M × ModelUnitSphere n) where
  toFun := sphereFrameEquiv n M p
  invFun := (sphereFrameEquiv n M p).symm
  source := UnitTangentSphere.proj n M ⁻¹'
    (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet
  target := Prod.fst ⁻¹'
    (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet
  map_source' _ h := h
  map_target' _ h := h
  left_inv' v _ := (sphereFrameEquiv n M p).symm_apply_apply v
  right_inv' q _ := (sphereFrameEquiv n M p).apply_symm_apply q
  open_source :=
    (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).open_baseSet.preimage
      (UnitTangentSphere.continuous_proj n M)
  open_target :=
    (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).open_baseSet.preimage
      continuous_fst
  continuousOn_toFun := fun v hv ↦ (continuousAt_sphereFrameEquiv n M p v hv).continuousWithinAt
  continuousOn_invFun := fun q hq ↦ (continuousAt_sphereFrameEquiv_symm n M p q hq).continuousWithinAt

theorem mem_sphereLocalProduct_source (v : UnitTangentSphere n M) :
    v ∈ (sphereLocalProduct n M (UnitTangentSphere.proj n M v)).source := by
  change v.1.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) v.1.1).baseSet
  exact FiberBundle.mem_baseSet_trivializationAt' _

section PositiveDimension
variable [Fact (0 < n)]

instance modelUnitSphereDimension : Fact (Module.finrank ℝ (Model n) = (2*n-1)+1) :=
  ⟨by simp only [Model, finrank_euclideanSpace, Fintype.card_fin]
      have hn := Fact.out (p := 0<n)
      omega⟩

/-- The Euclidean model for the true unit tangent sphere, of dimension
`2*n + (2*n-1)`. -/
abbrev SphereBundleModel := Model n × EuclideanSpace ℝ (Fin (2*n-1))

abbrev SphereBundleChartModel := ModelProd (Model n) (EuclideanSpace ℝ (Fin (2*n-1)))

abbrev sphereBundleModel := (model n).prod (𝓡 (2*n-1))

theorem sphereBundleModel_eq_self : sphereBundleModel n = 𝓘(ℝ, SphereBundleModel n) :=
  modelWithCornersSelf_prod.symm

/-- Transition between two frame product coordinates is smooth on the
overlap, by actual smooth frame coordinates and actual sphere inclusion. -/
theorem contMDiffAt_sphereFrameTransition (p q : M)
    (z : M × ModelUnitSphere n)
    (hzp : z.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (hzq : z.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) q).baseSet) :
    ContMDiffAt (sphereBundleModel n) (sphereBundleModel n) ∞
      ((sphereFrameEquiv n M q) ∘ (sphereFrameEquiv n M p).symm) z := by
  have hinc : ContMDiffAt (sphereBundleModel n) ((model n).prod (model n)) ∞
      (fun y : M × ModelUnitSphere n ↦ (y.1, y.2.1)) z :=
    contMDiffAt_fst.prodMk (contMDiff_coe_sphere.contMDiffAt.comp z contMDiffAt_snd)
  have hrec := (contMDiffAt_localFrameReconstruct n M p (z.1,z.2.1) hzp).comp z hinc
  have hcoord := (contMDiffAt_localFrameCoordinates n M q
    (localFrameReconstruct n M p (z.1,z.2.1)) hzq).comp z hrec
  have hsphere : ContMDiffAt (sphereBundleModel n) (𝓡 (2*n-1)) ∞
      (fun y : M × ModelUnitSphere n ↦
        (sphereFrameEquiv n M q ((sphereFrameEquiv n M p).symm y)).2) z :=
    contMDiffAt_sphere_of_ambient hcoord
  exact contMDiffAt_fst.prodMk hsphere

/-- Product-coordinate transitions on their actual partial-homeomorphism
sources. This is the smooth compatibility needed by the sphere atlas. -/
theorem contMDiffOn_sphereLocalProduct_transition (p q : M) :
    ContMDiffOn (sphereBundleModel n) (sphereBundleModel n) ∞
      ((sphereLocalProduct n M p).symm ≫ₕ sphereLocalProduct n M q)
      ((sphereLocalProduct n M p).symm ≫ₕ sphereLocalProduct n M q).source := by
  intro z hz
  exact (contMDiffAt_sphereFrameTransition n M p q z hz.1 hz.2).contMDiffWithinAt

/-- First atlas: genuine local product coordinates on the actual sphere
subspace, with no replacement of its topology. -/
def sphereProductChartedSpace :
    ChartedSpace (M × ModelUnitSphere n) (UnitTangentSphere n M) where
  atlas := Set.range (sphereLocalProduct n M)
  chartAt v := sphereLocalProduct n M (UnitTangentSphere.proj n M v)
  mem_chart_source := mem_sphereLocalProduct_source n M
  chart_mem_atlas v := ⟨_, rfl⟩

/-- Compose the smooth base charts with the existing standard-sphere
stereographic charts to obtain charts in dimension `4*n-1`. -/
instance sphereBundleChartedSpace :
    ChartedSpace (SphereBundleChartModel n) (UnitTangentSphere n M) :=
  letI := sphereProductChartedSpace n M
  ChartedSpace.comp (SphereBundleChartModel n) (M × ModelUnitSphere n) (UnitTangentSphere n M)

instance sphereBundleChartedSpaceSelf :
    ChartedSpace (SphereBundleModel n) (UnitTangentSphere n M) := sphereBundleChartedSpace n M

/-- Smooth compatibility of the composed sphere-bundle atlas follows from
the explicitly proved frame transitions, rather than from an assumed sphere
bundle smoothness field. -/
instance unitTangentSphere_isManifold :
    IsManifold (sphereBundleModel n) ∞ (UnitTangentSphere n M) := by
  letI : ChartedSpace (SphereBundleChartModel n) (SphereBundleModel n) := chartedSpaceSelf _
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨f, ⟨p, rfl⟩, g, hg, rfl⟩ := he
  obtain ⟨f', ⟨q, rfl⟩, g', hg', rfl⟩ := he'
  have hgmax : g ∈ IsManifold.maximalAtlas (sphereBundleModel n) ∞ (M × ModelUnitSphere n) :=
    IsManifold.subset_maximalAtlas hg
  have hg'max : g' ∈ IsManifold.maximalAtlas (sphereBundleModel n) ∞ (M × ModelUnitSphere n) :=
    IsManifold.subset_maximalAtlas hg'
  have hginv := contMDiffOn_symm_of_mem_maximalAtlas hgmax
  have hg'for := contMDiffOn_of_mem_maximalAtlas hg'max
  intro x hx
  have hx' : x ∈ g.target ∧ g.symm x ∈ (sphereLocalProduct n M p).target ∧
      (sphereLocalProduct n M p).symm (g.symm x) ∈ (sphereLocalProduct n M q).source ∧
      sphereLocalProduct n M q ((sphereLocalProduct n M p).symm (g.symm x)) ∈ g'.source := by
    simpa [mfld_simps, Prod.map_def, Function.comp_def, and_assoc] using hx
  have hi := hginv.contMDiffAt (g.open_target.mem_nhds hx'.1)
  have ht := contMDiffAt_sphereFrameTransition n M p q (g.symm x) hx'.2.1 hx'.2.2.1
  have ho := hg'for.contMDiffAt (g'.open_source.mem_nhds hx'.2.2.2)
  have h := ho.comp x (ht.comp x hi)
  rw [sphereBundleModel_eq_self] at h
  convert h.contDiffAt.contDiffWithinAt using 1
  rfl

instance unitTangentSphere_isManifold_self :
    IsManifold 𝓘(ℝ, SphereBundleModel n) ∞ (UnitTangentSphere n M) := by
  simpa only [sphereBundleModel_eq_self] using unitTangentSphere_isManifold n M

end PositiveDimension
end GaussBonnetChern

