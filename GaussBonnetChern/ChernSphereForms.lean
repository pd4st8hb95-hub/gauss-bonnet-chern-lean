import GaussBonnetChern.ChernTransgression
import GaussBonnetChern.SphereBundleManifold
import GaussBonnetChern.FrameStructureEquations

/-! # Actual local Chern forms on the punctured tangent bundle

The direction coordinates are normalized using the given metric. Connection
and curvature forms are pulled back by the actual tangent-bundle projection.
Thus their restriction to the actual unit tangent sphere will be genuine
forms on that sphere bundle. Local frame domains are always explicit.
Positive orientation and global gluing are subsequent obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

section SphereMaps
variable [Fact (0<n)]

theorem contMDiffAt_sphereLocalProduct (p : M) (v : UnitTangentSphere n M)
    (hv : v ∈ (sphereLocalProduct n M p).source) :
    ContMDiffAt (sphereBundleModel n) (sphereBundleModel n) ∞
      (sphereLocalProduct n M p) v := by
  letI : ChartedSpace (SphereBundleChartModel n) (SphereBundleModel n) := chartedSpaceSelf _
  let f := sphereLocalProduct n M p
  let g := chartAt (SphereBundleChartModel n) (f v)
  have hg : g ∈ IsManifold.maximalAtlas (sphereBundleModel n) ∞ (M × ModelUnitSphere n) :=
    IsManifold.chart_mem_maximalAtlas _
  have hchart : f ≫ₕ g ∈ atlas (SphereBundleChartModel n) (UnitTangentSphere n M) :=
    ⟨f, ⟨p,rfl⟩, g, chart_mem_atlas _ _, rfl⟩
  have hvchart : v ∈ (f ≫ₕ g).source := by
    refine ⟨hv, ?_⟩
    change f v ∈ g.source
    exact mem_chart_source _ _
  have hmax : f ≫ₕ g ∈ IsManifold.maximalAtlas (sphereBundleModel n) ∞
      (UnitTangentSphere n M) := IsManifold.subset_maximalAtlas hchart
  have hc := contMDiffAt_of_mem_maximalAtlas hmax hvchart
  have hi := contMDiffAt_symm_of_mem_maximalAtlas hg (g.map_source (mem_chart_source _ _))
  have h := hi.comp v hc
  apply h.congr_of_eventuallyEq
  have hevent : ∀ᶠ w in 𝓝 v, f w ∈ g.source :=
    (continuousAt_sphereFrameEquiv n M p v hv) (g.open_source.mem_nhds (mem_chart_source _ _))
  filter_upwards [hevent] with w hw
  exact (g.left_inv hw).symm

theorem contMDiff_sphereInclusion :
    ContMDiff (sphereBundleModel n) (model n).tangent ∞
      ((↑) : UnitTangentSphere n M → TangentBundle (model n) M) := by
  intro v
  let p := UnitTangentSphere.proj n M v
  have hv := mem_sphereLocalProduct_source n M v
  have hc := contMDiffAt_sphereLocalProduct n M p v hv
  have hinc : ContMDiffAt (sphereBundleModel n) ((model n).prod (model n)) ∞
      (fun w : UnitTangentSphere n M ↦
        ((sphereLocalProduct n M p w).1, ((sphereLocalProduct n M p w).2 : Model n))) v :=
    hc.fst.prodMk (contMDiff_coe_sphere.contMDiffAt.comp v hc.snd)
  have hr := contMDiffAt_localFrameReconstruct n M p
    ((sphereLocalProduct n M p v).1, ((sphereLocalProduct n M p v).2 : Model n))
    (FiberBundle.mem_baseSet_trivializationAt' p)
  have h := hr.comp v hinc
  convert h using 1
  funext w
  exact congrArg (fun z : UnitTangentSphere n M ↦ z.1)
    ((sphereFrameEquiv n M p).symm_apply_apply w).symm

theorem contMDiff_unitTangentSphere_proj :
    ContMDiff (sphereBundleModel n) (model n) ∞ (UnitTangentSphere.proj n M) :=
  (contMDiff_proj (TangentSpace (model n) : M → Type _)).comp (contMDiff_sphereInclusion n M)

/-- Local smoothness into the actual sphere bundle is detected by its
ambient tangent-bundle inclusion. -/
theorem contMDiffAt_to_unitTangentSphere_of_ambient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H P]
    {f : P → UnitTangentSphere n M} {x : P}
    (hf : ContMDiffAt I (model n).tangent ∞ (fun y ↦ (f y).1) x) :
    ContMDiffAt I (sphereBundleModel n) ∞ f x := by
  let p := UnitTangentSphere.proj n M (f x)
  have hp : (f x).1.1 ∈
      (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hb := (contMDiffAt_proj (TangentSpace (model n) : M → Type _)).comp x hf
  have hu := (contMDiffAt_localFrameCoordinates n M p (f x).1 hp).comp x hf
  have hs : ContMDiffAt I (𝓡 (2*n-1)) ∞
      (fun y ↦ (sphereFrameEquiv n M p (f y)).2) x :=
    contMDiffAt_sphere_of_ambient hu
  have hh : ContMDiffAt I (sphereBundleModel n) ∞
      (fun y ↦ sphereFrameEquiv n M p (f y)) x := hb.prodMk hs
  have hc := (contMDiffAt_extChartAt (I := sphereBundleModel n)
    (x := sphereFrameEquiv n M p (f x))).comp x hh
  rw [contMDiffAt_iff_target]
  refine ⟨tendsto_subtype_rng.mpr hf.continuousAt, ?_⟩
  convert hc using 1
  funext y
  rfl

/-- The actual open complement of the zero set of a smooth tangent field. -/
def nonzeroFieldDomain (X : (x : M) → TangentSpace (model n) x)
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X)) : TopologicalSpace.Opens M :=
  ⟨{x | X x ≠ 0}, (isOpen_nonzeroTangentBundle n M).preimage hX.continuous⟩

/-- Radial normalization as a map from the actual open complement of zeros
into the actual unit tangent sphere. -/
def normalizedSphereSection (X : (x : M) → TangentSpace (model n) x)
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X)) :
    nonzeroFieldDomain n M X hX → UnitTangentSphere n M :=
  fun x ↦ UnitTangentSphere.ofNonzero n M x.1 (X x.1) x.2

@[simp] theorem proj_normalizedSphereSection (X : (x : M) → TangentSpace (model n) x)
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X))
    (x : nonzeroFieldDomain n M X hX) :
    UnitTangentSphere.proj n M (normalizedSphereSection n M X hX x) = x.1 := rfl

theorem contMDiff_normalizedSphereSection (X : (x : M) → TangentSpace (model n) x)
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X)) :
    ContMDiff (model n) (sphereBundleModel n) ∞ (normalizedSphereSection n M X hX) := by
  intro x
  apply contMDiffAt_to_unitTangentSphere_of_ambient n M
  have h := (contMDiffAt_normalizedVectorField n M (hX x.1) x.2).comp x
    (contMDiff_subtype_val (I := model n) (U := nonzeroFieldDomain n M X hX)).contMDiffAt
  exact h


end SphereMaps

/-- Pullback of the actual local Levi-Civita connection matrix. -/
def tangentConnectionForm (p : M) (a b : Fin (2*n)) :
    DifferentialForm.Form (model n).tangent (TangentBundle (model n) M) 1 :=
  DifferentialForm.pullback (I := (model n).tangent)
    (Bundle.TotalSpace.proj : TangentBundle (model n) M → M)
    (localConnectionOneForm n M p a b)

/-- Pullback of the actual local curvature matrix. -/
def tangentCurvatureForm (p : M) (a b : Fin (2*n)) :
    DifferentialForm.Form (model n).tangent (TangentBundle (model n) M) 2 :=
  DifferentialForm.pullback (I := (model n).tangent)
    (Bundle.TotalSpace.proj : TangentBundle (model n) M → M)
    (localOrthonormalCurvatureForm n M p a b)

/-- Actual differential of a normalized direction coordinate. -/
def tangentDirectionDifferential (p : M) (a : Fin (2*n)) :
    DifferentialForm.Form (model n).tangent (TangentBundle (model n) M) 1 :=
  fun v ↦ ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0:Fin 1)
    (mvfderiv (model n).tangent (normalizedDirectionCoordinate n M p a) v)

/-- Chern's covariant direction form `θ_i=du_i+Σ_j α_ij u_j`, with the
actual local connection, not a freely supplied matrix of forms. -/
def tangentDirectionForm (p : M) (a : Fin (2*n)) :
    DifferentialForm.Form (model n).tangent (TangentBundle (model n) M) 1 :=
  tangentDirectionDifferential n M p a +
    ∑ b, fun v ↦ normalizedDirectionCoordinate n M p b v • tangentConnectionForm n M p a b v

@[simp] theorem tangentDirectionForm_apply (p : M) (a : Fin (2*n))
    (v : TangentBundle (model n) M) (w : Fin 1 → TangentSpace (model n).tangent v) :
    tangentDirectionForm n M p a v w =
      mvfderiv (model n).tangent (normalizedDirectionCoordinate n M p a) v (w 0) +
        ∑ b, normalizedDirectionCoordinate n M p b v * tangentConnectionForm n M p a b v w := by
  simp [tangentDirectionForm, tangentDirectionDifferential,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, smul_eq_mul]

theorem tangentConnectionForm_skew (p : M) (a b : Fin (2*n))
    (v : TangentBundle (model n) M)
    (hv : v.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    tangentConnectionForm n M p a b v = -tangentConnectionForm n M p b a v := by
  ext w
  simp only [tangentConnectionForm, DifferentialForm.pullback_apply,
    ContinuousAlternatingMap.neg_apply]
  exact congrArg (fun α ↦ α (fun j ↦ mfderiv (model n).tangent (model n)
    (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) v (w j)))
    (localConnectionOneForm_skew n M p a b hv)

private theorem weighted_skew_sum_zero {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (A : ι → ι → ℝ) (hA : ∀ i j, A i j = -A j i) :
    ∑ i, ∑ j, u i * u j * A i j = 0 := by
  have hs : (∑ i, ∑ j, u i * u j * A i j) = -(∑ i, ∑ j, u i * u j * A i j) := by
    nth_rw 1 [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA j i]
    ring
  linarith

/-- The actual covariant direction is tangent to the unit sphere:
`Σ_i u_i θ_i=0`. This uses both differentiation of the actual unit-length
relation and metric compatibility of the actual Levi-Civita connection. -/
theorem tangentDirectionForm_orthogonal (p : M) (v : TangentBundle (model n) M)
    (hv : v.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (hv0 : v.2 ≠ 0) :
    (∑ i, normalizedDirectionCoordinate n M p i v • tangentDirectionForm n M p i v) = 0 := by
  ext w
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    tangentDirectionForm_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    zero_apply]
  rw [normalizedDirection_differential_orthogonal n M p v hv hv0 (w 0), zero_add]
  simp only [Finset.mul_sum, ← mul_assoc]
  apply weighted_skew_sum_zero
  intro i j
  exact congrArg (fun α ↦ α w) (tangentConnectionForm_skew n M p i j v hv)

end GaussBonnetChern

