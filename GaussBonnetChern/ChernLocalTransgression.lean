import GaussBonnetChern.ScalarDifferential
import GaussBonnetChern.ChernSphereForms
import GaussBonnetChern.ChernFrameGeometry

/-! Actual sphere fibers and local transgression geometry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.DifferentialForm
open Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℝ,E) ∞ P]
  {k : ℕ}

/-- Equality on an actual neighborhood gives equality of chart expressions
on the corresponding coordinate neighborhood. -/
theorem chartRepresentation_eventuallyEq_of_eventuallyEq
    (α β : Form 𝓘(ℝ,E) P k) (e : OpenPartialHomeomorph P E) (x : P)
    (hx : x ∈ e.source) (h : ∀ᶠ y in 𝓝 x, α y = β y) :
    chartRepresentation e α =ᶠ[𝓝 (e x)] chartRepresentation e β := by
  have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    simpa only [e.left_inv hx] using (e.continuousAt_symm (e.map_source hx)).tendsto
  have hp := ht.eventually h
  filter_upwards [hp] with y hy
  simp only [chartRepresentation_eq, hy]

/-- Exterior differentiation is local even for the totalized derivative.
This supplies the chart-choice bridge for an already glued angular form. -/
theorem exteriorDerivative_eq_of_eventuallyEq
    (α β : Form 𝓘(ℝ,E) P k) (x : P) (h : ∀ᶠ y in 𝓝 x, α y = β y) :
    exteriorDerivative α x = exteriorDerivative β x := by
  have hc := chartRepresentation_eventuallyEq_of_eventuallyEq α β (chartAt E x) x
    (mem_chart_source E x) h
  unfold exteriorDerivative chartDerivative
  rw [hc.extDeriv_eq]

end GaussBonnetChern.DifferentialForm

namespace GaussBonnetChern
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] [Fact (0<n)]

/-- Actual inclusion of a metric unit sphere fiber using a specified
orthonormal basis, so its orientation can be supplied and audited explicitly. -/
def sphereFiberInclusion (x : M)
    (b : OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x)) :
    ModelUnitSphere n → UnitTangentSphere n M :=
  fun u ↦ ⟨⟨x, b.repr.symm u.1⟩, by
    simpa only [LinearIsometryEquiv.norm_map, mem_sphere_zero_iff_norm] using u.2⟩

@[simp] theorem proj_sphereFiberInclusion (x : M)
    (b : OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x)) (u : ModelUnitSphere n) :
    UnitTangentSphere.proj n M (sphereFiberInclusion n M x b u) = x := rfl

theorem contMDiff_sphereFiberInclusion (x : M)
    (b : OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x)) :
    ContMDiff (𝓡 (2*n-1)) (sphereBundleModel n) ∞ (sphereFiberInclusion n M x b) := by
  intro u
  apply contMDiffAt_to_unitTangentSphere_of_ambient n M
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const, ?_⟩
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let L := (e.continuousLinearMapAt ℝ x).comp b.repr.symm.toContinuousLinearMap
  have h : ContMDiffAt (𝓡 (2*n-1)) 𝓘(ℝ,Model n) ∞
      (fun v : ModelUnitSphere n ↦ L v.1) u :=
    (L.contMDiff (n := ∞)).contMDiffAt.comp u
      (contMDiff_coe_sphere (n := 2*n-1) (m := ∞) (E := Model n)).contMDiffAt
  convert h using 1
  funext v
  exact (e.continuousLinearMapAt_apply_of_mem ℝ hx _).symm

theorem normalizedDirectionCoordinate_fiber (p x : M)
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (i : Fin (2*n)) (u : ModelUnitSphere n) :
    normalizedDirectionCoordinate n M p i
      (sphereFiberInclusion n M x (localOrthonormalBasis n M p x) u).1 = u.1 i := by
  have hu : ‖u.1‖ = 1 := by simpa using u.2
  simp only [normalizedDirectionCoordinate, sphereFiberInclusion,
    LinearIsometryEquiv.norm_map, hu, inv_one, one_mul, localDirectionCoordinate]
  rw [← localOrthonormalBasis_apply n M p hx]
  simpa only [OrthonormalBasis.repr_apply_apply] using congrArg (fun v : Model n ↦ v i)
    ((localOrthonormalBasis n M p x).repr.apply_symm_apply u.1)

/-- Every actual positive-degree form pulled back from the base vanishes
on a genuine sphere fiber, since its base projection is constant. -/
theorem sphereFiber_pullback_horizontal (x : M)
    (b : OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x))
    (k : ℕ) (α : DifferentialForm.Form (model n) M (k+1)) :
    DifferentialForm.pullback (I := 𝓡 (2*n-1)) (sphereFiberInclusion n M x b)
      (DifferentialForm.pullback (I := sphereBundleModel n) (UnitTangentSphere.proj n M) α) = 0 := by
  rw [← DifferentialForm.pullback_comp (I := 𝓡 (2*n-1))
    (I' := sphereBundleModel n) (sphereFiberInclusion n M x b) (UnitTangentSphere.proj n M) α
    ((contMDiff_sphereFiberInclusion n M x b).mdifferentiable (by simp))
    ((contMDiff_unitTangentSphere_proj n M).mdifferentiable (by simp))]
  change DifferentialForm.pullback (I := 𝓡 (2*n-1)) (fun _ : ModelUnitSphere n ↦ x) α = 0
  exact DifferentialForm.pullback_const_succ x k α

/-- Actual connection matrix pulled back to the actual sphere bundle. -/
def sphereConnectionForm (p : M) (a b : Fin (2*n)) :
    DifferentialForm.Form (sphereBundleModel n) (UnitTangentSphere n M) 1 :=
  DifferentialForm.pullback (I := sphereBundleModel n) (UnitTangentSphere.proj n M)
    (localConnectionOneForm n M p a b)

/-- Actual curvature matrix pulled back to the actual sphere bundle. -/
def sphereCurvatureForm (p : M) (a b : Fin (2*n)) :
    DifferentialForm.Form (sphereBundleModel n) (UnitTangentSphere n M) 2 :=
  DifferentialForm.pullback (I := sphereBundleModel n) (UnitTangentSphere.proj n M)
    (localOrthonormalCurvatureForm n M p a b)

theorem sphereConnectionForm_fiber_zero (p x : M)
    (b : OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x)) (i j : Fin (2*n)) :
    DifferentialForm.pullback (I := 𝓡 (2*n-1)) (sphereFiberInclusion n M x b)
      (sphereConnectionForm n M p i j) = 0 :=
  sphereFiber_pullback_horizontal n M x b 0 _

theorem sphereCurvatureForm_fiber_zero (p x : M)
    (b : OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x)) (i j : Fin (2*n)) :
    DifferentialForm.pullback (I := 𝓡 (2*n-1)) (sphereFiberInclusion n M x b)
      (sphereCurvatureForm n M p i j) = 0 :=
  sphereFiber_pullback_horizontal n M x b 1 _

/-- Actual unit-direction coordinate restricted to the sphere bundle. -/
def sphereDirectionCoordinate (p : M) (i : Fin (2*n)) (v : UnitTangentSphere n M) : ℝ :=
  normalizedDirectionCoordinate n M p i v.1

/-- The actual covariant direction form on the sphere is the restriction
of the radially normalized form on the punctured tangent bundle. -/
def sphereDirectionForm (p : M) (i : Fin (2*n)) :
    DifferentialForm.Form (sphereBundleModel n) (UnitTangentSphere n M) 1 :=
  DifferentialForm.pullback (I := sphereBundleModel n)
    ((↑) : UnitTangentSphere n M → TangentBundle (model n) M) (tangentDirectionForm n M p i)

theorem sphereDirectionForm_orthogonal (p : M) (v : UnitTangentSphere n M)
    (hv : v.1.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    (∑ i, sphereDirectionCoordinate n M p i v • sphereDirectionForm n M p i v) = 0 := by
  ext w
  have h := tangentDirectionForm_orthogonal n M p v.1 hv (UnitTangentSphere.vector_ne_zero n M v)
  have heval := congrArg (fun α ↦ α (fun i ↦ mfderiv (sphereBundleModel n) (model n).tangent
    ((↑) : UnitTangentSphere n M → TangentBundle (model n) M) v (w i))) h
  simp only [sphereDirectionCoordinate, sphereDirectionForm, DifferentialForm.pullback_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply] at heval ⊢
  convert! heval using 1 <;> rfl

/-- On a genuine unit-sphere fiber the connection contribution vanishes,
and the covariant direction form is precisely the differential of the usual
sphere coordinate. This is a real pullback identity, not a formal restriction. -/
theorem sphereDirectionForm_fiber (p x : M)
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (i : Fin (2*n)) :
    DifferentialForm.pullback (I := 𝓡 (2*n-1))
      (sphereFiberInclusion n M x (localOrthonormalBasis n M p x)) (sphereDirectionForm n M p i) =
      DifferentialForm.scalarDifferential (E := EuclideanSpace ℝ (Fin (2*n-1)))
        (fun u : ModelUnitSphere n ↦ u.1 i) := by
  let b := localOrthonormalBasis n M p x
  let F : ModelUnitSphere n → TangentBundle (model n) M :=
    fun u ↦ (sphereFiberInclusion n M x b u).1
  have hF : ContMDiff (𝓡 (2*n-1)) (model n).tangent ∞ F :=
    (contMDiff_sphereInclusion n M).comp (contMDiff_sphereFiberInclusion n M x b)
  have hπ : MDifferentiable (model n).tangent (model n)
      (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) :=
    (contMDiff_proj (F := Model n) (IB := model n) (n := ∞)
      (TangentSpace (model n) : M → Type _)).mdifferentiable (by simp)
  have hcoord : (normalizedDirectionCoordinate n M p i) ∘ F =
      (fun u : ModelUnitSphere n ↦ u.1 i) := by
    funext u
    exact normalizedDirectionCoordinate_fiber n M p x hx i u
  funext u
  ext w
  let W := fun j ↦ mfderiv (𝓡 (2*n-1)) (model n).tangent F u (w j)
  have hunit : (F u).2 ≠ 0 := UnitTangentSphere.vector_ne_zero n M _
  have hU := (contMDiffAt_normalizedDirectionCoordinate n M p i (F u) hx hunit).mdifferentiableAt
    (by simp)
  have hdu : mvfderiv (𝓡 (2*n-1)) (fun z : ModelUnitSphere n ↦ z.1 i) u (w 0) =
      mvfderiv (model n).tangent (normalizedDirectionCoordinate n M p i) (F u) (W 0) := by
    rw [← hcoord]
    unfold mvfderiv
    rw [mfderiv_comp u hU ((hF u).mdifferentiableAt (by simp))]
    rfl
  have hbase (j : Fin 1) : mfderiv (model n).tangent (model n)
      (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) (F u) (W j) = 0 := by
    have hh := congrArg (fun L ↦ L (w j))
      (mfderiv_comp u (hπ (F u)) ((hF u).mdifferentiableAt (by simp)))
    change mfderiv (𝓡 (2*n-1)) (model n) (fun _ : ModelUnitSphere n ↦ x) u (w j) = _ at hh
    rw [mfderiv_const] at hh
    exact hh.symm
  have hcomp : mfderiv (𝓡 (2*n-1)) (model n).tangent F u =
      (mfderiv (sphereBundleModel n) (model n).tangent
        ((↑) : UnitTangentSphere n M → TangentBundle (model n) M)
        (sphereFiberInclusion n M x b u)).comp
      (mfderiv (𝓡 (2*n-1)) (sphereBundleModel n) (sphereFiberInclusion n M x b) u) :=
    mfderiv_comp u
      (((contMDiff_sphereInclusion n M) (sphereFiberInclusion n M x b u)).mdifferentiableAt (by simp))
      (((contMDiff_sphereFiberInclusion n M x b) u).mdifferentiableAt (by simp))
  simp only [DifferentialForm.pullback_apply, sphereDirectionForm,
    DifferentialForm.scalarDifferential_apply]
  change tangentDirectionForm n M p i (F u)
    (fun j ↦ mfderiv (sphereBundleModel n) (model n).tangent
      ((↑) : UnitTangentSphere n M → TangentBundle (model n) M)
      (sphereFiberInclusion n M x b u)
      (mfderiv (𝓡 (2*n-1)) (sphereBundleModel n) (sphereFiberInclusion n M x b) u (w j))) = _
  have hW : (fun j ↦ mfderiv (sphereBundleModel n) (model n).tangent
      ((↑) : UnitTangentSphere n M → TangentBundle (model n) M)
      (sphereFiberInclusion n M x b u)
      (mfderiv (𝓡 (2*n-1)) (sphereBundleModel n) (sphereFiberInclusion n M x b) u (w j))) = W := by
    funext j
    exact (congrArg (fun L ↦ L (w j)) hcomp).symm
  rw [hW, tangentDirectionForm_apply, hdu]
  have hs : (∑ j, normalizedDirectionCoordinate n M p j (F u) *
      tangentConnectionForm n M p i j (F u) W) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [tangentConnectionForm, DifferentialForm.pullback_apply, hbase]
    rw [(localConnectionOneForm n M p i j (F u).1).map_coord_zero 0 rfl, mul_zero]
  rw [hs, add_zero]

end GaussBonnetChern

namespace GaussBonnetChern
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] [Fact (0<n)]
variable (b : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x))

section PullbackDirection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℝ,E) ∞ P]

/-- Actual covariant direction under an arbitrary differentiable map into
the punctured tangent bundle. This is pointwise, so no smoothness at a zero
outside the relevant domain is imposed on the map. -/
theorem pullback_frameTangentDirectionForm_at (φ : P → TangentBundle (model n) M)
    (x : P) (hφ : MDifferentiableAt 𝓘(ℝ,E) (model n).tangent φ x)
    (hb : ∀ j, ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun y ↦ b y j)) (φ x).1) (hv : (φ x).2 ≠ 0) (i : Fin (2*n)) :
    DifferentialForm.pullback (I := 𝓘(ℝ,E)) φ (frameTangentDirectionForm n M b i) x =
      DifferentialForm.scalarDifferential ((frameDirectionCoordinate n M b i) ∘ φ) x +
        ∑ j, frameDirectionCoordinate n M b j (φ x) •
          DifferentialForm.pullback (I := 𝓘(ℝ,E))
            ((Bundle.TotalSpace.proj : TangentBundle (model n) M → M) ∘ φ)
            (smoothFrameConnectionOneForm n M b i j) x := by
  let projection : TangentBundle (model n) M → M := Bundle.TotalSpace.proj
  have hprojection : MDifferentiableAt (model n).tangent (model n) projection (φ x) :=
    (contMDiffAt_proj (F := Model n) (IB := model n) (n := ∞)
      (TangentSpace (model n) : M → Type _)).mdifferentiableAt (by simp)
  have hconn (j : Fin (2*n)) :
      DifferentialForm.pullback (I := 𝓘(ℝ,E)) (projection ∘ φ)
        (smoothFrameConnectionOneForm n M b i j) x =
      DifferentialForm.pullback (I := 𝓘(ℝ,E)) φ (frameTangentConnectionForm n M b i j) x :=
    DifferentialForm.pullback_comp_at (I := 𝓘(ℝ,E)) (I' := (model n).tangent)
      (I'' := model n) (k := 1) φ projection
      (smoothFrameConnectionOneForm n M b i j) x hφ hprojection
  change DifferentialForm.pullback (I := 𝓘(ℝ,E)) φ (frameTangentDirectionForm n M b i) x =
    DifferentialForm.scalarDifferential ((frameDirectionCoordinate n M b i) ∘ φ) x +
      ∑ j, frameDirectionCoordinate n M b j (φ x) •
        DifferentialForm.pullback (I := 𝓘(ℝ,E)) (projection ∘ φ)
          (smoothFrameConnectionOneForm n M b i j) x
  simp_rw [hconn]
  ext w
  have hdu : mvfderiv 𝓘(ℝ,E) ((frameDirectionCoordinate n M b i) ∘ φ) x (w 0) =
      mvfderiv (model n).tangent (frameDirectionCoordinate n M b i) (φ x)
        (mfderiv 𝓘(ℝ,E) (model n).tangent φ x (w 0)) := by
    unfold mvfderiv
    rw [mfderiv_comp x
      ((contMDiffAt_frameDirectionCoordinate n M b i (φ x) hb hv).mdifferentiableAt (by simp)) hφ]
    rfl
  simp only [DifferentialForm.pullback_apply, frameTangentDirectionForm_apply,
    DifferentialForm.scalarDifferential_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    hdu]

end PullbackDirection

/-- Actual normalized coordinates of any specified frame reduce to the
usual unit-sphere coordinates on the matching metric fiber. -/
theorem frameDirectionCoordinate_fiber (x : M) (i : Fin (2*n)) (u : ModelUnitSphere n) :
    frameDirectionCoordinate n M b i (sphereFiberInclusion n M x (b x) u).1 = u.1 i := by
  have hu : ‖u.1‖ = 1 := by simpa using u.2
  simp only [frameDirectionCoordinate, sphereFiberInclusion,
    LinearIsometryEquiv.norm_map, hu, inv_one, one_mul]
  rw [← OrthonormalBasis.repr_apply_apply]
  exact congrArg (fun z : Model n ↦ z i) ((b x).repr.apply_symm_apply u.1)

/-- The genuine covariant direction form restricted to its metric fiber
is the ordinary coordinate differential. The connection part vanishes
because the genuine base projection of the inclusion is constant. -/
theorem frameTangentDirectionForm_fiber (x : M)
    (hb : ∀ j, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ b y j)) x)
    (i : Fin (2*n)) :
    DifferentialForm.pullback (I := 𝓡 (2*n-1))
      (fun u : ModelUnitSphere n ↦ (sphereFiberInclusion n M x (b x) u).1)
      (frameTangentDirectionForm n M b i) =
      DifferentialForm.scalarDifferential (E := EuclideanSpace ℝ (Fin (2*n-1)))
        (fun u : ModelUnitSphere n ↦ u.1 i) := by
  let F : ModelUnitSphere n → TangentBundle (model n) M :=
    fun u ↦ (sphereFiberInclusion n M x (b x) u).1
  have hF : ContMDiff (𝓡 (2*n-1)) (model n).tangent ∞ F :=
    (contMDiff_sphereInclusion n M).comp (contMDiff_sphereFiberInclusion n M x (b x))
  have hπ : MDifferentiable (model n).tangent (model n)
      (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) :=
    (contMDiff_proj (F := Model n) (IB := model n) (n := ∞)
      (TangentSpace (model n) : M → Type _)).mdifferentiable (by simp)
  have hcoord : (frameDirectionCoordinate n M b i) ∘ F =
      (fun u : ModelUnitSphere n ↦ u.1 i) := by
    funext u
    exact frameDirectionCoordinate_fiber n M b x i u
  funext u
  ext w
  let W := fun j ↦ mfderiv (𝓡 (2*n-1)) (model n).tangent F u (w j)
  have hU := (contMDiffAt_frameDirectionCoordinate n M b i (F u) hb
    (UnitTangentSphere.vector_ne_zero n M _)).mdifferentiableAt (by simp)
  have hdu : mvfderiv (𝓡 (2*n-1)) (fun z : ModelUnitSphere n ↦ z.1 i) u (w 0) =
      mvfderiv (model n).tangent (frameDirectionCoordinate n M b i) (F u) (W 0) := by
    rw [← hcoord]
    unfold mvfderiv
    rw [mfderiv_comp u hU ((hF u).mdifferentiableAt (by simp))]
    rfl
  have hbase (j : Fin 1) : mfderiv (model n).tangent (model n)
      (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) (F u) (W j) = 0 := by
    have hh := congrArg (fun L ↦ L (w j))
      (mfderiv_comp u (hπ (F u)) ((hF u).mdifferentiableAt (by simp)))
    change mfderiv (𝓡 (2*n-1)) (model n) (fun _ : ModelUnitSphere n ↦ x) u (w j) = _ at hh
    rw [mfderiv_const] at hh
    exact hh.symm
  simp only [DifferentialForm.pullback_apply, DifferentialForm.scalarDifferential_apply]
  change frameTangentDirectionForm n M b i (F u) W = _
  rw [frameTangentDirectionForm_apply, hdu]
  have hs : (∑ j, frameDirectionCoordinate n M b j (F u) *
      frameTangentConnectionForm n M b i j (F u) W) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [frameTangentConnectionForm, DifferentialForm.pullback_apply, hbase]
    rw [(smoothFrameConnectionOneForm n M b i j (F u).1).map_coord_zero 0 rfl, mul_zero]
  rw [hs, add_zero]

/-- Actual curvature pulled back to a sphere fiber is zero; this is a
positive-degree horizontal form on a map with constant base projection. -/
theorem frameTangentCurvatureForm_fiber_zero (x : M) (i j : Fin (2*n)) :
    DifferentialForm.pullback (I := 𝓡 (2*n-1))
      (fun u : ModelUnitSphere n ↦ (sphereFiberInclusion n M x (b x) u).1)
      (frameTangentCurvatureForm n M b i j) = 0 := by
  let F : ModelUnitSphere n → TangentBundle (model n) M :=
    fun u ↦ (sphereFiberInclusion n M x (b x) u).1
  have hF : ContMDiff (𝓡 (2*n-1)) (model n).tangent ∞ F :=
    (contMDiff_sphereInclusion n M).comp (contMDiff_sphereFiberInclusion n M x (b x))
  have hprojection : MDifferentiable (model n).tangent (model n)
      (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) :=
    (contMDiff_proj (F := Model n) (IB := model n) (n := ∞)
      (TangentSpace (model n) : M → Type _)).mdifferentiable (by simp)
  change DifferentialForm.pullback (I := 𝓡 (2*n-1)) F
    (DifferentialForm.pullback (I := (model n).tangent)
      (Bundle.TotalSpace.proj : TangentBundle (model n) M → M)
      (smoothFrameCurvatureTwoForm n M b i j)) = 0
  rw [← DifferentialForm.pullback_comp (I := 𝓡 (2*n-1)) (I' := (model n).tangent)
    (I'' := model n) (k := 2)
    F (Bundle.TotalSpace.proj : TangentBundle (model n) M → M)
    (smoothFrameCurvatureTwoForm n M b i j) (hF.mdifferentiable (by simp)) hprojection]
  exact DifferentialForm.pullback_const_succ x 1 _

end GaussBonnetChern


