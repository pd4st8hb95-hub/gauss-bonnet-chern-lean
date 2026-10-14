import GaussBonnetChern.ChernAngularForm
import GaussBonnetChern.ChernLocalTransgression
import GaussBonnetChern.ChernGlobalTransgression
import GaussBonnetChern.AngularVerticalDeterminant
import GaussBonnetChern.SphereChartIntegralAtlas

/-! The actual Chern angular form has oriented integral one on every
metric sphere fiber. Its restriction and its form integral are proved separately. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle Module Metric MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern
open DifferentialForm
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] [Fact (0<n)]

/-- The outward normal-first orientation of the standard sphere used to
parameterize a positively framed metric sphere fiber. -/
def chernFiberModelBasis : OrthonormalBasis (Fin ((2*n-1)+1)) ℝ (Model n) :=
  (EuclideanSpace.basisFun (Fin (2*n)) ℝ).reindex
    (AngularVertical.evenSuccEquiv n Fact.out).symm

private theorem chernFiberIntegral_const_smul (c : ℝ)
    (α : Form (𝓡 (2*n-1)) (ModelUnitSphere n) (2*n-1)) :
    sphereFormIntegral (chernFiberModelBasis n) (c • α) =
      c * sphereFormIntegral (chernFiberModelBasis n) α := by
  unfold sphereFormIntegral
  have hc (u : ModelUnitSphere n) :
      sphereFormCoefficient (chernFiberModelBasis n) (c • α) u =
      c * sphereFormCoefficient (chernFiberModelBasis n) α u :=
    sphereFormCoefficient_fsmul (chernFiberModelBasis n) (fun _ ↦ c) α u
  simp_rw [hc]
  exact integral_const_mul c _

/-- The actual generic-frame angular form pulls back to the ordinary
sphere-coordinate polynomial; all actual curvature terms vanish there. -/
theorem frameSphereAngularForm_fiber_polynomial
    (b : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x)) (x : M)
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ b y i)) x) :
    pullback (I := 𝓡 (2*n-1)) (sphereFiberInclusion n M x (b x))
      (frameSphereAngularForm n M b) =
      Chern.angularForm n (fun i (u : ModelUnitSphere n) ↦ u.1 i)
        (fun i ↦ scalarDifferential (fun u : ModelUnitSphere n ↦ u.1 i))
        (fun _ _ ↦ 0) := by
  let F : ModelUnitSphere n → TangentBundle (model n) M :=
    fun u ↦ (sphereFiberInclusion n M x (b x) u).1
  have hinc : ContMDiff (sphereBundleModel n) 𝓘(ℝ,Model n × Model n) ∞
      ((↑) : UnitTangentSphere n M → TangentBundle (model n) M) := by
    simpa only [modelWithCornersSelf_prod] using contMDiff_sphereInclusion n M
  have hθ (i : Fin (2*n)) :
      pullback (I := 𝓡 (2*n-1)) F (frameTangentDirectionForm n M b i) =
        scalarDifferential (fun u : ModelUnitSphere n ↦ u.1 i) :=
    frameTangentDirectionForm_fiber n M b x hb i
  have hB (i j : Fin (2*n)) :
      pullback (I := 𝓡 (2*n-1)) F (frameTangentCurvatureForm n M b i j) = 0 :=
    frameTangentCurvatureForm_fiber_zero n M b x i j
  have hu (i : Fin (2*n)) : frameDirectionCoordinate n M b i ∘ F =
      (fun u : ModelUnitSphere n ↦ u.1 i) := by
    funext u
    exact frameDirectionCoordinate_fiber n M b x i u
  rw [frameSphereAngularForm, ← pullback_comp (I := 𝓡 (2*n-1))
    (I' := sphereBundleModel n) (sphereFiberInclusion n M x (b x))
    ((↑) : UnitTangentSphere n M → TangentBundle (model n) M)
    (frameTangentAngularForm n M b)
    ((contMDiff_sphereFiberInclusion n M x (b x)).mdifferentiable (by simp))
    (hinc.mdifferentiable (by simp))]
  change pullback (I := 𝓡 (2*n-1)) F (frameTangentAngularForm n M b) = _
  let θ : Fin (2*n) → Form 𝓘(ℝ,Model n × Model n) (TangentBundle (model n) M) 1 :=
    fun i v ↦ frameTangentDirectionForm n M b i v
  let Ω : Fin (2*n) → Fin (2*n) →
      Form 𝓘(ℝ,Model n × Model n) (TangentBundle (model n) M) 2 :=
    fun i j v ↦ frameTangentCurvatureForm n M b i j v
  have hθ' (i : Fin (2*n)) : pullback (I := 𝓡 (2*n-1)) F (θ i) =
      scalarDifferential (fun u : ModelUnitSphere n ↦ u.1 i) := by
    calc
      _ = pullback (I := 𝓡 (2*n-1)) (I' := (model n).tangent) F
          (frameTangentDirectionForm n M b i) := by
        funext u
        ext w
        simp only [pullback_apply, θ]
        rw [← chernTangentModel_eq_self n]
      _ = _ := hθ i
  have hΩ' (i j : Fin (2*n)) : pullback (I := 𝓡 (2*n-1)) F (Ω i j) = 0 := by
    calc
      _ = pullback (I := 𝓡 (2*n-1)) (I' := (model n).tangent) F
          (frameTangentCurvatureForm n M b i j) := by
        funext u
        ext w
        simp only [pullback_apply, Ω]
        rw [← chernTangentModel_eq_self n]
      _ = _ := hB i j
  have hangular : frameTangentAngularForm n M b =
      Chern.angularForm n (frameDirectionCoordinate n M b) θ Ω := rfl
  rw [hangular, Chern.pullback_angularForm]
  rw [show (fun i ↦ frameDirectionCoordinate n M b i ∘ F) =
    (fun i (u : ModelUnitSphere n) ↦ u.1 i) from funext hu]
  exact congrArg₂ (fun θ' Ω' ↦
      Chern.angularForm n (fun i (u : ModelUnitSphere n) ↦ u.1 i) θ' Ω')
    (funext hθ') (funext fun i ↦ funext fun j ↦ hΩ' i j)

/-- This is an equality of actual forms, including the full alternation
factorial, rather than just a normalization against the sphere measure. -/
theorem frameSphereAngularForm_fiber_volume
    (b : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x)) (x : M)
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ b y i)) x) :
    pullback (I := 𝓡 (2*n-1)) (sphereFiberInclusion n M x (b x))
      (frameSphereAngularForm n M b) =
      (Chern.angularCoefficient n 0 * ((2*n-1).factorial : ℝ)) •
        sphereVolumeForm (chernFiberModelBasis n) := by
  rw [frameSphereAngularForm_fiber_polynomial n M b x hb,
    Chern.angularForm_zero_curvature n Fact.out]
  have h₀ := AngularVertical.sphere_angularTerm_zero_eq_factorial_volume n Fact.out
    (EuclideanSpace.basisFun (Fin (2*n)) ℝ)
  simp only [EuclideanSpace.basisFun_inner] at h₀
  rw [h₀, smul_smul]
  rfl

/-- Gluing restricts to any actual positive chart frame over the fixed
base point, independently of which chart the global definition selects. -/
theorem atlasSphereAngularForm_fiber_volume (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (x : M) (hx : x ∈ (a.chart i).source) :
    pullback (I := 𝓡 (2*n-1))
      (sphereFiberInclusion n M x (chartOrthonormalBasis n M (a.chart i) x))
      (atlasSphereAngularForm n M a) =
      (Chern.angularCoefficient n 0 * ((2*n-1).factorial : ℝ)) •
        sphereVolumeForm (chernFiberModelBasis n) := by
  have hform : pullback (I := 𝓡 (2*n-1))
      (sphereFiberInclusion n M x (chartOrthonormalBasis n M (a.chart i) x))
      (atlasSphereAngularForm n M a) =
    pullback (I := 𝓡 (2*n-1))
      (sphereFiberInclusion n M x (chartOrthonormalBasis n M (a.chart i) x))
      (frameSphereAngularForm n M (chartOrthonormalBasis n M (a.chart i))) := by
    funext u
    unfold pullback
    rw [atlasSphereAngularForm_eq_chart n M a i
      (sphereFiberInclusion n M x (chartOrthonormalBasis n M (a.chart i) x) u)
      (by change x ∈ (a.chart i).source; exact hx)]
    rfl
  rw [hform]
  exact frameSphereAngularForm_fiber_volume n M _ x
    (fun j ↦ contMDiffAt_chartOrthonormalBasis n M (a.chart i) (a.smooth i) j hx)

theorem isSmooth_atlasSphereAngularForm_fiber (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (x : M) (hx : x ∈ (a.chart i).source) :
    IsSmooth (pullback (I := 𝓡 (2*n-1))
      (sphereFiberInclusion n M x (chartOrthonormalBasis n M (a.chart i) x))
      (atlasSphereAngularForm n M a)) := by
  rw [atlasSphereAngularForm_fiber_volume n M a i x hx]
  exact (isSmooth_sphereVolumeForm _).const_smul _

/-- The genuine intrinsic oriented form integral on the metric fiber is
one, computed from its actual pullback and the proved volume-form integral. -/
theorem atlasSphereAngularForm_fiber_integral (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (x : M) (hx : x ∈ (a.chart i).source) :
    sphereFormIntegral (chernFiberModelBasis n)
      (pullback (I := 𝓡 (2*n-1))
        (sphereFiberInclusion n M x (chartOrthonormalBasis n M (a.chart i) x))
        (atlasSphereAngularForm n M a)) = 1 := by
  rw [atlasSphereAngularForm_fiber_volume n M a i x hx,
    chernFiberIntegral_const_smul, sphereFormIntegral_volume]
  exact Chern.angularCoefficient_mul_sphereMeasure n Fact.out

/-- The same normalization holds for the actual finite-chart oriented
form integral, with every subordinate smooth partition of unity. -/
theorem atlasSphereAngularForm_fiber_chart_integral (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (x : M) (hx : x ∈ (a.chart i).source)
    (c : FiniteSphereOrientedAtlas (chernFiberModelBasis n))
    (ρ : SmoothPartitionOfUnity (Fin c.card) (𝓡 (2*n-1)) (ModelUnitSphere n) Set.univ)
    (hρ : ρ.IsSubordinate (fun j ↦ (c.chart j).source)) :
    GenericFormIntegration.integral c.chart (fun j ↦ ρ j)
      (pullback (I := 𝓡 (2*n-1))
        (sphereFiberInclusion n M x (chartOrthonormalBasis n M (a.chart i) x))
        (atlasSphereAngularForm n M a)) = 1 := by
  rw [c.integral_eq_sphereFormIntegral (chernFiberModelBasis n) ρ hρ _
    (isSmooth_atlasSphereAngularForm_fiber n M a i x hx)]
  exact atlasSphereAngularForm_fiber_integral n M a i x hx

end GaussBonnetChern
