import GaussBonnetChern.ChernAngularForm
import GaussBonnetChern.ChernLocalTransgression
import GaussBonnetChern.ChernPatchGeometry
import GaussBonnetChern.ChernProductIdentities
import GaussBonnetChern.AngularPolynomialLimit

/-! Locality and regularity of the genuinely glued Chern angular form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle Filter
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℝ,E) ∞ P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace F Q] [IsManifold 𝓘(ℝ,F) ∞ Q]
  {k : ℕ}

/-- Pullback at a point depends only on the germ of the map there. -/
theorem pullback_eq_of_eventuallyEq_at (f g : P → Q) (α : Form 𝓘(ℝ,F) Q k)
    (x : P) (h : f =ᶠ[𝓝 x] g) :
    pullback (I := 𝓘(ℝ,E)) f α x = pullback (I := 𝓘(ℝ,E)) g α x := by
  ext v
  simp only [pullback_apply]
  rw [h.eq_of_nhds]
  congr 1
  funext j
  have hd := congrArg (fun L ↦ L (v j)) (h.mfderiv_eq (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,F)))
  exact hd

/-- The coordinate form on an open submanifold agrees locally with the
ambient coordinate form. This proves regularity from an actual restriction,
without assigning smoothness to an arbitrary extension. -/
theorem chartRepresentation_restrict_eventuallyEq (U : TopologicalSpace.Opens Q)
    (α : Form 𝓘(ℝ,F) Q k) (x : U) :
    chartRepresentation (chartAt F x.1) α =ᶠ[𝓝 (chartAt F x.1 x.1)]
      chartRepresentation (chartAt F x)
        (pullback (I := 𝓘(ℝ,F)) ((↑) : U → Q) α) := by
  let e := chartAt F x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ,F) ∞ U :=
    IsManifold.chart_mem_maximalAtlas x
  have hy : chartAt F x.1 x.1 ∈ e.target := e.map_source (mem_chart_source F x)
  have hg := U.chartAt_subtype_val_symm_eventuallyEq (H := F) (x := x)
  filter_upwards [hg.eventuallyEq_nhds, e.open_target.mem_nhds hy] with y hgy hye
  have hpb := pullback_eq_of_eventuallyEq_at (E := F)
    (chartAt F x.1).symm (((↑) : U → Q) ∘ e.symm) α y hgy
  have hcomp := pullback_comp_at (I := 𝓘(ℝ,F)) (I' := 𝓘(ℝ,F))
    e.symm ((↑) : U → Q) α y
    ((contMDiffAt_symm_of_mem_maximalAtlas he hye).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := 𝓘(ℝ,F)) (n := ∞) (U := U)).mdifferentiable (by simp) _)
  unfold chartRepresentation
  rw [hpb, hcomp]

theorem contDiffAt_chartRepresentation_of_smooth_restriction
    (U : TopologicalSpace.Opens Q) (α : Form 𝓘(ℝ,F) Q k)
    (hα : IsSmooth (pullback (I := 𝓘(ℝ,F)) ((↑) : U → Q) α))
    (x : Q) (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (chartRepresentation (chartAt F x) α) (chartAt F x x) := by
  let z : U := ⟨x,hx⟩
  have hs := (hα (chartAt F z) (IsManifold.chart_mem_maximalAtlas z)).contDiffAt
    ((chartAt F z).open_target.mem_nhds ((chartAt F z).map_source (mem_chart_source F z)))
  exact hs.congr_of_eventuallyEq (chartRepresentation_restrict_eventuallyEq U α z)

/-- Smoothness of a pullback in the centered source chart only requires
smoothness of the target form at the actual image point. -/
theorem contDiffAt_chartRepresentation_pullback_at (f : P → Q)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (α : Form 𝓘(ℝ,F) Q k) (x : P)
    (hα : ContDiffAt ℝ ∞ (chartRepresentation (chartAt F (f x)) α)
      (chartAt F (f x) (f x))) :
    ContDiffAt ℝ ∞ (chartRepresentation (chartAt E x) (pullback (I := 𝓘(ℝ,E)) f α))
      (chartAt E x x) := by
  let e := chartAt E x
  let e' := chartAt F (f x)
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ P := IsManifold.chart_mem_maximalAtlas x
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ,F) ∞ Q := IsManifold.chart_mem_maximalAtlas (f x)
  have hx : x ∈ e.source := mem_chart_source E x
  have hfx : f (e.symm (e x)) ∈ e'.source := by
    simpa only [e.left_inv hx] using mem_chart_source F (f x)
  have hc := coordinateMap_contDiffAt e e' he he' f hf (e x) (e.map_source hx) hfx
  have ha : ContDiffAt ℝ ∞ (chartRepresentation e' α) (coordinateMap e e' f (e x)) := by
    simpa only [coordinateMap, Function.comp_apply, e.left_inv hx] using hα
  have hpoly := contDiffAt_compContinuousLinearMap (ha.comp (e x) hc)
    (hc.fderiv_right (m := ∞) (by simp))
  exact hpoly.congr_of_eventuallyEq
    (chartRepresentation_pullback_eventuallyEq e e' he he' f hf α (e x) (e.map_source hx) hfx)

end GaussBonnetChern.DifferentialForm

namespace GaussBonnetChern.Chern
open DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℝ,E) ∞ P]

theorem isSmooth_angularForm (n : ℕ)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (hu : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (u i))
    (hθ : ∀ i, IsSmooth (θ i)) (hB : ∀ i j, IsSmooth (B i j)) :
    IsSmooth (angularForm n u θ B) := by
  unfold angularForm
  apply IsSmooth.sum
  intro k _
  apply IsSmooth.const_smul
  unfold angularTerm
  apply IsSmooth.sum
  intro σ _
  apply IsSmooth.const_smul
  apply IsSmooth.functionSmul (hu _)
  apply IsSmooth.degreeCast
  exact (isSmooth_oneFormProduct _ _ (fun _ ↦ hθ _)).wedge
    (isSmooth_twoFormProduct _ _ (fun _ ↦ hB _ _))
end GaussBonnetChern.Chern

namespace GaussBonnetChern
open DifferentialForm
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]
variable (b : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x))
  (s : TopologicalSpace.Opens M)

theorem chernTangentModel_eq_self : (model n).tangent = 𝓘(ℝ,Model n × Model n) := by
  change (𝓘(ℝ,Model n)).prod (𝓘(ℝ,Model n)) = 𝓘(ℝ,Model n × Model n)
  exact modelWithCornersSelf_prod.symm

/-- The actual angular polynomial on the actual open nonzero tangent patch. -/
def framePatchAngularForm :
    Form 𝓘(ℝ,Model n × Model n) (frameNonzeroDomain n M s) (2*n-1) :=
  Chern.angularForm n (framePatchDirectionCoordinate n M b s)
    (framePatchDirectionForm n M b s) (framePatchCurvatureForm n M b s)

variable (hb : ∀ i, ContMDiffOn (model n) (model n).tangent ∞
  (T% (fun x ↦ b x i)) s)

include hb in
theorem isSmooth_framePatchAngularForm : IsSmooth (framePatchAngularForm n M b s) := by
  apply Chern.isSmooth_angularForm
  · intro i
    simpa only [modelWithCornersSelf_prod] using
      contMDiff_framePatchDirectionCoordinate n M b s hb i
  · exact isSmooth_framePatchDirectionForm n M b s hb
  · exact isSmooth_framePatchCurvatureForm n M b s hb

include hb in
theorem framePatchAngularForm_eq_restrict :
    framePatchAngularForm n M b s =
      pullback (I := 𝓘(ℝ,Model n × Model n))
        ((↑) : frameNonzeroDomain n M s → TangentBundle (model n) M)
        (frameTangentAngularForm n M b) := by
  let inc : frameNonzeroDomain n M s → TangentBundle (model n) M := (↑)
  have hinc : MDifferentiable 𝓘(ℝ,Model n × Model n) (model n).tangent inc := by
    simpa only [modelWithCornersSelf_prod] using
      (contMDiff_subtype_val (I := 𝓘(ℝ,Model n × Model n)) (n := ∞)
        (U := frameNonzeroDomain n M s)).mdifferentiable (by simp)
  have hπ := (contMDiff_proj (F := Model n) (IB := model n) (n := ∞)
    (TangentSpace (model n) : M → Type _)).mdifferentiable (by simp)
  have hB (i j : Fin (2*n)) : framePatchCurvatureForm n M b s i j =
      pullback (I := 𝓘(ℝ,Model n × Model n)) inc (frameTangentCurvatureForm n M b i j) :=
    pullback_comp inc (Bundle.TotalSpace.proj : TangentBundle (model n) M → M)
      (smoothFrameCurvatureTwoForm n M b i j) hinc hπ
  let θ : Fin (2*n) → Form 𝓘(ℝ,Model n × Model n) (TangentBundle (model n) M) 1 :=
    fun i v ↦ frameTangentDirectionForm n M b i v
  let Ω : Fin (2*n) → Fin (2*n) →
      Form 𝓘(ℝ,Model n × Model n) (TangentBundle (model n) M) 2 :=
    fun i j v ↦ frameTangentCurvatureForm n M b i j v
  have hθ (i : Fin (2*n)) : framePatchDirectionForm n M b s i =
      pullback (I := 𝓘(ℝ,Model n × Model n)) inc (θ i) := by
    rw [framePatchDirectionForm_eq_restrict n M b s hb i]
    funext v
    ext w
    simp only [pullback_apply, θ]
    rw [← chernTangentModel_eq_self n]
  have hΩ (i j : Fin (2*n)) : framePatchCurvatureForm n M b s i j =
      pullback (I := 𝓘(ℝ,Model n × Model n)) inc (Ω i j) := by
    rw [hB i j]
    funext v
    ext w
    simp only [pullback_apply, Ω]
    rw [← chernTangentModel_eq_self n]
  have hangular : frameTangentAngularForm n M b =
      Chern.angularForm n (frameDirectionCoordinate n M b) θ Ω := by
    rfl
  rw [hangular, Chern.pullback_angularForm]
  change Chern.angularForm n (framePatchDirectionCoordinate n M b s)
      (framePatchDirectionForm n M b s) (framePatchCurvatureForm n M b s) =
    Chern.angularForm n (framePatchDirectionCoordinate n M b s)
      (fun i ↦ pullback (I := 𝓘(ℝ,Model n × Model n)) inc (θ i))
      (fun i j ↦ pullback (I := 𝓘(ℝ,Model n × Model n)) inc (Ω i j))
  exact congrArg₂
    (fun θ' Ω' ↦ Chern.angularForm n (framePatchDirectionCoordinate n M b s) θ' Ω')
    (funext hθ) (funext fun i ↦ funext fun j ↦ hΩ i j)

include hb in
theorem contDiffAt_chartRepresentation_frameTangentAngularForm
    (v : TangentBundle (model n) M) (hvs : v.1 ∈ s) (hv0 : v.2 ≠ 0) :
    ContDiffAt ℝ ∞
      (chartRepresentation (chartAt (Model n × Model n) v) (frameTangentAngularForm n M b))
      (chartAt (Model n × Model n) v v) := by
  apply contDiffAt_chartRepresentation_of_smooth_restriction (frameNonzeroDomain n M s)
  · rw [← framePatchAngularForm_eq_restrict n M b s hb]
    exact isSmooth_framePatchAngularForm n M b s hb
  · exact ⟨hvs,hv0⟩

section Sphere
variable [Fact (0<n)]

include hb in
theorem contDiffAt_chartRepresentation_frameSphereAngularForm
    (v : UnitTangentSphere n M) (hv : UnitTangentSphere.proj n M v ∈ s) :
    ContDiffAt ℝ ∞
      (chartRepresentation (chartAt (SphereBundleChartModel n) v) (frameSphereAngularForm n M b))
      (chartAt (SphereBundleChartModel n) v v) := by
  apply contDiffAt_chartRepresentation_pullback_at
    ((↑) : UnitTangentSphere n M → TangentBundle (model n) M)
  · have hinc := contMDiff_sphereInclusion n M
    rw [sphereBundleModel_eq_self] at hinc
    rw [chernTangentModel_eq_self n] at hinc
    exact hinc
  · exact contDiffAt_chartRepresentation_frameTangentAngularForm n M b s hb v.1 hv
      (UnitTangentSphere.vector_ne_zero n M v)

/-- Global smoothness is obtained from one fixed valid chart in each germ,
using the already proved overlap equality of actual angular forms. -/
theorem isSmooth_atlasSphereAngularForm (a : FiniteOrientedAtlas n M) :
    IsSmooth (atlasSphereAngularForm n M a) := by
  apply isSmooth_of_centeredChartSmoothAt
  intro v
  obtain ⟨i,hi⟩ := a.covers (UnitTangentSphere.proj n M v)
  have hs := contDiffAt_chartRepresentation_frameSphereAngularForm n M
    (chartOrthonormalBasis n M (a.chart i)) ⟨(a.chart i).source,(a.chart i).open_source⟩
    (contMDiffOn_chartOrthonormalBasis n M (a.chart i) (a.smooth i)) v hi
  apply hs.congr_of_eventuallyEq
  exact chartRepresentation_eventuallyEq_of_eventuallyEq
    (atlasSphereAngularForm n M a) (chartSphereAngularForm n M a i)
    (chartAt (SphereBundleChartModel n) v) v (mem_chart_source (SphereBundleChartModel n) v)
    (atlasSphereAngularForm_eventuallyEq_chart n M a i v hi)

/-- Exterior differentiation of the selected representative uses a fixed
valid chart expression on a neighborhood. -/
theorem exteriorDerivative_atlasSphereAngularForm_eq_chart (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (v : UnitTangentSphere n M)
    (hi : UnitTangentSphere.proj n M v ∈ (a.chart i).source) :
    exteriorDerivative (atlasSphereAngularForm n M a) v =
      exteriorDerivative (chartSphereAngularForm n M a i) v :=
  exteriorDerivative_eq_of_eventuallyEq _ _ v
    (atlasSphereAngularForm_eventuallyEq_chart n M a i v hi)

end Sphere
end GaussBonnetChern
