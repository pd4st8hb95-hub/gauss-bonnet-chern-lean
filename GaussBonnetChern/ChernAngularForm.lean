import GaussBonnetChern.ChernFrameGeometry
import GaussBonnetChern.PositiveOrthonormalFrames
import GaussBonnetChern.ChernFrameGauge

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle
open Filter
open scoped Manifold ContDiff Topology BigOperators
namespace GaussBonnetChern
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] [Fact (0<n)]

/-- The actual local angular form calculated in one of the atlas's
positive smooth orthonormal frames. Derivatives of the frame are taken
before selecting a chart at a particular point. -/
def chartSphereAngularForm (a : FiniteOrientedAtlas n M) (i : Fin a.card) :
    DifferentialForm.Form (sphereBundleModel n) (UnitTangentSphere n M) (2*n-1) :=
  frameSphereAngularForm n M (chartOrthonormalBasis n M (a.chart i))

/-- A chosen representative of the actual angular form. Independence of
this choice, smoothness, differential identity and fiber integral remain
separate theorems; none of those facts are inserted into this definition. -/
def atlasSphereAngularForm (a : FiniteOrientedAtlas n M) :
    DifferentialForm.Form (sphereBundleModel n) (UnitTangentSphere n M) (2*n-1) :=
  fun v ↦ chartSphereAngularForm n M a ((a.covers (UnitTangentSphere.proj n M v)).choose) v

/-- Curvature is pulled back from the actual oriented Euler form on the
base when comparing the transgression's derivative. -/
def sphereEulerForm (a : FiniteOrientedAtlas n M) (hn : 0<n) :
    DifferentialForm.Form (sphereBundleModel n) (UnitTangentSphere n M) (2*n) :=
  DifferentialForm.pullback (I := sphereBundleModel n) (UnitTangentSphere.proj n M)
    (atlasEulerForm n M a hn)

/-- Two actual chart angular forms agree on their genuine overlap, since
both frames are smooth and have the exact orientation fixed by the atlas. -/
theorem chartSphereAngularForm_eq_on_overlap (a : FiniteOrientedAtlas n M)
    (i j : Fin a.card) (v : UnitTangentSphere n M)
    (hi : UnitTangentSphere.proj n M v ∈ (a.chart i).source)
    (hj : UnitTangentSphere.proj n M v ∈ (a.chart j).source) :
    chartSphereAngularForm n M a j v = chartSphereAngularForm n M a i v := by
  apply frameSphereAngularForm_eq_of_orientation
  · intro k
    exact contMDiffAt_chartOrthonormalBasis n M (a.chart i) (a.smooth i) k hi
  · intro k
    exact contMDiffAt_chartOrthonormalBasis n M (a.chart j) (a.smooth j) k hj
  · change (chartOrthonormalBasis n M (a.chart i) (UnitTangentSphere.proj n M v)).toBasis.orientation =
      (chartOrthonormalBasis n M (a.chart j) (UnitTangentSphere.proj n M v)).toBasis.orientation
    rw [chartOrthonormalBasis_orientation n M a i hi,
      chartOrthonormalBasis_orientation n M a j hj]

/-- The selected global representative equals every valid local chart
representative. Selection happens after all frame derivatives are formed. -/
theorem atlasSphereAngularForm_eq_chart (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (v : UnitTangentSphere n M)
    (hi : UnitTangentSphere.proj n M v ∈ (a.chart i).source) :
    atlasSphereAngularForm n M a v = chartSphereAngularForm n M a i v := by
  exact chartSphereAngularForm_eq_on_overlap n M a i
    ((a.covers (UnitTangentSphere.proj n M v)).choose) v hi
    (a.covers (UnitTangentSphere.proj n M v)).choose_spec

/-- Gluing gives local equality with one fixed smooth chart expression on
an actual neighborhood; no derivative of a pointwise atlas choice is used. -/
theorem atlasSphereAngularForm_eventuallyEq_chart (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (v : UnitTangentSphere n M)
    (hi : UnitTangentSphere.proj n M v ∈ (a.chart i).source) :
    ∀ᶠ w in 𝓝 v, atlasSphereAngularForm n M a w = chartSphereAngularForm n M a i w := by
  have hs : IsOpen ((UnitTangentSphere.proj n M) ⁻¹' (a.chart i).source) :=
    (a.chart i).open_source.preimage (UnitTangentSphere.continuous_proj n M)
  filter_upwards [hs.mem_nhds hi] with w hw
  exact atlasSphereAngularForm_eq_chart n M a i w hw

theorem atlasSphereAngularForm_independent_of_chart_choice (a : FiniteOrientedAtlas n M)
    (chooseChart : UnitTangentSphere n M → Fin a.card)
    (hchoose : ∀ v, UnitTangentSphere.proj n M v ∈ (a.chart (chooseChart v)).source) :
    atlasSphereAngularForm n M a = fun v ↦ chartSphereAngularForm n M a (chooseChart v) v := by
  funext v
  exact atlasSphereAngularForm_eq_chart n M a (chooseChart v) v (hchoose v)

end GaussBonnetChern
