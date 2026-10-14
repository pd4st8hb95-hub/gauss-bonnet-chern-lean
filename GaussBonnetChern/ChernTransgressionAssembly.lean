import GaussBonnetChern.ChernGlobalTransgression

/-! Passage from actual local tangent-frame transgression identities to
the selected global angular form. The local identity remains an explicit
input here, until discharged by the geometric recurrence theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle Filter
open scoped Manifold ContDiff Topology BigOperators
namespace GaussBonnetChern
open DifferentialForm

private theorem assemblyCast_congr_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
    {r t : ℕ} (h : r=t) (α β : Form 𝓘(ℝ,E) P r) (x : P)
    (hα : α x = β x) : degreeCastForm h α x = degreeCastForm h β x := by
  subst t
  exact hα

universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] [Fact (0<n)]

/-- Actual exterior derivative in top base degree, with its necessary
degree equality rather than an implicit change of the form's arity. -/
def sphereAngularDerivative (a : FiniteOrientedAtlas n M) :
    Form (sphereBundleModel n) (UnitTangentSphere n M) (2*n) :=
  degreeCastForm (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
    (exteriorDerivative (atlasSphereAngularForm n M a))

/-- Local naturality applies to a genuine frame expression at every
nonzero point over its smooth domain. -/
theorem exteriorDerivative_frameSphereAngularForm_at
    (b : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x))
    (s : TopologicalSpace.Opens M)
    (hb : ∀ i, ContMDiffOn (model n) (model n).tangent ∞ (T% (fun x ↦ b x i)) s)
    (v : UnitTangentSphere n M) (hv : UnitTangentSphere.proj n M v ∈ s) :
    exteriorDerivative (frameSphereAngularForm n M b) v =
      pullback (I := sphereBundleModel n)
        ((↑) : UnitTangentSphere n M → TangentBundle (model n) M)
        (exteriorDerivative (frameTangentAngularForm n M b)) v := by
  symm
  apply pullback_exteriorDerivative_at
  · have hinc := contMDiff_sphereInclusion n M
    rw [sphereBundleModel_eq_self] at hinc
    rw [chernTangentModel_eq_self n] at hinc
    exact hinc
  · exact contDiffAt_chartRepresentation_frameTangentAngularForm n M b s hb v.1 hv
      (UnitTangentSphere.vector_ne_zero n M v)

/-- A fixed valid positive chart expresses the actual Euler pullback. -/
theorem sphereEulerForm_eq_chart_pullback (a : FiniteOrientedAtlas n M)
    (i : Fin a.card) (v : UnitTangentSphere n M)
    (hi : UnitTangentSphere.proj n M v ∈ (a.chart i).source) :
    sphereEulerForm n M a Fact.out v =
      pullback (I := sphereBundleModel n) (UnitTangentSphere.proj n M)
        (fun x ↦ frameEulerForm n M x (chartOrthonormalBasis n M (a.chart i) x)) v := by
  ext w
  simp only [sphereEulerForm, pullback_apply]
  rw [atlasEulerForm_eq_chartFrame n M a Fact.out i hi]

/-- This is the assembly bridge, not an assertion that the local
transgression input has already been proved. It preserves the actual Euler
form and uses the exact fixed-chart germ selected at the base point. -/
theorem sphereAngularDerivative_eq_neg_euler_of_local_transgression
    (a : FiniteOrientedAtlas n M)
    (hlocal : ∀ (i : Fin a.card) (v : TangentBundle (model n) M),
      v.1 ∈ (a.chart i).source → v.2 ≠ 0 →
      degreeCastForm (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
        (exteriorDerivative
          (frameTangentAngularForm n M (chartOrthonormalBasis n M (a.chart i)))) v =
        -pullback (I := 𝓘(ℝ,Model n × Model n))
          (Bundle.TotalSpace.proj : TangentBundle (model n) M → M)
          (fun x ↦ frameEulerForm n M x (chartOrthonormalBasis n M (a.chart i) x)) v) :
    sphereAngularDerivative n M a = -sphereEulerForm n M a Fact.out := by
  funext v
  obtain ⟨i,hi⟩ := a.covers (UnitTangentSphere.proj n M v)
  let b := chartOrthonormalBasis n M (a.chart i)
  let α : Form (model n) M (2*n) := fun x ↦ frameEulerForm n M x (b x)
  let inc : UnitTangentSphere n M → TangentBundle (model n) M := (↑)
  let projection : TangentBundle (model n) M → M := Bundle.TotalSpace.proj
  have hinc : MDifferentiable (sphereBundleModel n) 𝓘(ℝ,Model n × Model n) inc := by
    simpa only [modelWithCornersSelf_prod] using
      (contMDiff_sphereInclusion n M).mdifferentiable (by simp)
  have hπ : MDifferentiable 𝓘(ℝ,Model n × Model n) (model n) projection := by
    simpa only [modelWithCornersSelf_prod] using
      (contMDiff_proj (F := Model n) (IB := model n) (n := ∞)
        (TangentSpace (model n) : M → Type _)).mdifferentiable (by simp)
  have hc := pullback_comp_at (I := sphereBundleModel n)
    (I' := 𝓘(ℝ,Model n × Model n)) inc projection α v (hinc v) (hπ (inc v))
  have hd := exteriorDerivative_frameSphereAngularForm_at n M b
    ⟨(a.chart i).source,(a.chart i).open_source⟩
    (contMDiffOn_chartOrthonormalBasis n M (a.chart i) (a.smooth i)) v hi
  have hglobal := exteriorDerivative_atlasSphereAngularForm_eq_chart n M a i v hi
  have hlocalpoint : exteriorDerivative (atlasSphereAngularForm n M a) v =
      pullback (I := sphereBundleModel n) inc
        (exteriorDerivative (frameTangentAngularForm n M b)) v := hglobal.trans hd
  have hcast := assemblyCast_congr_at
    (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
    (exteriorDerivative (atlasSphereAngularForm n M a))
    (pullback (I := sphereBundleModel n) inc
      (exteriorDerivative (frameTangentAngularForm n M b))) v hlocalpoint
  have hcomm := congrFun (Chern.angularPullback_degreeCast
    (E := SphereBundleModel n) (F := Model n × Model n) inc
    (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
    (exteriorDerivative (frameTangentAngularForm n M b))) v
  have hpoint : sphereAngularDerivative n M a v =
      pullback (I := sphereBundleModel n) inc
        (degreeCastForm (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
          (exteriorDerivative (frameTangentAngularForm n M b))) v :=
    hcast.trans hcomm.symm
  ext w
  rw [hpoint]
  simp only [pullback_apply]
  rw [hlocal i v.1 hi (UnitTangentSphere.vector_ne_zero n M v)]
  change -(pullback (I := sphereBundleModel n) inc
    (pullback (I := 𝓘(ℝ,Model n × Model n)) projection α) v w) = _
  rw [← hc]
  simp only [Pi.neg_apply, ContinuousAlternatingMap.neg_apply]
  rw [sphereEulerForm_eq_chart_pullback n M a i v hi]
  rfl

end GaussBonnetChern
