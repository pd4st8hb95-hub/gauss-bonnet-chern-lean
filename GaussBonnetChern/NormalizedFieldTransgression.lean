import GaussBonnetChern.ChernGeometricTransgression
import GaussBonnetChern.ChernOpenRestriction
import GaussBonnetChern.StokesLocalization

/-! # The actual normalized-field transgression on the complement of its zeros

The ambient form is totalized by zero at field zeros. A local retraction into
the actual open nonzero locus transports the genuine normalized-section
pullback. Its restriction is proved equal to that pullback, so totalization
introduces neither a global-frame assumption nor a nonempty-space assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] {k : ℕ}

/-- A point supplies its own fallback for a total local retraction. -/
def openRetraction (U : TopologicalSpace.Opens M) (z : U) : M → U := by
  classical
  exact fun x ↦ if hx : x ∈ U then ⟨x,hx⟩ else z

theorem contMDiffAt_openRetraction (U : TopologicalSpace.Opens M)
    (z : U) (x : M) (hx : x ∈ U) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (openRetraction U z) x := by
  classical
  apply (ContMDiffAt.subtypeVal_comp_iff U (openRetraction U z) x).mp
  apply contMDiffAt_id.congr_of_eventuallyEq
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  change y ∈ U at hy
  have hgy : openRetraction U z y = ⟨y,hy⟩ := by
    change (if hy : y ∈ U then ⟨y,hy⟩ else z) = ⟨y,hy⟩
    rw [dif_pos hy]
  exact congrArg Subtype.val hgy

/-- Extension of a form on an open submanifold using actual derivative
pullbacks. The branch outside the open locus is zero. -/
def extendOpenForm (U : TopologicalSpace.Opens M) (α : Form 𝓘(ℝ,E) U k) :
    Form 𝓘(ℝ,E) M k := by
  classical
  exact fun x ↦ if hx : x ∈ U then
    pullback (I := 𝓘(ℝ,E)) (openRetraction U ⟨x,hx⟩) α x else 0

/-- The actual restriction of the totalized form is exactly the original
form; the chain rule proves the inclusion and retraction derivatives cancel. -/
theorem pullback_extendOpenForm (U : TopologicalSpace.Opens M)
    (α : Form 𝓘(ℝ,E) U k) :
    pullback (I := 𝓘(ℝ,E)) ((↑) : U → M) (extendOpenForm U α) = α := by
  classical
  funext z
  let inc : U → M := (↑)
  let g := openRetraction U z
  have hg : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) g z.val :=
    (contMDiffAt_openRetraction (E := E) (M := M) U z z.val z.property).mdifferentiableAt (by simp)
  have hi := (contMDiff_subtype_val (I := 𝓘(ℝ,E)) (n := ∞) (U := U)).mdifferentiable (by simp) z
  have hcomp : g ∘ inc = id := by
    funext y
    change openRetraction U z y.val = y
    change (if hy : y.val ∈ U then ⟨y.val,hy⟩ else z) = y
    rw [dif_pos y.property]
  have hchain := mfderiv_comp z hg hi
  rw [hcomp, mfderiv_id] at hchain
  have hgval : g z.val = z := by
    change (if hz : z.val ∈ U then ⟨z.val,hz⟩ else z) = z
    rw [dif_pos z.property]
  have hext : extendOpenForm U α z.val = pullback (I := 𝓘(ℝ,E)) g α z.val := by
    change (if hz : z.val ∈ U then
      pullback (I := 𝓘(ℝ,E)) (openRetraction U ⟨z.val,hz⟩) α z.val else 0) = _
    rw [dif_pos z.property]
  ext v
  change extendOpenForm U α z.val
    (fun j ↦ mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) inc z (v j)) = α z v
  rw [hext]
  simp only [pullback_apply]
  have hvec : (fun j ↦ mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) g z.val
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) inc z (v j))) = v := by
    funext j
    change ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) g z.val).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) inc z)) (v j) = v j
    exact congrArg (fun L ↦ L (v j)) hchain.symm
  rw [hvec]
  exact congrArg (fun y : U ↦ (show ContinuousAlternatingMap ℝ E ℝ (Fin k) from α y) v) hgval

/-- Centered-chart regularity transports to each maximal chart through
the same point, using the genuine coordinate-change pullback identity. -/
theorem isSmoothAtInCharts_of_centeredChartSmoothAt
    (α : Form 𝓘(ℝ,E) M k) (x : M)
    (hα : ContDiffAt ℝ ∞ (chartRepresentation (chartAt E x) α) (chartAt E x x)) :
    StokesLocalization.IsSmoothAtInCharts α x := by
  intro e he hx
  let e' := chartAt E x
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hy' : id (e.symm (e x)) ∈ e'.source := by
    simpa only [id_eq, e.left_inv hx] using mem_chart_source E x
  have hc := coordinateMap_contDiffAt e e' he he' id contMDiff_id
    (e x) (e.map_source hx) hy'
  have ha : ContDiffAt ℝ ∞ (chartRepresentation e' α) (coordinateMap e e' id (e x)) := by
    simpa only [coordinateMap, Function.comp_apply, id_eq, e.left_inv hx] using hα
  have hp := contDiffAt_compContinuousLinearMap (ha.comp (e x) hc)
    (hc.fderiv_right (m := ∞) (by simp))
  have heq := chartRepresentation_pullback_eventuallyEq e e' he he' id contMDiff_id
    α (e x) (e.map_source hx) hy'
  simpa only [pullback_id] using hp.congr_of_eventuallyEq heq

theorem isSmoothAtInCharts_extendOpenForm (U : TopologicalSpace.Opens M)
    (α : Form 𝓘(ℝ,E) U k) (hα : IsSmooth α) (x : M) (hx : x ∈ U) :
    StokesLocalization.IsSmoothAtInCharts (extendOpenForm U α) x := by
  apply isSmoothAtInCharts_of_centeredChartSmoothAt
  apply contDiffAt_chartRepresentation_of_smooth_restriction U _ _ x hx
  rw [pullback_extendOpenForm]
  exact hα

/-- Changing a target model by an actual equality changes no pullback.
This transports the model parameter itself, including its derivative. -/
theorem pullback_eq_of_target_model_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q]
    (J K : ModelWithCorners ℝ F H) (hJK : J = K)
    (f : M → Q) (α : Form J Q k) :
    pullback (I := 𝓘(ℝ,E)) (I' := J) f α =
      pullback (I := 𝓘(ℝ,E)) (I' := K) f α := by
  subst K
  rfl

/-- The degree cast commutes with an actual pullback for any target
model parameter on the same underlying Euclidean chart space. -/
theorem pullback_degreeCast_target_model
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace F Q] [IsManifold 𝓘(ℝ,F) ∞ Q]
    (J : ModelWithCorners ℝ F F) (f : M → Q) {r t : ℕ} (hrt : r = t)
    (α : Form 𝓘(ℝ,F) Q r) :
    pullback (I := 𝓘(ℝ,E)) (I' := J) f (degreeCastForm hrt α) =
      degreeCastForm hrt (pullback (I := 𝓘(ℝ,E)) (I' := J) f α) := by
  subst t
  rfl

end GaussBonnetChern.DifferentialForm

namespace GaussBonnetChern
open DifferentialForm StokesLocalization
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] [Fact (0<n)]

/-- The actual Chern angular form pulled back along the actual normalized
field, and then totalized in the ambient manifold. -/
def normalizedFieldAngularForm (a : FiniteOrientedAtlas n M)
    (X : (x : M) → TangentSpace (model n) x)
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X)) :
    Form (model n) M (2*n-1) :=
  extendOpenForm (nonzeroFieldDomain n M X hX)
    (pullback (I := model n) (normalizedSphereSection n M X hX)
      (atlasSphereAngularForm n M a))

theorem normalizedFieldAngularForm_restrict (a : FiniteOrientedAtlas n M)
    (X : (x : M) → TangentSpace (model n) x)
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X)) :
    pullback (I := model n) ((↑) : nonzeroFieldDomain n M X hX → M)
      (normalizedFieldAngularForm n M a X hX) =
      pullback (I := model n) (normalizedSphereSection n M X hX)
        (atlasSphereAngularForm n M a) := pullback_extendOpenForm _ _

theorem isSmoothAtInCharts_normalizedFieldAngularForm (a : FiniteOrientedAtlas n M)
    (X : (x : M) → TangentSpace (model n) x)
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X))
    (x : M) (hx : X x ≠ 0) :
    IsSmoothAtInCharts (normalizedFieldAngularForm n M a X hX) x := by
  apply isSmoothAtInCharts_extendOpenForm
  exact (isSmooth_atlasSphereAngularForm n M a).pullback
    (normalizedSphereSection n M X hX) (contMDiff_normalizedSphereSection n M X hX)
  exact hx

/-- Actual exterior transgression at every nonzero point. The geometric
global Chern identity is discharged by the imported theorem. -/
theorem normalizedFieldAngularForm_transgression (a : FiniteOrientedAtlas n M)
    (X : (x : M) → TangentSpace (model n) x)
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X))
    (x : M) (hx : X x ≠ 0) :
    degreeCastForm (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
      (exteriorDerivative (normalizedFieldAngularForm n M a X hX)) x =
        -atlasEulerForm n M a Fact.out x := by
  let U := nonzeroFieldDomain n M X hX
  let inc : U → M := (↑)
  let s := normalizedSphereSection n M X hX
  let Ψ := atlasSphereAngularForm n M a
  let β := normalizedFieldAngularForm n M a X hX
  let e := atlasEulerForm n M a Fact.out
  have hs : ContMDiff (model n) 𝓘(ℝ,SphereBundleModel n) ∞ s := by
    simpa only [sphereBundleModel_eq_self] using contMDiff_normalizedSphereSection n M X hX
  have hΨ : IsSmooth Ψ := isSmooth_atlasSphereAngularForm n M a
  have hd := restrict_exteriorDerivative_of_chartSmoothAt U β (fun y hy ↦
    isSmoothAtInCharts_normalizedFieldAngularForm n M a X hX y hy
      (chartAt (Model n) y) (IsManifold.chart_mem_maximalAtlas y)
      (mem_chart_source (Model n) y))
  have he : pullback (I := model n) s (sphereEulerForm n M a Fact.out) =
      pullback (I := model n) inc e := by
    change pullback (I := model n) (I' := sphereBundleModel n) s
      (pullback (I := sphereBundleModel n) (I' := model n) (UnitTangentSphere.proj n M) e) =
        pullback (I := model n) inc e
    exact (pullback_comp (I := model n) (I' := sphereBundleModel n) (I'' := model n)
      s (UnitTangentSphere.proj n M) e
      ((contMDiff_normalizedSphereSection n M X hX).mdifferentiable (by simp))
      ((contMDiff_unitTangentSphere_proj n M).mdifferentiable (by simp))).symm
  have hβ : pullback (I := model n) inc β =
      pullback (I := model n) (I' := sphereBundleModel n) s Ψ :=
    normalizedFieldAngularForm_restrict n M a X hX
  have hp_d : exteriorDerivative (pullback (I := model n) (I' := sphereBundleModel n) s Ψ) =
      pullback (I := model n) (I' := sphereBundleModel n) s (exteriorDerivative Ψ) := by
    have hp := pullback_eq_of_target_model_eq (E := Model n) (M := U)
      (F := SphereBundleModel n) (H := SphereBundleModel n) (Q := UnitTangentSphere n M)
      (sphereBundleModel n) 𝓘(ℝ,SphereBundleModel n)
      (sphereBundleModel_eq_self n) s Ψ
    have hdp := pullback_eq_of_target_model_eq (E := Model n) (M := U)
      (F := SphereBundleModel n) (H := SphereBundleModel n) (Q := UnitTangentSphere n M)
      (sphereBundleModel n) 𝓘(ℝ,SphereBundleModel n)
      (sphereBundleModel_eq_self n) s (exteriorDerivative Ψ)
    exact ((congrArg (fun γ : Form (model n) U (2*n-1) ↦ exteriorDerivative γ) hp).trans
      (pullback_exteriorDerivative s hs Ψ hΨ).symm).trans hdp.symm
  have hdβ : pullback (I := model n) inc (exteriorDerivative β) =
      pullback (I := model n) (I' := sphereBundleModel n) s (exteriorDerivative Ψ) :=
    (hd.trans (congrArg (fun γ : Form (model n) U (2*n-1) ↦ exteriorDerivative γ) hβ)).trans hp_d
  have hrestriction : pullback (I := model n) inc
      (degreeCastForm (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
        (exteriorDerivative β)) = pullback (I := model n) inc (-e) := by
    let hdegree : (2*n-1)+1=2*n := by have hn : 0<n := Fact.out; omega
    calc
      _ = degreeCastForm hdegree (pullback (I := model n) inc (exteriorDerivative β)) :=
        Chern.angularPullback_degreeCast inc hdegree (exteriorDerivative β)
      _ = degreeCastForm hdegree
          (pullback (I := model n) (I' := sphereBundleModel n) s (exteriorDerivative Ψ)) :=
        congrArg (fun γ : Form (model n) U ((2*n-1)+1) ↦ degreeCastForm hdegree γ) hdβ
      _ = pullback (I := model n) (I' := sphereBundleModel n) s
          (degreeCastForm hdegree (exteriorDerivative Ψ)) :=
        (pullback_degreeCast_target_model (E := Model n) (M := U)
          (F := SphereBundleModel n) (Q := UnitTangentSphere n M)
          (sphereBundleModel n) s hdegree (exteriorDerivative Ψ)).symm
      _ = pullback (I := model n) s (sphereAngularDerivative n M a) := rfl
      _ = pullback (I := model n) s (-sphereEulerForm n M a Fact.out) :=
        congrArg (pullback (I := model n) s) (sphereAngularDerivative_eq_neg_euler n M a)
      _ = pullback (I := model n) inc (-e) := by
        funext y
        ext v
        exact congrArg (fun η ↦ -(η y v)) he
  exact pullback_open_inclusion_at_injective U _ _ x hx (congrFun hrestriction ⟨x,hx⟩)

/-- Pulling back the totalized ambient form along a genuinely smooth map
in the nonzero locus recovers the actual normalized-section pullback. -/
theorem pullback_normalizedFieldAngularForm
    (a : FiniteOrientedAtlas n M)
    (X : (x : M) → TangentSpace (model n) x)
    (hX : ContMDiff (model n) (model n).tangent ∞ (T% X))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J ∞ P]
    (F : P → M) (hF : ContMDiff J (model n) ∞ F) (hnz : ∀ p, X (F p) ≠ 0) :
    pullback (I := J) F (normalizedFieldAngularForm n M a X hX) =
      pullback (I := J) (fun p ↦ UnitTangentSphere.ofNonzero n M (F p) (X (F p)) (hnz p))
        (atlasSphereAngularForm n M a) := by
  let U := nonzeroFieldDomain n M X hX
  let L : P → U := fun p ↦ ⟨F p, hnz p⟩
  let inc : U → M := (↑)
  let s := normalizedSphereSection n M X hX
  have hL : ContMDiff J (model n) ∞ L := by
    intro p
    apply (ContMDiffAt.subtypeVal_comp_iff U L p).mp
    exact hF p
  have hi := (contMDiff_subtype_val (I := model n) (n := ∞) (U := U)).mdifferentiable (by simp)
  have hs := (contMDiff_normalizedSphereSection n M X hX).mdifferentiable (by simp)
  calc
    _ = pullback (I := J) L (pullback (I := model n) inc
        (normalizedFieldAngularForm n M a X hX)) :=
      pullback_comp L inc _ (hL.mdifferentiable (by simp)) hi
    _ = pullback (I := J) L (pullback (I := model n) s (atlasSphereAngularForm n M a)) := by
      rw [normalizedFieldAngularForm_restrict]
    _ = pullback (I := J) (s ∘ L) (atlasSphereAngularForm n M a) :=
      (pullback_comp L s _ (hL.mdifferentiable (by simp)) hs).symm
    _ = _ := rfl

end GaussBonnetChern
