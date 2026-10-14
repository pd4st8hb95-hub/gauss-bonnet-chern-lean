import GaussBonnetChern.FrameStructureEquations
import GaussBonnetChern.ExteriorSmoothLinear

/-! # Cartan's equation in arbitrary smooth coordinates

The connection and curvature matrices are pullbacks of the actual local
Levi-Civita forms. No free coordinate curvature is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators
namespace GaussBonnetChern
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]
theorem chartDerivative_oneForm_apply_fields
    (af : DifferentialForm.Form (model n) M 1)
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    {X Y : (y : M) → TangentSpace (model n) y} {x : M}
    (hx : x ∈ e.source)
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hAfX : MDifferentiableAt (model n) 𝓘(ℝ) (fun y ↦ af y ![X y]) x)
    (hAfY : MDifferentiableAt (model n) 𝓘(ℝ) (fun y ↦ af y ![Y y]) x)
    (hA : DifferentiableAt ℝ (DifferentialForm.chartRepresentation e af)
      (e x)) :
    DifferentialForm.chartDerivative e af x ![X x, Y x] =
      mvfderiv (model n) (fun y ↦ af y ![Y y]) x (X x) -
      mvfderiv (model n) (fun y ↦ af y ![X y]) x (Y x) -
      af x ![VectorField.mlieBracket (model n) X Y x] := by
  let : IsManifold (model n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (model n) 2 M)
  let g : Model n → M := e.symm
  let q := e x
  let XP := VectorField.mpullback (model n) (model n) g X
  let YP := VectorField.mpullback (model n) (model n) g Y
  have hq : q ∈ e.target := e.map_source hx
  have hqx : g q = x := e.left_inv hx
  have hge (z : Model n) (hz : z ∈ e.target) : ContMDiffAt (model n) (model n) ∞ g z :=
    contMDiffAt_symm_of_mem_maximalAtlas he hz
  have hgi (z : Model n) (hz : z ∈ e.target) :
      (mfderiv (model n) (model n) g z).IsInvertible :=
    ⟨(show e.MDifferentiable (model n) (model n) from
      ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
       (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩).symm.mfderiv hz, rfl⟩
  have hXg : ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g q) := by simpa [hqx] using hX
  have hYg : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) (g q) := by simpa [hqx] using hY
  have hXP := hXg.mpullback_vectorField_preimage (hge q hq) (hgi q hq) (by simp)
  have hYP := hYg.mpullback_vectorField_preimage (hge q hq) (hgi q hq) (by simp)
  have hEval (V : (y : M) → TangentSpace (model n) y) (z : Model n) (hz : z ∈ e.target) :
      DifferentialForm.chartRepresentation e af z
        ![VectorField.mpullback (model n) (model n) g V z] = af (g z) ![V (g z)] := by
    rw [DifferentialForm.chartRepresentation_eq]
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      DifferentialForm.inverseChartTangentMap, ContinuousLinearMap.comp_apply,
      VectorField.mpullback_apply]
    congr 1
    funext i
    fin_cases i
    exact (hgi z hz).self_apply_inverse _
  have hEq (V : (y : M) → TangentSpace (model n) y) :
      (fun z ↦ DifferentialForm.chartRepresentation e af z
        ![VectorField.mpullback (model n) (model n) g V z]) =ᶠ[𝓝 q]
      (fun z ↦ af (g z) ![V (g z)]) := by
    filter_upwards [e.open_target.mem_nhds hq] with z hz
    exact hEval V z hz
  have hcoord (V : (y : M) → TangentSpace (model n) y) :
      VectorField.mpullback (model n) (model n) g V q = DifferentialForm.chartTangentMap e x (V x) := by
    apply (hgi q hq).injective
    simp only [VectorField.mpullback_apply]
    rw [(hgi q hq).self_apply_inverse]
    have hh := (DifferentialForm.inverseChartTangentMap_chartTangentMap e he x hx (V x)).symm
    change V x = (mfderiv (model n) (model n) g q) (DifferentialForm.chartTangentMap e x (V x)) at hh
    rw [hqx]
    exact hh
  have h := extDeriv_oneForm_apply_fields n hA
    ((contMDiffAt_vectorSpace_iff_contDiffAt.mp hXP).differentiableAt (by simp))
    ((contMDiffAt_vectorSpace_iff_contDiffAt.mp hYP).differentiableAt (by simp))
  have hbr := VectorField.mpullback_mlieBracket
    (hXg.mdifferentiableAt (by simp)) (hYg.mdifferentiableAt (by simp)) (hge q hq) (by simp)
  have hbr' : VectorField.lieBracket ℝ XP YP q =
      VectorField.mpullback (model n) (model n) g (VectorField.mlieBracket (model n) X Y) q := by
    simpa only [VectorField.mlieBracket, VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracket, VectorField.lieBracketWithin, fderivWithin_univ, XP, YP] using hbr.symm
  rw [hbr', hEval _ q hq] at h
  rw [(hEq Y).fderiv_eq, (hEq X).fderiv_eq] at h
  have hdy := mvfderiv_mpullback_scalar n M X q
    (show MDifferentiableAt (model n) 𝓘(ℝ) (fun y ↦ af y ![Y y]) (g q) from hqx.symm ▸ hAfY)
    ((hge q hq).mdifferentiableAt (by simp)) (hgi q hq)
  have hdx := mvfderiv_mpullback_scalar n M Y q
    (show MDifferentiableAt (model n) 𝓘(ℝ) (fun y ↦ af y ![X y]) (g q) from hqx.symm ▸ hAfX)
    ((hge q hq).mdifferentiableAt (by simp)) (hgi q hq)
  simp only [mvfderiv_eq_fderiv, Function.comp_def] at hdy hdx
  erw [hdy, hdx, hqx] at h
  erw [hcoord X, hcoord Y] at h
  have htuple : (fun i : Fin 2 ↦ DifferentialForm.chartTangentMap e x (![X x, Y x] i)) =
      ![DifferentialForm.chartTangentMap e x (X x), DifferentialForm.chartTangentMap e x (Y x)] := by
    ext i
    fin_cases i <;> rfl
  simpa only [DifferentialForm.exteriorDerivative, DifferentialForm.chartDerivative,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, htuple,
    XP, YP, q] using h


/-- Cartan's actual curvature equation computed using any smooth chart on
the local frame domain. -/
theorem localCartan_chartStructureEquation (p : M) (a b : Fin (2 * n))
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) {x : M} (hx : x ∈ e.source)
    (hxp : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    localOrthonormalCurvatureForm n M p a b x =
      DifferentialForm.chartDerivative e (localConnectionOneForm n M p a b) x +
      ∑ c, DifferentialForm.wedgeFiber (localConnectionOneForm n M p a c x)
        (localConnectionOneForm n M p c b x) := by
  ext v
  let X := FiberBundle.extend (Model n) (x := x) (v 0)
  let Y := FiberBundle.extend (Model n) (x := x) (v 1)
  have hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x := contMDiffAt_extend ..
  have hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x := contMDiffAt_extend ..
  have hfX := (contMDiffAt_connectionCoefficient_field n M p a b hxp hX).mdifferentiableAt (by simp)
  have hfY := (contMDiffAt_connectionCoefficient_field n M p a b hxp hY).mdifferentiableAt (by simp)
  have hA := contDiffAt_chartRepresentation_localConnectionOneForm n M p a b e he
    (e.map_source hx) (by rw [e.left_inv hx]; exact hxp)
  have hd := chartDerivative_oneForm_apply_fields n M (localConnectionOneForm n M p a b)
    e he hx hX hY hfX hfY (hA.differentiableAt (by simp))
  have hc := localCartan_scalar n M p a b hxp hX hY
  simp only [connectionCoefficient] at hc
  rw [← hd] at hc
  have hv : ![X x, Y x] = v := by
    ext i
    fin_cases i <;> simp [X, Y]
  rw [← hv]
  simpa only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply,
    wedgeFiber_one_apply, connectionCoefficient, X, Y, FiberBundle.extend_apply_self] using hc

/-- The actual connection matrix pulled back to a smooth chart. -/
def coordinateConnectionForm (p : M) (e : OpenPartialHomeomorph M (Model n))
    (a b : Fin (2 * n)) : Model n → (Model n) [⋀^Fin 1]→L[ℝ] ℝ :=
  DifferentialForm.chartRepresentation e (localConnectionOneForm n M p a b)

/-- The actual curvature matrix pulled back to the same smooth chart. -/
def coordinateCurvatureForm (p : M) (e : OpenPartialHomeomorph M (Model n))
    (a b : Fin (2 * n)) : Model n → (Model n) [⋀^Fin 2]→L[ℝ] ℝ :=
  DifferentialForm.chartRepresentation e (localOrthonormalCurvatureForm n M p a b)

theorem contDiffAt_coordinateConnectionForm (p : M)
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (a b : Fin (2 * n))
    {y : Model n} (hy : y ∈ e.target)
    (hyp : e.symm y ∈
      (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ContDiffAt ℝ ∞ (coordinateConnectionForm n M p e a b) y :=
  contDiffAt_chartRepresentation_localConnectionOneForm n M p a b e he hy hyp

/-- Curvature in genuine chart coordinates is exactly `dA + A ∧ A` for the
genuine Levi-Civita connection matrix in those coordinates. -/
theorem coordinateCurvatureForm_eq (p : M) (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (a b : Fin (2 * n))
    {y : Model n} (hy : y ∈ e.target)
    (hyp : e.symm y ∈
      (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    coordinateCurvatureForm n M p e a b y =
      extDeriv (coordinateConnectionForm n M p e a b) y +
      ∑ c, DifferentialForm.wedgeFiber (coordinateConnectionForm n M p e a c y)
        (coordinateConnectionForm n M p e c b y) := by
  ext v
  have hc := congrArg (fun af ↦ af (fun i ↦ DifferentialForm.inverseChartTangentMap e y (v i)))
    (localCartan_chartStructureEquation n M p a b e he (e.map_target hy) hyp)
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply,
    DifferentialForm.chartDerivative, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, e.right_inv hy,
    DifferentialForm.chartTangentMap_inverseChartTangentMap e he y hy] at hc
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply]
  convert hc using 1
  · rfl
  · congr 1

/-- The genuine local curvature matrix has smooth coefficients in every
smooth chart on the frame domain. -/
theorem contDiffAt_coordinateCurvatureForm (p : M)
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (a b : Fin (2 * n))
    {y : Model n} (hy : y ∈ e.target)
    (hyp : e.symm y ∈
      (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ContDiffAt ℝ ∞ (coordinateCurvatureForm n M p e a b) y := by
  have hA := contDiffAt_coordinateConnectionForm n M p e he a b hy hyp
  have hd : ContDiffAt ℝ ∞ (extDeriv (coordinateConnectionForm n M p e a b)) y :=
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Model n) ℝ).contDiff.contDiffAt.comp y
      (hA.fderiv_right (by simp))
  have hw : ContDiffAt ℝ ∞
      (fun z ↦ ∑ c, DifferentialForm.wedgeFiber (coordinateConnectionForm n M p e a c z)
        (coordinateConnectionForm n M p e c b z)) y := by
    apply ContDiffAt.sum
    intro c _
    exact DifferentialForm.contDiffAt_wedgeFiber
      (contDiffAt_coordinateConnectionForm n M p e he a c hy hyp)
      (contDiffAt_coordinateConnectionForm n M p e he c b hy hyp)
  apply (hd.add hw).congr_of_eventuallyEq
  let t := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p
  have hp : e.symm ⁻¹' t.baseSet ∈ 𝓝 y :=
    (e.continuousAt_symm hy).preimage_mem_nhds (t.open_baseSet.mem_nhds hyp)
  filter_upwards [e.open_target.mem_nhds hy, hp] with z hz hzp
  exact coordinateCurvatureForm_eq n M p e he a b hz hzp

/-- The actual curvature coordinate matrix agrees with the connection
curvature as a germ, which permits exterior differentiation of the identity. -/
theorem coordinateCurvatureForm_eventuallyEq (p : M)
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (a b : Fin (2 * n))
    {y : Model n} (hy : y ∈ e.target)
    (hyp : e.symm y ∈
      (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    coordinateCurvatureForm n M p e a b =ᶠ[𝓝 y]
      DifferentialForm.connectionMatrixCurvature (coordinateConnectionForm n M p e) a b := by
  let t := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p
  have hp : e.symm ⁻¹' t.baseSet ∈ 𝓝 y :=
    (e.continuousAt_symm hy).preimage_mem_nhds (t.open_baseSet.mem_nhds hyp)
  filter_upwards [e.open_target.mem_nhds hy, hp] with z hz hzp
  exact coordinateCurvatureForm_eq n M p e he a b hz hzp

/-- Bianchi's equation for the genuine Levi-Civita curvature matrix in
arbitrary local coordinates. -/
theorem coordinateCurvatureForm_bianchi (p : M)
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (a b : Fin (2 * n))
    {y : Model n} (hy : y ∈ e.target)
    (hyp : e.symm y ∈
      (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    extDeriv (coordinateCurvatureForm n M p e a b) y =
      ∑ c, (DifferentialForm.wedgeFiber (coordinateCurvatureForm n M p e a c y)
        (coordinateConnectionForm n M p e c b y) -
        DifferentialForm.wedgeFiber (coordinateConnectionForm n M p e a c y)
          (coordinateCurvatureForm n M p e c b y)) := by
  have hEq := coordinateCurvatureForm_eventuallyEq n M p e he a b hy hyp
  have hd : extDeriv (coordinateCurvatureForm n M p e a b) y =
      extDeriv (DifferentialForm.connectionMatrixCurvature (coordinateConnectionForm n M p e) a b) y := by
    simp only [extDeriv, hEq.fderiv_eq]
  rw [hd, DifferentialForm.extDeriv_connectionMatrixCurvature
    (coordinateConnectionForm n M p e) y
    (fun i j ↦ contDiffAt_coordinateConnectionForm n M p e he i j hy hyp)]
  apply Finset.sum_congr rfl
  intro c _
  rw [← (coordinateCurvatureForm_eventuallyEq n M p e he a c hy hyp).self_of_nhds,
    ← (coordinateCurvatureForm_eventuallyEq n M p e he c b hy hyp).self_of_nhds]

/-- Bianchi's matrix equation for the actual local Levi-Civita curvature
forms on the manifold, with the project's actual exterior derivative. -/
theorem localCurvature_bianchi (p : M) (a b : Fin (2 * n)) {x : M}
    (hxp : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    DifferentialForm.exteriorDerivative (localOrthonormalCurvatureForm n M p a b) x =
      ∑ c, (DifferentialForm.wedgeFiber (localOrthonormalCurvatureForm n M p a c x)
        (localConnectionOneForm n M p c b x) -
        DifferentialForm.wedgeFiber (localConnectionOneForm n M p a c x)
          (localOrthonormalCurvatureForm n M p c b x)) := by
  let e := chartAt (Model n) x
  have he := IsManifold.chart_mem_maximalAtlas (I := model n) (n := ∞) x
  have hx : x ∈ e.source := mem_chart_source (Model n) x
  have hy : e x ∈ e.target := e.map_source hx
  have hxy : e.symm (e x) = x := e.left_inv hx
  have hc := coordinateCurvatureForm_bianchi n M p e he a b hy (by rw [hxy]; exact hxp)
  ext v
  have hv := congrArg (fun af ↦ af (fun i ↦ DifferentialForm.chartTangentMap e x (v i))) hc
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.sub_apply] at hv ⊢
  change extDeriv (coordinateCurvatureForm n M p e a b) (e x)
    (fun i ↦ DifferentialForm.chartTangentMap e x (v i)) = _
  rw [hv]
  apply Finset.sum_congr rfl
  intro c _
  have hleft := congrArg (fun af ↦ af v)
    (DifferentialForm.wedgeFiber_compContinuousLinearMap
      (coordinateCurvatureForm n M p e a c (e x))
      (coordinateConnectionForm n M p e c b (e x))
      (DifferentialForm.chartTangentMap e x))
  have hright := congrArg (fun af ↦ af v)
    (DifferentialForm.wedgeFiber_compContinuousLinearMap
      (coordinateConnectionForm n M p e a c (e x))
      (coordinateCurvatureForm n M p e c b (e x))
      (DifferentialForm.chartTangentMap e x))
  simp only [coordinateCurvatureForm, coordinateConnectionForm,
    DifferentialForm.chartRepresentation_recover e he _ x hx,
    ContinuousAlternatingMap.compContinuousLinearMap_apply] at hleft hright
  exact congrArg₂ (· - ·) hleft hright

end GaussBonnetChern
