import GaussBonnetChern.FrameCoordinateStructure

/-! # Structure equations in any genuine smooth orthonormal frame

The basis may be specified arbitrarily away from its smooth local domain.
Every connection and curvature coefficient is computed from the original
Levi-Civita connection and curvature. No structural equation is assumed.
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

local instance : IsContMDiffRiemannianBundle (model n) 1 (Model n)
    (TangentSpace (model n) : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)

variable (E : (x : M) → OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x))

/-- Actual connection one-form in the specified orthonormal basis. -/
def smoothFrameConnectionOneForm (a b : Fin (2 * n)) : DifferentialForm.Form (model n) M 1 :=
  fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)
    ((innerSL ℝ (E x a)).comp (connection n M (fun y ↦ E y b) x))

@[simp] theorem smoothFrameConnectionOneForm_apply (a b : Fin (2 * n)) (x : M)
    (v : Fin 1 → TangentSpace (model n) x) :
    smoothFrameConnectionOneForm n M E a b x v = inner ℝ (E x a)
      (connection n M (fun y ↦ E y b) x (v 0)) := rfl

def smoothFrameCoefficient (a b : Fin (2 * n)) (x : M) (v : TangentSpace (model n) x) : ℝ :=
  smoothFrameConnectionOneForm n M E a b x ![v]

@[simp] theorem smoothFrameCoefficient_apply (a b : Fin (2 * n)) (x : M)
    (v : TangentSpace (model n) x) :
    smoothFrameCoefficient n M E a b x v = inner ℝ (E x a)
      (connection n M (fun y ↦ E y b) x v) := rfl

theorem smoothFrameConnectionOneForm_skew (a b : Fin (2 * n)) {x : M}
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x) :
    smoothFrameConnectionOneForm n M E a b x = -smoothFrameConnectionOneForm n M E b a x := by
  classical
  have hconst : (fun y ↦ inner ℝ (E y a) (E y b)) = fun _ ↦ if a = b then (1 : ℝ) else 0 :=
    funext fun y ↦ (E y).inner_eq_ite a b
  ext v
  have hm := (connection_isMetricCompatible n M).mvfderiv_inner_eq
    (extend (Model n) (x := x) (v 0))
    ((hE a).mdifferentiableAt (by simp)) ((hE b).mdifferentiableAt (by simp))
  rw [hconst, mvfderiv_const] at hm
  simp only [zero_apply, extend_apply_self] at hm
  rw [← real_inner_comm (connection n M (fun y ↦ E y a) x (v 0))] at hm
  simp only [ContinuousAlternatingMap.neg_apply, smoothFrameConnectionOneForm_apply]
  linarith

theorem smoothFrameCoefficient_skew (a b : Fin (2 * n)) {x : M}
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x)
    (v : TangentSpace (model n) x) :
    smoothFrameCoefficient n M E a b x v = -smoothFrameCoefficient n M E b a x v :=
  congrArg (fun af ↦ af ![v]) (smoothFrameConnectionOneForm_skew n M E a b hE)

theorem contMDiffAt_smoothFrameCoefficient_field (a b : Fin (2 * n))
    {X : (y : M) → TangentSpace (model n) y} {x : M}
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x)
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x) :
    ContMDiffAt (model n) 𝓘(ℝ) ∞ (fun y ↦ smoothFrameCoefficient n M E a b y (X y)) x :=
  (hE a).inner_bundle (contMDiffAt_connection_apply n M hX (hE b))

theorem smoothFrame_connection_inner_expansion (a b : Fin (2 * n)) {x : M}
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x)
    (u v : TangentSpace (model n) x) :
    inner ℝ (connection n M (fun y ↦ E y a) x u) (connection n M (fun y ↦ E y b) x v) =
      -(∑ c, smoothFrameCoefficient n M E a c x u * smoothFrameCoefficient n M E c b x v) := by
  rw [← (E x).sum_inner_mul_inner]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [real_inner_comm (E x c)]
  change smoothFrameCoefficient n M E c a x u * smoothFrameCoefficient n M E c b x v = _
  rw [smoothFrameCoefficient_skew n M E c a hE]
  ring

/-- The original curvature two-form in the specified orthonormal basis. -/
def smoothFrameCurvatureTwoForm (a b : Fin (2 * n)) : DifferentialForm.Form (model n) M 2 :=
  fun x ↦ curvatureTwoForm n M x (E x a) (E x b)

@[simp] theorem smoothFrameCurvatureTwoForm_apply (a b : Fin (2 * n)) (x : M)
    (v : Fin 2 → TangentSpace (model n) x) :
    smoothFrameCurvatureTwoForm n M E a b x v =
      inner ℝ (curvature n M x (v 0) (v 1) (E x b)) (E x a) := rfl

theorem smoothFrameCurvatureTwoForm_skew (a b : Fin (2 * n)) (x : M) :
    smoothFrameCurvatureTwoForm n M E a b x = -smoothFrameCurvatureTwoForm n M E b a x :=
  curvatureTwoForm_swap n M x _ _

theorem smoothFrameCartan_scalar (a b : Fin (2 * n))
    {X Y : (y : M) → TangentSpace (model n) y} {x : M}
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x)
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x) :
    smoothFrameCurvatureTwoForm n M E a b x ![X x, Y x] =
      mvfderiv (model n) (fun y ↦ smoothFrameCoefficient n M E a b y (Y y)) x (X x) -
      mvfderiv (model n) (fun y ↦ smoothFrameCoefficient n M E a b y (X y)) x (Y x) -
      smoothFrameCoefficient n M E a b x (VectorField.mlieBracket (model n) X Y x) +
      ∑ c, (smoothFrameCoefficient n M E a c x (X x) * smoothFrameCoefficient n M E c b x (Y x) -
        smoothFrameCoefficient n M E a c x (Y x) * smoothFrameCoefficient n M E c b x (X x)) := by
  have hYb := contMDiffAt_connection_apply n M hY (hE b)
  have hXb := contMDiffAt_connection_apply n M hX (hE b)
  have h1 := (connection_isMetricCompatible n M).mvfderiv_inner_eq X
    ((hE a).mdifferentiableAt (by simp)) (hYb.mdifferentiableAt (by simp))
  have h2 := (connection_isMetricCompatible n M).mvfderiv_inner_eq Y
    ((hE a).mdifferentiableAt (by simp)) (hXb.mdifferentiableAt (by simp))
  dsimp only at h1 h2
  rw [smoothFrame_connection_inner_expansion n M E a b hE (X x) (Y x)] at h1
  rw [smoothFrame_connection_inner_expansion n M E a b hE (Y x) (X x)] at h2
  have hR := congrArg (fun z ↦ inner ℝ (E x a) z) (curvature_apply n M hX hY (hE b))
  simp only [curvatureOnFields, inner_sub_right] at hR
  simp only [smoothFrameCurvatureTwoForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← real_inner_comm (curvature n M x (X x) (Y x) (E x b)), Finset.sum_sub_distrib]
  simp only [smoothFrameCoefficient_apply] at h1 h2 hR ⊢
  linarith

theorem contDiffAt_chartRepresentation_smoothFrameConnection (a b : Fin (2 * n))
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) {y : Model n} (hy : y ∈ e.target)
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun z ↦ E z i)) (e.symm y)) :
    ContDiffAt ℝ ∞
      (DifferentialForm.chartRepresentation e (smoothFrameConnectionOneForm n M E a b)) y := by
  let g : Model n → M := e.symm
  have hg := contMDiffAt_symm_of_mem_maximalAtlas he hy
  let L : Model n → Model n →L[ℝ] ℝ := fun z ↦ (innerSL ℝ (E (g z) a)).comp
    ((connection n M (fun w ↦ E w b) (g z)).comp (DifferentialForm.inverseChartTangentMap e z))
  have hL : ContMDiffAt (model n) 𝓘(ℝ, Model n →L[ℝ] ℝ) ∞ L y := by
    apply contMDiffAt_clm_of_apply n (Model n)
    intro w
    have hw : ContMDiffAt (model n) (model n).tangent ∞
        (fun z : Model n ↦ (⟨z, w⟩ : TangentBundle (model n) (Model n))) y :=
      contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
    have hd := (hg.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates hw hg
    have hc := ((contMDiffAt_connection_section n M (hE b)).comp y hg).clm_bundle_apply hd
    exact ((hE a).comp y hg).inner_bundle hc
  let A := ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Model n) (F := ℝ) (0 : Fin 1)
  have hs : ContDiffAt ℝ ∞ (fun z ↦ A (L z)) y :=
    A.toContinuousLinearEquiv.contDiff.contDiffAt.comp y hL.contDiffAt
  convert hs using 1
  funext z
  ext v
  rfl

/-- Actual Cartan equation for any smooth orthonormal frame germ, using an
arbitrary smooth chart. -/
theorem smoothFrameCartan_chart (a b : Fin (2 * n))
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) {x : M} (hx : x ∈ e.source)
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x) :
    smoothFrameCurvatureTwoForm n M E a b x =
      DifferentialForm.chartDerivative e (smoothFrameConnectionOneForm n M E a b) x +
      ∑ c, DifferentialForm.wedgeFiber (smoothFrameConnectionOneForm n M E a c x)
        (smoothFrameConnectionOneForm n M E c b x) := by
  ext v
  let X := extend (Model n) (x := x) (v 0)
  let Y := extend (Model n) (x := x) (v 1)
  have hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x := contMDiffAt_extend ..
  have hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x := contMDiffAt_extend ..
  have hfX := (contMDiffAt_smoothFrameCoefficient_field n M E a b hE hX).mdifferentiableAt (by simp)
  have hfY := (contMDiffAt_smoothFrameCoefficient_field n M E a b hE hY).mdifferentiableAt (by simp)
  have hA := contDiffAt_chartRepresentation_smoothFrameConnection n M E a b e he (e.map_source hx)
    (by simpa only [e.left_inv hx] using hE)
  have hd := chartDerivative_oneForm_apply_fields n M (smoothFrameConnectionOneForm n M E a b)
    e he hx hX hY hfX hfY (hA.differentiableAt (by simp))
  have hc := smoothFrameCartan_scalar n M E a b hE hX hY
  simp only [smoothFrameCoefficient] at hc
  rw [← hd] at hc
  have hv : ![X x, Y x] = v := by
    ext i
    fin_cases i <;> simp [X, Y]
  rw [← hv]
  simpa only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply,
    wedgeFiber_one_apply, smoothFrameCoefficient, X, Y, extend_apply_self] using hc

theorem smoothFrameCartan (a b : Fin (2 * n)) {x : M}
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x) :
    smoothFrameCurvatureTwoForm n M E a b x =
      DifferentialForm.exteriorDerivative (smoothFrameConnectionOneForm n M E a b) x +
      ∑ c, DifferentialForm.wedgeFiber (smoothFrameConnectionOneForm n M E a c x)
        (smoothFrameConnectionOneForm n M E c b x) :=
  smoothFrameCartan_chart n M E a b (chartAt (Model n) x)
    (IsManifold.chart_mem_maximalAtlas (I := model n) (n := ∞) x) (mem_chart_source (Model n) x) hE

def smoothFrameCoordinateConnection (e : OpenPartialHomeomorph M (Model n))
    (a b : Fin (2 * n)) : Model n → (Model n) [⋀^Fin 1]→L[ℝ] ℝ :=
  DifferentialForm.chartRepresentation e (smoothFrameConnectionOneForm n M E a b)

def smoothFrameCoordinateCurvature (e : OpenPartialHomeomorph M (Model n))
    (a b : Fin (2 * n)) : Model n → (Model n) [⋀^Fin 2]→L[ℝ] ℝ :=
  DifferentialForm.chartRepresentation e (smoothFrameCurvatureTwoForm n M E a b)

theorem smoothFrameCoordinateCurvature_eq (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (a b : Fin (2 * n))
    {y : Model n} (hy : y ∈ e.target)
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun z ↦ E z i)) (e.symm y)) :
    smoothFrameCoordinateCurvature n M E e a b y =
      DifferentialForm.connectionMatrixCurvature (smoothFrameCoordinateConnection n M E e) a b y := by
  ext v
  have hc := congrArg (fun af ↦ af (fun i ↦ DifferentialForm.inverseChartTangentMap e y (v i)))
    (smoothFrameCartan_chart n M E a b e he (e.map_target hy) hE)
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply,
    DifferentialForm.chartDerivative, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, e.right_inv hy,
    DifferentialForm.chartTangentMap_inverseChartTangentMap e he y hy] at hc
  simp only [DifferentialForm.connectionMatrixCurvature,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply]
  convert hc using 1
  · rfl
  · congr 1

theorem smoothFrameCoordinateCurvature_eventuallyEq {s : Set M} (hs : IsOpen s)
    (hE : ∀ i, ContMDiffOn (model n) (model n).tangent ∞ (T% (fun z ↦ E z i)) s)
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (a b : Fin (2 * n))
    {y : Model n} (hy : y ∈ e.target) (hys : e.symm y ∈ s) :
    smoothFrameCoordinateCurvature n M E e a b =ᶠ[𝓝 y]
      DifferentialForm.connectionMatrixCurvature (smoothFrameCoordinateConnection n M E e) a b := by
  have hp : e.symm ⁻¹' s ∈ 𝓝 y := (e.continuousAt_symm hy).preimage_mem_nhds (hs.mem_nhds hys)
  filter_upwards [e.open_target.mem_nhds hy, hp] with z hz hzs
  exact smoothFrameCoordinateCurvature_eq n M E e he a b hz
    (fun i ↦ (hE i).contMDiffAt (hs.mem_nhds hzs))

theorem smoothFrameCoordinate_bianchi {s : Set M} (hs : IsOpen s)
    (hE : ∀ i, ContMDiffOn (model n) (model n).tangent ∞ (T% (fun z ↦ E z i)) s)
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (a b : Fin (2 * n))
    {y : Model n} (hy : y ∈ e.target) (hys : e.symm y ∈ s) :
    extDeriv (smoothFrameCoordinateCurvature n M E e a b) y =
      ∑ c, (DifferentialForm.wedgeFiber (smoothFrameCoordinateCurvature n M E e a c y)
        (smoothFrameCoordinateConnection n M E e c b y) -
        DifferentialForm.wedgeFiber (smoothFrameCoordinateConnection n M E e a c y)
          (smoothFrameCoordinateCurvature n M E e c b y)) := by
  have hEq := smoothFrameCoordinateCurvature_eventuallyEq n M E hs hE e he a b hy hys
  have hd : extDeriv (smoothFrameCoordinateCurvature n M E e a b) y =
      extDeriv (DifferentialForm.connectionMatrixCurvature (smoothFrameCoordinateConnection n M E e) a b) y := by
    simp only [extDeriv, hEq.fderiv_eq]
  rw [hd, DifferentialForm.extDeriv_connectionMatrixCurvature
    (smoothFrameCoordinateConnection n M E e) y
    (fun i j ↦ contDiffAt_chartRepresentation_smoothFrameConnection n M E i j e he hy
      (fun k ↦ (hE k).contMDiffAt (hs.mem_nhds hys)))]
  apply Finset.sum_congr rfl
  intro c _
  rw [← (smoothFrameCoordinateCurvature_eventuallyEq n M E hs hE e he a c hy hys).self_of_nhds,
    ← (smoothFrameCoordinateCurvature_eventuallyEq n M E hs hE e he c b hy hys).self_of_nhds]

/-- The real local Bianchi equation for any genuinely smooth orthonormal
basis field. This applies to the positive chart frames as well as the original
trivialization frames once their actual smoothness is proved. -/
theorem smoothFrame_bianchi {s : Set M} (hs : IsOpen s)
    (hE : ∀ i, ContMDiffOn (model n) (model n).tangent ∞ (T% (fun z ↦ E z i)) s)
    (a b : Fin (2 * n)) {x : M} (hxs : x ∈ s) :
    DifferentialForm.exteriorDerivative (smoothFrameCurvatureTwoForm n M E a b) x =
      ∑ c, (DifferentialForm.wedgeFiber (smoothFrameCurvatureTwoForm n M E a c x)
        (smoothFrameConnectionOneForm n M E c b x) -
        DifferentialForm.wedgeFiber (smoothFrameConnectionOneForm n M E a c x)
          (smoothFrameCurvatureTwoForm n M E c b x)) := by
  let e := chartAt (Model n) x
  have he := IsManifold.chart_mem_maximalAtlas (I := model n) (n := ∞) x
  have hx : x ∈ e.source := mem_chart_source (Model n) x
  have hy : e x ∈ e.target := e.map_source hx
  have hxy : e.symm (e x) = x := e.left_inv hx
  have hc := smoothFrameCoordinate_bianchi n M E hs hE e he a b hy (by rw [hxy]; exact hxs)
  ext v
  have hv := congrArg (fun af ↦ af (fun i ↦ DifferentialForm.chartTangentMap e x (v i))) hc
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.sub_apply] at hv ⊢
  change extDeriv (smoothFrameCoordinateCurvature n M E e a b) (e x)
    (fun i ↦ DifferentialForm.chartTangentMap e x (v i)) = _
  rw [hv]
  apply Finset.sum_congr rfl
  intro c _
  have hleft := congrArg (fun af ↦ af v)
    (DifferentialForm.wedgeFiber_compContinuousLinearMap
      (smoothFrameCoordinateCurvature n M E e a c (e x))
      (smoothFrameCoordinateConnection n M E e c b (e x))
      (DifferentialForm.chartTangentMap e x))
  have hright := congrArg (fun af ↦ af v)
    (DifferentialForm.wedgeFiber_compContinuousLinearMap
      (smoothFrameCoordinateConnection n M E e a c (e x))
      (smoothFrameCoordinateCurvature n M E e c b (e x))
      (DifferentialForm.chartTangentMap e x))
  simp only [smoothFrameCoordinateCurvature, smoothFrameCoordinateConnection,
    DifferentialForm.chartRepresentation_recover e he _ x hx,
    ContinuousAlternatingMap.compContinuousLinearMap_apply] at hleft hright
  exact congrArg₂ (· - ·) hleft hright

theorem contDiffAt_smoothFrameCoordinateCurvature {s : Set M} (hs : IsOpen s)
    (hE : ∀ i, ContMDiffOn (model n) (model n).tangent ∞ (T% (fun z ↦ E z i)) s)
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (a b : Fin (2 * n))
    {y : Model n} (hy : y ∈ e.target) (hys : e.symm y ∈ s) :
    ContDiffAt ℝ ∞ (smoothFrameCoordinateCurvature n M E e a b) y := by
  have hA (i j : Fin (2 * n)) :
      ContDiffAt ℝ ∞ (smoothFrameCoordinateConnection n M E e i j) y :=
    contDiffAt_chartRepresentation_smoothFrameConnection n M E i j e he hy
      (fun k ↦ (hE k).contMDiffAt (hs.mem_nhds hys))
  have hd := DifferentialForm.contDiffAt_extDeriv (hA a b)
  have hw : ContDiffAt ℝ ∞
      (fun z ↦ ∑ c, DifferentialForm.wedgeFiber (smoothFrameCoordinateConnection n M E e a c z)
        (smoothFrameCoordinateConnection n M E e c b z)) y := by
    apply ContDiffAt.sum
    intro c _
    exact DifferentialForm.contDiffAt_wedgeFiber (hA a c) (hA c b)
  have hF : ContDiffAt ℝ ∞
      (DifferentialForm.connectionMatrixCurvature (smoothFrameCoordinateConnection n M E e) a b) y :=
    hd.add hw
  exact hF.congr_of_eventuallyEq
    (smoothFrameCoordinateCurvature_eventuallyEq n M E hs hE e he a b hy hys)

end GaussBonnetChern
