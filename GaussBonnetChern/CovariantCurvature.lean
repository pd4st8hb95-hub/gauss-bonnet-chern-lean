import GaussBonnetChern.CurvatureTensor
import GaussBonnetChern.DifferentialForms

/-! # Covariant differentiation of the actual Riemannian curvature

The connection and curvature in these definitions are the same as those in
`StatementFor`. Identities use smooth local fields and impose no new geometric
hypothesis on the Gauss–Bonnet–Chern target.
-/

noncomputable section
open Bundle FiberBundle Filter
open scoped Manifold Topology ContDiff
namespace GaussBonnetChern
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

/-- Covariant differentiation of a tangent field in another field's direction. -/
abbrev covariantField (X Y : (y : M) → TangentSpace (model n) y) :
    (y : M) → TangentSpace (model n) y := fun y ↦ connection n M Y y (X y)

/-- Covariant derivative of the true curvature tensor, written on local fields. -/
def covariantCurvatureOnFields (X Y Z W : (y : M) → TangentSpace (model n) y)
    (x : M) : TangentSpace (model n) x :=
  covariantField n M X (curvatureOnFields n M Y Z W) x -
    curvatureOnFields n M (covariantField n M X Y) Z W x -
    curvatureOnFields n M Y (covariantField n M X Z) W x -
    curvatureOnFields n M Y Z (covariantField n M X W) x

set_option backward.isDefEq.respectTransparency false in
/-- Differentiating the connection commutator is legitimate on smooth germs. -/
theorem covariantField_curvatureOnFields
    {X Y Z W : (y : M) → TangentSpace (model n) y} {x : M}
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x) :
    covariantField n M X (curvatureOnFields n M Y Z W) x =
      covariantField n M X (covariantField n M Y (covariantField n M Z W)) x -
      covariantField n M X (covariantField n M Z (covariantField n M Y W)) x -
      covariantField n M X (covariantField n M (VectorField.mlieBracket (model n) Y Z) W) x := by
  have h1 := contMDiffAt_connection_apply n M hY (contMDiffAt_connection_apply n M hZ hW)
  have h2 := contMDiffAt_connection_apply n M hZ (contMDiffAt_connection_apply n M hY hW)
  have h3 := contMDiffAt_connection_apply n M (contMDiffAt_mlieBracket_smooth n M hY hZ) hW
  have h := congrArg (fun L : TangentSpace (model n) x →L[ℝ] TangentSpace (model n) x ↦ L (X x))
    (connection_sub n M (h1.sub_section h2) h3)
  rw [connection_sub n M h1 h2] at h
  unfold covariantField curvatureOnFields
  simpa only [sub_apply, Pi.sub_def] using h

/-- The actual covariant curvature derivative remains smooth on smooth germs. -/
theorem contMDiffAt_covariantCurvatureOnFields
    {X Y Z W : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x) :
    ContMDiffAt (model n) (model n).tangent ∞
      (T% (covariantCurvatureOnFields n M X Y Z W)) x := by
  exact (((contMDiffAt_connection_apply n M hX
      (contMDiffAt_curvatureOnFields n M hY hZ hW)).sub_section
      (contMDiffAt_curvatureOnFields n M (contMDiffAt_connection_apply n M hX hY) hZ hW)).sub_section
      (contMDiffAt_curvatureOnFields n M hY (contMDiffAt_connection_apply n M hX hZ) hW)).sub_section
      (contMDiffAt_curvatureOnFields n M hY hZ (contMDiffAt_connection_apply n M hX hW))

omit [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] in
/-- Jacobi for smooth tangent fields, in cyclic form. -/
theorem mlieBracket_cyclic_eq_zero
    {X Y Z : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x) :
    VectorField.mlieBracket (model n) X (VectorField.mlieBracket (model n) Y Z) x +
      VectorField.mlieBracket (model n) Y (VectorField.mlieBracket (model n) Z X) x +
      VectorField.mlieBracket (model n) Z (VectorField.mlieBracket (model n) X Y) x = 0 := by
  let : IsManifold (model n) (minSmoothness ℝ 3) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (model n) 3 M)
  have hXZ := contMDiffAt_mlieBracket_smooth n M hX hZ
  have hJac := VectorField.leibniz_identity_mlieBracket_apply
    (hX.of_le (by simp)) (hY.of_le (by simp)) (hZ.of_le (by simp))
  have hn : VectorField.mlieBracket (model n) Y (VectorField.mlieBracket (model n) Z X) x =
      -VectorField.mlieBracket (model n) Y (VectorField.mlieBracket (model n) X Z) x := by
    rw [VectorField.mlieBracket_swap (V := Z) (W := X)]
    simpa only [neg_one_smul] using VectorField.mlieBracket_const_smul_right
      (V := Y) (c := (-1 : ℝ)) (hXZ.mdifferentiableAt (by simp))
  rw [hJac, hn, VectorField.mlieBracket_swap (V := Z) (W := VectorField.mlieBracket (model n) X Y)]
  simp only [Pi.neg_apply]
  module

/-- The exterior covariant Bianchi identity of the genuine connection.
It follows from the operator Jacobi identity before using torsion-freeness. -/
theorem curvatureOnFields_covariant_bianchi
    {X Y Z W : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x) :
    (covariantField n M X (curvatureOnFields n M Y Z W) x -
      curvatureOnFields n M Y Z (covariantField n M X W) x +
      curvatureOnFields n M X (VectorField.mlieBracket (model n) Y Z) W x) +
    (covariantField n M Y (curvatureOnFields n M Z X W) x -
      curvatureOnFields n M Z X (covariantField n M Y W) x +
      curvatureOnFields n M Y (VectorField.mlieBracket (model n) Z X) W x) +
    (covariantField n M Z (curvatureOnFields n M X Y W) x -
      curvatureOnFields n M X Y (covariantField n M Z W) x +
      curvatureOnFields n M Z (VectorField.mlieBracket (model n) X Y) W x) = 0 := by
  have hJac := congrArg (connection n M W x) (mlieBracket_cyclic_eq_zero n M hX hY hZ)
  simp only [map_add, map_zero] at hJac
  rw [covariantField_curvatureOnFields n M hY hZ hW,
    covariantField_curvatureOnFields n M hZ hX hW,
    covariantField_curvatureOnFields n M hX hY hW]
  unfold curvatureOnFields covariantField
  linear_combination (norm := module) -hJac
/-- Torsion-freeness converts the antisymmetric direction correction into
curvature evaluated on the Lie bracket. -/
theorem curvatureOnFields_torsion_correction
    {X Y Z W : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x) :
    curvatureOnFields n M (covariantField n M X Y) Z W x -
      curvatureOnFields n M (covariantField n M Y X) Z W x =
      curvatureOnFields n M (VectorField.mlieBracket (model n) X Y) Z W x := by
  rw [← curvature_apply n M (contMDiffAt_connection_apply n M hX hY) hZ hW,
    ← curvature_apply n M (contMDiffAt_connection_apply n M hY hX) hZ hW,
    ← curvature_apply n M (contMDiffAt_mlieBracket_smooth n M hX hY) hZ hW]
  calc
    _ = curvature n M x (covariantField n M X Y x - covariantField n M Y X x) (Z x) (W x) := by
      change curvatureTensor n M x _ _ _ - curvatureTensor n M x _ _ _ =
        curvatureTensor n M x (_ - _) _ _
      simp only [(curvatureTensor n M x).map_sub, sub_apply]
    _ = _ := by rw [connection_torsion_apply n M (hX.mdifferentiableAt (by simp))
      (hY.mdifferentiableAt (by simp))]

/-- Second Bianchi for the covariant derivative of the actual curvature. -/
theorem covariantCurvatureOnFields_second_bianchi
    {X Y Z W : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x) :
    covariantCurvatureOnFields n M X Y Z W x +
      covariantCurvatureOnFields n M Y Z X W x +
      covariantCurvatureOnFields n M Z X Y W x = 0 := by
  have hb := curvatureOnFields_covariant_bianchi n M hX hY hZ hW
  have ht1 := curvatureOnFields_torsion_correction n M hX hY hZ hW
  have ht2 := curvatureOnFields_torsion_correction n M hY hZ hX hW
  have ht3 := curvatureOnFields_torsion_correction n M hZ hX hY hW
  rw [curvatureOnFields_swap n M X (VectorField.mlieBracket (model n) Y Z),
    curvatureOnFields_swap n M Y (VectorField.mlieBracket (model n) Z X),
    curvatureOnFields_swap n M Z (VectorField.mlieBracket (model n) X Y)] at hb
  unfold covariantCurvatureOnFields
  rw [curvatureOnFields_swap n M Y (covariantField n M X Z),
    curvatureOnFields_swap n M Z (covariantField n M Y X),
    curvatureOnFields_swap n M X (covariantField n M Z Y)]
  linear_combination (norm := module) hb - ht1 - ht2 - ht3
/-- The same covariant curvature derivative written directly with the original
pointwise curvature from `Geometry`. -/
def covariantCurvatureLocalFields (X Y Z W : (y : M) → TangentSpace (model n) y)
    (x : M) : TangentSpace (model n) x :=
  covariantField n M X (fun y ↦ curvature n M y (Y y) (Z y) (W y)) x -
    curvature n M x (covariantField n M X Y x) (Z x) (W x) -
    curvature n M x (Y x) (covariantField n M X Z x) (W x) -
    curvature n M x (Y x) (Z x) (covariantField n M X W x)

/-- On a genuine smooth local domain the field-commutator formula equals the
covariant derivative of the original curvature, including its derivative term. -/
theorem covariantCurvatureLocalFields_eq
    {X Y Z W : (y : M) → TangentSpace (model n) y} {s : Set M} {x : M}
    (hs : IsOpen s) (hx : x ∈ s)
    (hX : ContMDiffOn (model n) (model n).tangent ∞ (T% X) s)
    (hY : ContMDiffOn (model n) (model n).tangent ∞ (T% Y) s)
    (hZ : ContMDiffOn (model n) (model n).tangent ∞ (T% Z) s)
    (hW : ContMDiffOn (model n) (model n).tangent ∞ (T% W) s) :
    covariantCurvatureLocalFields n M X Y Z W x =
      covariantCurvatureOnFields n M X Y Z W x := by
  have hXx := hX.contMDiffAt (hs.mem_nhds hx)
  have hYx := hY.contMDiffAt (hs.mem_nhds hx)
  have hZx := hZ.contMDiffAt (hs.mem_nhds hx)
  have hWx := hW.contMDiffAt (hs.mem_nhds hx)
  have hraw := (contMDiffOn_curvature_apply n M hs hY hZ hW).contMDiffAt (hs.mem_nhds hx)
  have hfields := contMDiffAt_curvatureOnFields n M hYx hZx hWx
  have heq : ∀ᶠ y in 𝓝 x, curvature n M y (Y y) (Z y) (W y) =
      curvatureOnFields n M Y Z W y := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact curvature_apply n M (hY.contMDiffAt (hs.mem_nhds hy))
      (hZ.contMDiffAt (hs.mem_nhds hy)) (hW.contMDiffAt (hs.mem_nhds hy))
  have hc := (connection n M).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (hraw.mdifferentiableAt (by simp)) (hfields.mdifferentiableAt (by simp)) Filter.univ_mem heq
  unfold covariantCurvatureLocalFields covariantCurvatureOnFields covariantField
  rw [hc, curvature_apply n M (contMDiffAt_connection_apply n M hXx hYx) hZx hWx,
    curvature_apply n M hYx (contMDiffAt_connection_apply n M hXx hZx) hWx,
    curvature_apply n M hYx hZx (contMDiffAt_connection_apply n M hXx hWx)]

/-- Second Bianchi stated directly for the original curvature, on any smooth
local domain of the vector fields. -/
theorem covariantCurvatureLocalFields_second_bianchi
    {X Y Z W : (y : M) → TangentSpace (model n) y} {s : Set M} {x : M}
    (hs : IsOpen s) (hx : x ∈ s)
    (hX : ContMDiffOn (model n) (model n).tangent ∞ (T% X) s)
    (hY : ContMDiffOn (model n) (model n).tangent ∞ (T% Y) s)
    (hZ : ContMDiffOn (model n) (model n).tangent ∞ (T% Z) s)
    (hW : ContMDiffOn (model n) (model n).tangent ∞ (T% W) s) :
    covariantCurvatureLocalFields n M X Y Z W x +
      covariantCurvatureLocalFields n M Y Z X W x +
      covariantCurvatureLocalFields n M Z X Y W x = 0 := by
  rw [covariantCurvatureLocalFields_eq n M hs hx hX hY hZ hW,
    covariantCurvatureLocalFields_eq n M hs hx hY hZ hX hW,
    covariantCurvatureLocalFields_eq n M hs hx hZ hX hY hW]
  exact covariantCurvatureOnFields_second_bianchi n M
    (hX.contMDiffAt (hs.mem_nhds hx)) (hY.contMDiffAt (hs.mem_nhds hx))
    (hZ.contMDiffAt (hs.mem_nhds hx)) (hW.contMDiffAt (hs.mem_nhds hx))
local instance tensorModelNormOne : NormedAddCommGroup (Model n →L[ℝ] Model n) := inferInstance
local instance tensorModelSpaceOne : NormedSpace ℝ (Model n →L[ℝ] Model n) := inferInstance
local instance tensorModelNormTwo : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] Model n) := inferInstance
local instance tensorModelSpaceTwo : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] Model n) := inferInstance
local instance tensorModelNormThree : NormedAddCommGroup
    (Model n →L[ℝ] Model n →L[ℝ] Model n →L[ℝ] Model n) := inferInstance
local instance tensorModelSpaceThree : NormedSpace ℝ
    (Model n →L[ℝ] Model n →L[ℝ] Model n →L[ℝ] Model n) := inferInstance

set_option synthInstance.maxHeartbeats 80000 in
theorem contMDiff_curvatureTensor :
    ContMDiff (model n) ((model n).prod
      𝓘(ℝ, Model n →L[ℝ] Model n →L[ℝ] Model n →L[ℝ] Model n)) ∞
      (fun y ↦ TotalSpace.mk' (Model n →L[ℝ] Model n →L[ℝ] Model n →L[ℝ] Model n)
        y (curvatureTensor n M y)) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply n M
  intro u
  apply contMDiffAt_clm_of_apply n M
  intro v
  apply contMDiffAt_clm_of_apply n M
  intro w
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt' x
  have hframe (a : Model n) : ContMDiffOn (model n) (model n).tangent ∞
      (T% (fun y ↦ e.symmL ℝ y a)) e.baseSet := by
    intro y hy
    have he := e.contMDiffAt_symmL (IB := model n) (n := ∞) hy
    have ha : ContMDiffAt (model n) ((model n).prod 𝓘(ℝ, Model n)) ∞
        (fun z ↦ (⟨z, a⟩ : TotalSpace (Model n) (Bundle.Trivial M (Model n)))) y :=
      contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, contMDiffAt_const⟩
    exact (he.clm_bundle_apply ha).contMDiffWithinAt
  have hR := contMDiffOn_curvature_apply n M e.open_baseSet (hframe u) (hframe v) (hframe w)
  have hc := (contMDiffAt_section x).mp (hR.contMDiffAt (e.open_baseSet.mem_nhds hx))
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  have hy' : y ∈ (chartAt (Model n) x).source := hy
  simp (disch := simp [hom_trivializationAt_baseSet, hy, hy'])
    [ContinuousLinearMap.inCoordinates, Trivialization.continuousLinearMapAt_apply_of_mem, Trivialization.linearMapAt_apply, hom_trivializationAt_baseSet, hy, hy',
      hom_trivializationAt_apply, curvatureTensor_apply, e]

/-- Smoothness of the true curvature evaluated on any three smooth field
germs, obtained from the smooth curvature tensor bundle section. -/
theorem contMDiffAt_curvature_apply
    {X Y Z : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x) :
    ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun y ↦ curvature n M y (X y) (Y y) (Z y))) x := by
  have h := (((contMDiff_curvatureTensor n M x).clm_bundle_apply hX).clm_bundle_apply hY).clm_bundle_apply hZ
  simpa only [curvatureTensor_apply] using h
/-- The true curvature paired with two tangent vectors is a real two-form. -/
def curvatureTwoForm (x : M) (a b : TangentSpace (model n) x) :
    ContinuousAlternatingMap ℝ (TangentSpace (model n) x) ℝ (Fin 2) where
  toFun v := inner ℝ (curvature n M x (v 0) (v 1) b) a
  map_update_add' := by
    intro _ v i u u'
    fin_cases i <;> simp [curvature_add_first, curvature_add_second, inner_add_left]
  map_update_smul' := by
    intro _ v i c u
    fin_cases i <;> simp [curvature_smul_first, curvature_smul_second, real_inner_smul_left]
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    have hv : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    rw [← hv]
    have h := congrArg (fun w ↦ inner ℝ w a) (curvature_swap n M x (v 0) (v 0) b)
    simp only [inner_neg_left] at h
    linarith
  cont := by
    change Continuous (fun v : Fin 2 → TangentSpace (model n) x ↦
      inner ℝ (curvatureTensor n M x (v 0) (v 1) b) a)
    exact (((continuous_const.clm_apply (continuous_apply 0)).clm_apply
      (continuous_apply 1)).clm_apply continuous_const).inner continuous_const

@[simp] theorem curvatureTwoForm_apply (x : M) (a b : TangentSpace (model n) x)
    (v : Fin 2 → TangentSpace (model n) x) :
    curvatureTwoForm n M x a b v = inner ℝ (curvature n M x (v 0) (v 1) b) a := rfl

theorem curvatureTwoForm_swap (x : M) (a b : TangentSpace (model n) x) :
    curvatureTwoForm n M x a b = -curvatureTwoForm n M x b a := by
  ext v
  have h := curvature_inner_skew n M x (v 0) (v 1) b a
  rw [← real_inner_comm b] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Local matrix of curvature two-forms, paired against the genuine smooth
local frame in the fixed tangent trivialization. -/
def localCurvatureForms (p : M) (a b : Model n) : DifferentialForm.Form (model n) M 2 :=
  fun x ↦ curvatureTwoForm n M x (localFrameVector n M p a x) (localFrameVector n M p b x)

theorem localCurvatureForms_swap (p : M) (a b : Model n) :
    localCurvatureForms n M p a b = -localCurvatureForms n M p b a := by
  funext x
  exact curvatureTwoForm_swap n M x _ _

/-- Evaluation on the original orthonormal frame recovers the curvature
components used by the statement, with no replacement curvature data. -/
theorem curvatureComponents_eq_twoForm (x : M) (a b i j : Fin (2 * n)) :
    curvatureComponents n M x a b i j =
      curvatureTwoForm n M x (orthonormalFrame n M x a) (orthonormalFrame n M x b)
        ![orthonormalFrame n M x i, orthonormalFrame n M x j] := by
  simp [curvatureComponents, curvatureTwoForm_apply]

omit [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] in
/-- Constant vectors transported by a fixed local tangent trivialization are
smooth throughout its base set. -/
theorem contMDiffAt_localFrameVector_of_mem (p : M) (a : Model n) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ContMDiffAt (model n) (model n).tangent ∞ (T% (localFrameVector n M p a)) x := by
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p
  have he := e.contMDiffAt_symmL (IB := model n) (n := ∞) hx
  have ha : ContMDiffAt (model n) ((model n).prod 𝓘(ℝ, Model n)) ∞
      (fun y ↦ (⟨y, a⟩ : TotalSpace (Model n) (Bundle.Trivial M (Model n)))) x :=
    contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, contMDiffAt_const⟩
  exact he.clm_bundle_apply ha

/-- Scalar evaluations of the local matrix of genuine curvature forms are
smooth on the fixed frame domain, against arbitrary smooth direction fields. -/
theorem contMDiffOn_localCurvatureForms_apply (p : M) (a b : Model n)
    {X Y : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiffOn (model n) (model n).tangent ∞ (T% X)
      (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (hY : ContMDiffOn (model n) (model n).tangent ∞ (T% Y)
      (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ContMDiffOn (model n) 𝓘(ℝ) ∞
      (fun x ↦ localCurvatureForms n M p a b x ![X x, Y x])
      (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet := by
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p
  have hframe (v : Model n) : ContMDiffOn (model n) (model n).tangent ∞
      (T% (localFrameVector n M p v)) e.baseSet := by
    intro x hx
    exact (contMDiffAt_localFrameVector_of_mem n M p v hx).contMDiffWithinAt
  have hR := contMDiffOn_curvature_apply n M e.open_baseSet hX hY (hframe b)
  intro x hx
  have h := (hR.contMDiffAt (e.open_baseSet.mem_nhds hx)).inner_bundle
    (contMDiffAt_localFrameVector_of_mem n M p a hx)
  convert h.contMDiffWithinAt using 1
  funext y
  simp only [localCurvatureForms, curvatureTwoForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
/-- The local curvature matrix, indexed by the canonical Euclidean model
basis and taking values in genuine real two-forms. -/
def localCurvatureMatrixForms (p : M) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) (DifferentialForm.Form (model n) M 2) :=
  fun a b ↦ localCurvatureForms n M p (EuclideanSpace.basisFun (Fin (2 * n)) ℝ a)
    (EuclideanSpace.basisFun (Fin (2 * n)) ℝ b)

theorem localCurvatureMatrixForms_transpose (p : M) :
    (localCurvatureMatrixForms n M p).transpose = -localCurvatureMatrixForms n M p := by
  funext a b
  exact localCurvatureForms_swap n M p _ _
end GaussBonnetChern











