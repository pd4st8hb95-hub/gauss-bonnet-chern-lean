import GaussBonnetChern.EulerForm
import GaussBonnetChern.ExteriorProduct
import Mathlib.Analysis.Calculus.DifferentialForm.VectorField

/-! # Actual local connection forms and Cartan identities

We use the column-frame convention `α_ab(X) = ⟪e_a, ∇_X e_b⟫`.
The corresponding curvature matrix is the original `B_ab = ⟪R(X,Y)e_b,e_a⟫`.
These are transpose indices relative to Chern's `de_i = ∑_j ω_ij e_j`.
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

def localConnectionOneForm (p : M) (a b : Fin (2*n)) :
    DifferentialForm.Form (model n) M 1 :=
  fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0:Fin 1)
    ((innerSL ℝ (localOrthonormalFrame n M p a x)).comp
      (connection n M (localOrthonormalFrame n M p b) x))

@[simp] theorem localConnectionOneForm_apply (p : M) (a b : Fin (2*n)) (x : M)
    (v : Fin 1 → TangentSpace (model n) x) :
    localConnectionOneForm n M p a b x v =
      inner ℝ (localOrthonormalFrame n M p a x)
        (connection n M (localOrthonormalFrame n M p b) x (v 0)) := rfl

theorem localConnectionOneForm_skew (p : M) (a b : Fin (2*n)) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    localConnectionOneForm n M p a b x = -localConnectionOneForm n M p b a x := by
  classical
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p
  have hconst : (fun y ↦ inner ℝ (localOrthonormalFrame n M p a y)
      (localOrthonormalFrame n M p b y)) =ᶠ[𝓝 x] (fun _ ↦ if a=b then (1:ℝ) else 0) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact (orthonormal_iff_ite.mp (localOrthonormalFrame_orthonormal n M p hy)) a b
  have hd : mvfderiv (model n) (fun y ↦ inner ℝ (localOrthonormalFrame n M p a y)
      (localOrthonormalFrame n M p b y)) x = 0 := by
    calc
      _ = mvfderiv (model n) (fun _ : M ↦ if a=b then (1:ℝ) else 0) x := hconst.mfderiv_eq
      _ = 0 := mvfderiv_const _
  ext v
  have ha := (contMDiffAt_localOrthonormalFrame n M p a hx).mdifferentiableAt (by simp)
  have hb := (contMDiffAt_localOrthonormalFrame n M p b hx).mdifferentiableAt (by simp)
  have hmetric := (connection_isMetricCompatible n M).mvfderiv_inner_eq
    (FiberBundle.extend (Model n) (x := x) (v 0)) ha hb
  rw [hd] at hmetric
  simp only [zero_apply, FiberBundle.extend_apply_self] at hmetric
  simp only [ContinuousAlternatingMap.neg_apply, localConnectionOneForm_apply]
  rw [← real_inner_comm (connection n M (localOrthonormalFrame n M p a) x (v 0))] at hmetric
  linarith

/-- Scalar connection coefficient in the local orthonormal frame. -/
def connectionCoefficient (p : M) (a b : Fin (2 * n)) (x : M)
    (v : TangentSpace (model n) x) : ℝ :=
  localConnectionOneForm n M p a b x ![v]

@[simp] theorem connectionCoefficient_apply (p : M) (a b : Fin (2 * n)) (x : M)
    (v : TangentSpace (model n) x) :
    connectionCoefficient n M p a b x v =
      inner ℝ (localOrthonormalFrame n M p a x)
        (connection n M (localOrthonormalFrame n M p b) x v) := rfl

theorem connectionCoefficient_skew (p : M) (a b : Fin (2 * n)) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (v : TangentSpace (model n) x) :
    connectionCoefficient n M p a b x v = -connectionCoefficient n M p b a x v := by
  exact congrArg (fun af ↦ af ![v]) (localConnectionOneForm_skew n M p a b hx)

theorem contMDiffAt_connectionCoefficient_field (p : M) (a b : Fin (2 * n))
    {X : (x : M) → TangentSpace (model n) x} {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x) :
    ContMDiffAt (model n) 𝓘(ℝ) ∞
      (fun y ↦ connectionCoefficient n M p a b y (X y)) x :=
  (contMDiffAt_localOrthonormalFrame n M p a hx).inner_bundle
    (contMDiffAt_connection_apply n M hX (contMDiffAt_localOrthonormalFrame n M p b hx))

theorem connection_inner_frame_expansion (p : M) (a b : Fin (2 * n)) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (u v : TangentSpace (model n) x) :
    inner ℝ (connection n M (localOrthonormalFrame n M p a) x u)
        (connection n M (localOrthonormalFrame n M p b) x v) =
      -(∑ c, connectionCoefficient n M p a c x u * connectionCoefficient n M p c b x v) := by
  let e := localOrthonormalBasis n M p x
  calc
    _ = ∑ c, connectionCoefficient n M p c a x u *
        connectionCoefficient n M p c b x v := by
      have h := e.sum_inner_mul_inner
        (connection n M (localOrthonormalFrame n M p a) x u)
        (connection n M (localOrthonormalFrame n M p b) x v)
      rw [← h]
      apply Finset.sum_congr rfl
      intro c _
      simp only [connectionCoefficient_apply, e, localOrthonormalBasis_apply n M p hx]
      rw [real_inner_comm (connection n M (localOrthonormalFrame n M p a) x u)]
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro c _
      rw [connectionCoefficient_skew n M p c a hx]
      ring

/-- The genuine local curvature matrix in the constructed orthonormal frame. -/
def localOrthonormalCurvatureForm (p : M) (a b : Fin (2 * n)) :
    DifferentialForm.Form (model n) M 2 :=
  fun x ↦ curvatureTwoForm n M x (localOrthonormalFrame n M p a x)
    (localOrthonormalFrame n M p b x)

@[simp] theorem localOrthonormalCurvatureForm_apply (p : M) (a b : Fin (2 * n)) (x : M)
    (v : Fin 2 → TangentSpace (model n) x) :
    localOrthonormalCurvatureForm n M p a b x v =
      inner ℝ (curvature n M x (v 0) (v 1) (localOrthonormalFrame n M p b x))
        (localOrthonormalFrame n M p a x) := rfl

theorem localOrthonormalCurvatureForm_skew (p : M) (a b : Fin (2 * n)) (x : M) :
    localOrthonormalCurvatureForm n M p a b x =
      -localOrthonormalCurvatureForm n M p b a x :=
  curvatureTwoForm_swap n M x _ _

/-- Cartan's curvature identity evaluated on smooth field germs, with every
coefficient defined from the actual Levi-Civita connection. The exterior
derivative term is displayed explicitly by its directional-derivative formula. -/
theorem localCartan_scalar (p : M) (a b : Fin (2 * n))
    {X Y : (y : M) → TangentSpace (model n) y} {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x) :
    localOrthonormalCurvatureForm n M p a b x ![X x, Y x] =
      mvfderiv (model n) (fun y ↦ connectionCoefficient n M p a b y (Y y)) x (X x) -
      mvfderiv (model n) (fun y ↦ connectionCoefficient n M p a b y (X y)) x (Y x) -
      connectionCoefficient n M p a b x (VectorField.mlieBracket (model n) X Y x) +
      ∑ c, (connectionCoefficient n M p a c x (X x) * connectionCoefficient n M p c b x (Y x) -
        connectionCoefficient n M p a c x (Y x) * connectionCoefficient n M p c b x (X x)) := by
  have ha := contMDiffAt_localOrthonormalFrame n M p a hx
  have hb := contMDiffAt_localOrthonormalFrame n M p b hx
  have hYb := contMDiffAt_connection_apply n M hY hb
  have hXb := contMDiffAt_connection_apply n M hX hb
  have h1 := (connection_isMetricCompatible n M).mvfderiv_inner_eq X
    (ha.mdifferentiableAt (by simp)) (hYb.mdifferentiableAt (by simp))
  have h2 := (connection_isMetricCompatible n M).mvfderiv_inner_eq Y
    (ha.mdifferentiableAt (by simp)) (hXb.mdifferentiableAt (by simp))
  dsimp only at h1 h2
  rw [connection_inner_frame_expansion n M p a b hx (X x) (Y x)] at h1
  rw [connection_inner_frame_expansion n M p a b hx (Y x) (X x)] at h2
  have hR := congrArg (fun z ↦ inner ℝ (localOrthonormalFrame n M p a x) z)
    (curvature_apply n M hX hY hb)
  simp only [curvatureOnFields, inner_sub_right] at hR
  simp only [localOrthonormalCurvatureForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← real_inner_comm (curvature n M x (X x) (Y x) (localOrthonormalFrame n M p b x)),
    Finset.sum_sub_distrib]
  simp only [connectionCoefficient_apply] at h1 h2 hR ⊢
  linarith

/-- The actual local connection one-form has smooth chart coefficients on
the overlap of its frame domain with any smooth chart. -/
theorem contDiffAt_chartRepresentation_localConnectionOneForm (p : M)
    (a b : Fin (2 * n)) (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) {y : Model n}
    (hy : y ∈ e.target)
    (hx : e.symm y ∈
      (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ContDiffAt ℝ ∞
      (DifferentialForm.chartRepresentation e (localConnectionOneForm n M p a b)) y := by
  let g : Model n → M := e.symm
  have hg := contMDiffAt_symm_of_mem_maximalAtlas he hy
  have ha := contMDiffAt_localOrthonormalFrame n M p a hx
  have hb := contMDiffAt_localOrthonormalFrame n M p b hx
  let L : Model n → Model n →L[ℝ] ℝ := fun z ↦
    (innerSL ℝ (localOrthonormalFrame n M p a (g z))).comp
      ((connection n M (localOrthonormalFrame n M p b) (g z)).comp
        (DifferentialForm.inverseChartTangentMap e z))
  have hL : ContMDiffAt (model n) 𝓘(ℝ, Model n →L[ℝ] ℝ) ∞ L y := by
    apply contMDiffAt_clm_of_apply n (Model n)
    intro w
    have hw : ContMDiffAt (model n) (model n).tangent ∞
        (fun z : Model n ↦ (⟨z, w⟩ : TangentBundle (model n) (Model n))) y :=
      contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
    have hd := (hg.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates hw hg
    have hc := ((contMDiffAt_connection_section n M hb).comp y hg).clm_bundle_apply hd
    have h := (ha.comp y hg).inner_bundle hc
    exact h
  let A := ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Model n) (F := ℝ) (0 : Fin 1)
  have hs : ContDiffAt ℝ ∞ (fun z ↦ A (L z)) y :=
    A.toContinuousLinearEquiv.contDiff.contDiffAt.comp y hL.contDiffAt
  convert hs using 1
  funext z
  ext v
  rfl

/-- The standard degree-one exterior derivative formula in normed coordinates. -/
theorem extDeriv_oneForm_apply_fields
    {A : Model n → (Model n) [⋀^Fin 1]→L[ℝ] ℝ}
    {X Y : Model n → Model n} {z : Model n}
    (hA : DifferentiableAt ℝ A z)
    (hX : DifferentiableAt ℝ X z) (hY : DifferentiableAt ℝ Y z) :
    extDeriv A z ![X z, Y z] =
      fderiv ℝ (fun y ↦ A y ![Y y]) z (X z) -
      fderiv ℝ (fun y ↦ A y ![X y]) z (Y z) -
      A z ![VectorField.lieBracket ℝ X Y z] := by
  have hV : ∀ i : Fin 2, DifferentiableAt ℝ (![X, Y] i) z := by
    intro i
    fin_cases i
    · exact hX
    · exact hY
  have h := extDeriv_apply_vectorField (n := 0) (V := ![X, Y]) hA hV
  have htuple (y : Model n) : (fun i ↦ (![X, Y] i) y) = ![X y, Y y] := by
    ext i
    fin_cases i <;> rfl
  have hrem0 (y : Model n) : (0 : Fin 2).removeNth ![X y, Y y] = ![Y y] := by
    ext i
    fin_cases i
    rfl
  have hrem1 (y : Model n) : (1 : Fin 2).removeNth ![X y, Y y] = ![X y] := by
    ext i
    fin_cases i
    rfl
  simp only [htuple, Fin.sum_univ_two, Fin.sum_univ_one, hrem0, hrem1] at h
  simpa [sub_eq_add_neg, hrem0, hrem1] using h

/-- The degree-one exterior derivative on the manifold agrees with the
intrinsic vector-field formula. Its coordinate differentiability is an
explicit local hypothesis here, discharged for connection forms below. -/
theorem exteriorDerivative_oneForm_apply_fields
    (af : DifferentialForm.Form (model n) M 1)
    {X Y : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hAfX : MDifferentiableAt (model n) 𝓘(ℝ) (fun y ↦ af y ![X y]) x)
    (hAfY : MDifferentiableAt (model n) 𝓘(ℝ) (fun y ↦ af y ![Y y]) x)
    (hA : DifferentiableAt ℝ (DifferentialForm.chartRepresentation (chartAt (Model n) x) af)
      ((chartAt (Model n) x) x)) :
    DifferentialForm.exteriorDerivative af x ![X x, Y x] =
      mvfderiv (model n) (fun y ↦ af y ![Y y]) x (X x) -
      mvfderiv (model n) (fun y ↦ af y ![X y]) x (Y x) -
      af x ![VectorField.mlieBracket (model n) X Y x] := by
  let : IsManifold (model n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (model n) 2 M)
  let e := chartAt (Model n) x
  let g : Model n → M := e.symm
  let q := e x
  let XP := VectorField.mpullback (model n) (model n) g X
  let YP := VectorField.mpullback (model n) (model n) g Y
  have hx : x ∈ e.source := mem_chart_source (Model n) x
  have hq : q ∈ e.target := e.map_source hx
  have hqx : g q = x := e.left_inv hx
  have he := IsManifold.chart_mem_maximalAtlas (I := model n) (n := ∞) x
  have hge (z : Model n) (hz : z ∈ e.target) : ContMDiffAt (model n) (model n) ∞ g z :=
    contMDiffAt_symm_of_mem_maximalAtlas he hz
  have hgi (z : Model n) (hz : z ∈ e.target) :
      (mfderiv (model n) (model n) g z).IsInvertible :=
    ⟨(mdifferentiable_chart (I := model n) x).symm.mfderiv hz, rfl⟩
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
    e, XP, YP, q] using h

/-- Explicit degree-one exterior product; the formula retains the order of
the two arguments used in the curvature convention. -/
theorem wedgeFiber_one_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (a b : ContinuousAlternatingMap ℝ E ℝ (Fin 1)) (u v : E) :
    DifferentialForm.wedgeFiber a b ![u, v] = a ![u] * b ![v] - a ![v] * b ![u] := by
  classical
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
    ext σ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hσ : σ 0 = 0 ∨ σ 0 = 1 := by omega
    rcases hσ with hσ | hσ
    · left
      apply Equiv.ext
      intro i
      fin_cases i
      · exact hσ
      · have hn := σ.injective.ne (show (1 : Fin 2) ≠ 0 by decide)
        simp only [hσ] at hn
        have hh : σ 1 = 1 := Fin.ext (by omega)
        exact hh
    · right
      apply Equiv.ext
      intro i
      fin_cases i
      · simpa using hσ
      · have hn := σ.injective.ne (show (1 : Fin 2) ≠ 0 by decide)
        simp only [hσ] at hn
        have hh : σ 1 = 0 := Fin.ext (by omega)
        simpa using hh
  rw [DifferentialForm.wedgeFiber_apply]
  rw [hp]
  have hn : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro h
    have hh := congrArg (fun σ : Equiv.Perm (Fin 2) ↦ σ 0) h
    simp at hh
  have ha0 : (fun i : Fin 1 ↦ ![u, v] (Fin.castAdd 1 i)) = ![u] := by
    ext i; fin_cases i; rfl
  have hb1 : (fun j : Fin 1 ↦ ![u, v] j.succ) = ![v] := by
    ext i; fin_cases i; rfl
  have ha1 : (fun i : Fin 1 ↦ ![u, v] ((Equiv.swap 0 1) (Fin.castAdd 1 i))) = ![v] := by
    ext i; fin_cases i; simp
  have hb0 : (fun j : Fin 1 ↦ ![u, v] ((Equiv.swap 0 1) j.succ)) = ![u] := by
    ext i; fin_cases i; simp
  have hnot : (1 : Equiv.Perm (Fin 2)) ∉ ({Equiv.swap 0 1} : Finset (Equiv.Perm (Fin 2))) := by
    simpa only [Finset.mem_singleton] using hn
  have hnat : (Fin.natAdd 1 : Fin 1 → Fin 2) = Fin.succ := by
    funext i
    fin_cases i
    rfl
  simp only [Nat.factorial_one, Nat.cast_one, mul_one, inv_one, one_mul,
    Finset.sum_insert hnot, Finset.sum_singleton,
    Equiv.Perm.sign_one, one_smul, Equiv.Perm.one_apply,
    Equiv.Perm.sign_swap (show (0 : Fin 2) ≠ 1 by decide), neg_smul,
    hnat,
    ha0, hb1, ha1, hb0, sub_eq_add_neg]
  simp [Units.smul_def]

/-- Cartan's second structure equation for the actual local Levi-Civita
matrix, expressed with the project's genuine exterior derivative and wedge. -/
theorem localCartan_structureEquation (p : M) (a b : Fin (2 * n)) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    localOrthonormalCurvatureForm n M p a b x =
      DifferentialForm.exteriorDerivative (localConnectionOneForm n M p a b) x +
      ∑ c, DifferentialForm.wedgeFiber (localConnectionOneForm n M p a c x)
        (localConnectionOneForm n M p c b x) := by
  ext v
  let X := FiberBundle.extend (Model n) (x := x) (v 0)
  let Y := FiberBundle.extend (Model n) (x := x) (v 1)
  have hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x := contMDiffAt_extend ..
  have hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x := contMDiffAt_extend ..
  have hfX := (contMDiffAt_connectionCoefficient_field n M p a b hx hX).mdifferentiableAt (by simp)
  have hfY := (contMDiffAt_connectionCoefficient_field n M p a b hx hY).mdifferentiableAt (by simp)
  have hcx : (chartAt (Model n) x).symm ((chartAt (Model n) x) x) = x :=
    (chartAt (Model n) x).left_inv (mem_chart_source (Model n) x)
  have hA := contDiffAt_chartRepresentation_localConnectionOneForm n M p a b (chartAt (Model n) x)
    (IsManifold.chart_mem_maximalAtlas (I := model n) (n := ∞) x)
    (mem_chart_target (Model n) x) (by rw [hcx]; exact hx)
  have hd := exteriorDerivative_oneForm_apply_fields n M
    (localConnectionOneForm n M p a b) hX hY hfX hfY (hA.differentiableAt (by simp))
  have hc := localCartan_scalar n M p a b hx hX hY
  simp only [connectionCoefficient] at hc
  rw [← hd] at hc
  have hv : ![X x, Y x] = v := by
    ext i
    fin_cases i <;> simp [X, Y]
  rw [← hv]
  simpa only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply,
    wedgeFiber_one_apply, connectionCoefficient, X, Y, FiberBundle.extend_apply_self] using hc

end GaussBonnetChern
