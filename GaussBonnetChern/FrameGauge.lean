import GaussBonnetChern.SmoothFrameStructure
import Mathlib.Analysis.InnerProductSpace.Orientation

/-! # Genuine changes of orthonormal frame

`P_ab = ⟪E_a,F_b⟫`, hence the columns of `P` are the new frame in the old
frame. The connection convention is `Γ_ab = ⟪E_a,∇E_b⟫` throughout.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle FiberBundle Module
open scoped Manifold ContDiff Topology BigOperators Matrix
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
variable (E F : (x : M) → OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x))

def frameChangeMatrix (x : M) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun a b ↦ inner ℝ (E x a) (F x b)

theorem frameChangeMatrix_eq_basisMatrix (x : M) :
    frameChangeMatrix n M E F x = (E x).toBasis.toMatrix (F x) := by
  ext a b
  simp [frameChangeMatrix, Basis.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

theorem frameChangeMatrix_transpose_mul (x : M) :
    (frameChangeMatrix n M E F x).transpose * frameChangeMatrix n M E F x = 1 := by
  rw [frameChangeMatrix_eq_basisMatrix]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (E x).toMatrix_orthonormalBasis_conjTranspose_mul_self (F x)

theorem frameChangeMatrix_mul_transpose (x : M) :
    frameChangeMatrix n M E F x * (frameChangeMatrix n M E F x).transpose = 1 := by
  rw [frameChangeMatrix_eq_basisMatrix]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (E x).toMatrix_orthonormalBasis_self_mul_conjTranspose (F x)

theorem frameChangeMatrix_det_eq_one_of_orientation (x : M)
    (h : (E x).toBasis.orientation = (F x).toBasis.orientation) :
    (frameChangeMatrix n M E F x).det = 1 := by
  rw [frameChangeMatrix_eq_basisMatrix]
  change (E x).toBasis.det (F x) = 1
  have hp := ((E x).toBasis.orientation_eq_iff_det_pos (F x).toBasis).mp h
  rcases (E x).det_to_matrix_orthonormalBasis_real (F x) with hd | hd
  · exact hd
  · simp only [OrthonormalBasis.coe_toBasis] at hp
    linarith

theorem contMDiffAt_frameChangeMatrix {x : M}
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x)
    (hF : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ F y i)) x) :
    ContMDiffAt (model n) 𝓘(ℝ, Fin (2 * n) → Fin (2 * n) → ℝ) ∞
      (fun y a b ↦ frameChangeMatrix n M E F y a b) x := by
  apply contMDiffAt_pi_space.mpr
  intro a
  apply contMDiffAt_pi_space.mpr
  intro b
  exact (hE a).inner_bundle (hF b)

/-- Actual tangent vector coordinates obey the transpose frame-change rule. -/
theorem frameCoordinates_change (x : M) (v : TangentSpace (model n) x) :
    (fun a ↦ inner ℝ (F x a) v) =
      (frameChangeMatrix n M E F x).transpose *ᵥ (fun a ↦ inner ℝ (E x a) v) := by
  funext a
  change inner ℝ (F x a) v =
    ∑ c, frameChangeMatrix n M E F x c a * inner ℝ (E x c) v
  have h := (E x).sum_inner_mul_inner (F x a) v
  rw [← h]
  apply Finset.sum_congr rfl
  intro c _
  simp only [frameChangeMatrix, Matrix.transpose_apply]
  rw [real_inner_comm (E x c)]

def frameConnectionMatrix (x : M) (v : TangentSpace (model n) x) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun a b ↦ smoothFrameCoefficient n M E a b x v

def frameCurvatureMatrix (x : M) (u v : TangentSpace (model n) x) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun a b ↦ smoothFrameCurvatureTwoForm n M E a b x ![u, v]

def frameChangeDerivative (x : M) (v : TangentSpace (model n) x) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun a b ↦ mvfderiv (model n) (fun y ↦ frameChangeMatrix n M E F y a b) x v

/-- The actual differential of the change-of-frame coefficients satisfies
`dP = P ΓF - ΓE P`, by metric compatibility. -/
theorem frameChangeDerivative_eq {x : M}
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x)
    (hF : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ F y i)) x)
    (v : TangentSpace (model n) x) :
    frameChangeDerivative n M E F x v =
      frameChangeMatrix n M E F x * frameConnectionMatrix n M F x v -
        frameConnectionMatrix n M E x v * frameChangeMatrix n M E F x := by
  ext a b
  have hm := (connection_isMetricCompatible n M).mvfderiv_inner_eq
    (extend (Model n) (x := x) v)
    ((hE a).mdifferentiableAt (by simp)) ((hF b).mdifferentiableAt (by simp))
  dsimp only at hm
  simp only [extend_apply_self] at hm
  have hleft : inner ℝ (connection n M (fun y ↦ E y a) x v) (F x b) =
      -(∑ c, smoothFrameCoefficient n M E a c x v * frameChangeMatrix n M E F x c b) := by
    rw [← (E x).sum_inner_mul_inner, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [real_inner_comm (E x c)]
    change smoothFrameCoefficient n M E c a x v * frameChangeMatrix n M E F x c b = _
    rw [smoothFrameCoefficient_skew n M E c a hE]
    ring
  have hright : inner ℝ (E x a) (connection n M (fun y ↦ F y b) x v) =
      ∑ c, frameChangeMatrix n M E F x a c * smoothFrameCoefficient n M F c b x v := by
    exact ((F x).sum_inner_mul_inner (E x a) (connection n M (fun y ↦ F y b) x v)).symm
  rw [hleft, hright] at hm
  simp only [frameChangeDerivative, frameChangeMatrix, frameConnectionMatrix,
    Matrix.sub_apply, Matrix.mul_apply] at hm ⊢
  linarith

/-- The genuine connection matrix obeys the usual inhomogeneous gauge law. -/
theorem frameConnectionMatrix_gauge {x : M}
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x)
    (hF : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ F y i)) x)
    (v : TangentSpace (model n) x) :
    frameConnectionMatrix n M F x v =
      (frameChangeMatrix n M E F x).transpose * frameConnectionMatrix n M E x v *
        frameChangeMatrix n M E F x +
      (frameChangeMatrix n M E F x).transpose * frameChangeDerivative n M E F x v := by
  let P := frameChangeMatrix n M E F x
  let A := frameConnectionMatrix n M E x v
  let B := frameConnectionMatrix n M F x v
  let D := frameChangeDerivative n M E F x v
  have hd : D = P * B - A * P := frameChangeDerivative_eq n M E F hE hF v
  have hr : A * P + D = P * B := by rw [hd]; abel
  change B = P.transpose * A * P + P.transpose * D
  calc
    B = P.transpose * (P * B) := by
      rw [← Matrix.mul_assoc, frameChangeMatrix_transpose_mul n M E F x, one_mul]
    _ = P.transpose * (A * P + D) := by rw [hr]
    _ = _ := by rw [Matrix.mul_add, ← Matrix.mul_assoc]

/-- The same original curvature transforms tensorially under the actual
orthonormal basis change, with no derivatives of the change matrix. -/
theorem frameCurvatureMatrix_gauge (x : M) (u v : TangentSpace (model n) x) :
    frameCurvatureMatrix n M F x u v =
      (frameChangeMatrix n M E F x).transpose * frameCurvatureMatrix n M E x u v *
        frameChangeMatrix n M E F x := by
  let A := curvatureFramePairing n M x u v
  have h := LinearMap.BilinForm.toMatrix_comp (E x).toBasis (F x).toBasis A
    (LinearMap.id : TangentSpace (model n) x →ₗ[ℝ] TangentSpace (model n) x) LinearMap.id
  have hP : LinearMap.toMatrix (F x).toBasis (E x).toBasis (LinearMap.id) =
      frameChangeMatrix n M E F x := by
    rw [LinearMap.toMatrix_id_eq_basis_toMatrix, frameChangeMatrix_eq_basisMatrix]
    simp only [OrthonormalBasis.coe_toBasis]
  rw [hP] at h
  have hE : LinearMap.BilinForm.toMatrix (E x).toBasis A = frameCurvatureMatrix n M E x u v := by
    ext a b
    simp [A, frameCurvatureMatrix, smoothFrameCurvatureTwoForm_apply,
      LinearMap.BilinForm.toMatrix_apply]
  have hF : LinearMap.BilinForm.toMatrix (F x).toBasis
      (LinearMap.BilinForm.comp A LinearMap.id LinearMap.id) =
      frameCurvatureMatrix n M F x u v := by
    ext a b
    simp [A, frameCurvatureMatrix, smoothFrameCurvatureTwoForm_apply,
      LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.comp_apply]
  rw [hE, hF] at h
  exact h

/-- The genuine differential of a frame-change entry as a one-form. -/
def frameChangeDifferential (a b : Fin (2 * n)) : DifferentialForm.Form (model n) M 1 :=
  fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)
    (mvfderiv (model n) (fun y ↦ frameChangeMatrix n M E F y a b) x)

@[simp] theorem frameChangeDifferential_apply (a b : Fin (2 * n)) (x : M)
    (v : Fin 1 → TangentSpace (model n) x) :
    frameChangeDifferential n M E F a b x v =
      frameChangeDerivative n M E F x (v 0) a b := rfl

/-- Gauge change for actual one-forms, with the scalar entries of `P`
acting on the fibers and `dP` the actual differential of those entries. -/
theorem smoothFrameConnectionOneForm_gauge {x : M}
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x)
    (hF : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ F y i)) x)
    (a b : Fin (2 * n)) :
    smoothFrameConnectionOneForm n M F a b x =
      (∑ i, ∑ j, (frameChangeMatrix n M E F x i a * frameChangeMatrix n M E F x j b) •
        smoothFrameConnectionOneForm n M E i j x) +
      ∑ i, frameChangeMatrix n M E F x i a • frameChangeDifferential n M E F i b x := by
  ext v
  have h := congrArg (fun P : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ ↦ P a b)
    (frameConnectionMatrix_gauge n M E F hE hF (v 0))
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, frameConnectionMatrix,
    smoothFrameCoefficient] at h
  have hv : ![v 0] = v := by
    ext i
    fin_cases i
    rfl
  rw [hv] at h
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, frameChangeDifferential_apply]
  rw [h]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The curvature two-form matrix changes by the homogeneous gauge rule. -/
theorem smoothFrameCurvatureTwoForm_gauge (x : M) (a b : Fin (2 * n)) :
    smoothFrameCurvatureTwoForm n M F a b x =
      ∑ i, ∑ j, (frameChangeMatrix n M E F x i a * frameChangeMatrix n M E F x j b) •
        smoothFrameCurvatureTwoForm n M E i j x := by
  ext v
  have h := congrArg (fun P : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ ↦ P a b)
    (frameCurvatureMatrix_gauge n M E F x (v 0) (v 1))
  have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
  simp only [Matrix.mul_apply, Matrix.transpose_apply, frameCurvatureMatrix, hv] at h
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [h]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Reversing the orthonormal basis change transposes its actual matrix. -/
theorem frameChangeMatrix_reverse (x : M) :
    frameChangeMatrix n M F E x = (frameChangeMatrix n M E F x).transpose := by
  ext a b
  exact real_inner_comm _ _

/-- Component version of `dP = P ΓF - ΓE P`, convenient for differentiating
the actual direction-coordinate identity in the sphere bundle. -/
theorem frameChangeDerivative_component {x : M}
    (hE : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ E y i)) x)
    (hF : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y ↦ F y i)) x)
    (v : TangentSpace (model n) x) (a b : Fin (2 * n)) :
    mvfderiv (model n) (fun y ↦ frameChangeMatrix n M E F y a b) x v =
      (∑ c, frameChangeMatrix n M E F x a c * smoothFrameCoefficient n M F c b x v) -
      ∑ c, smoothFrameCoefficient n M E a c x v * frameChangeMatrix n M E F x c b := by
  have h := congrArg (fun P : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ ↦ P a b)
    (frameChangeDerivative_eq n M E F hE hF v)
  simpa only [frameChangeDerivative, frameConnectionMatrix, Matrix.sub_apply, Matrix.mul_apply] using h

theorem frameCoordinates_change_reverse (x : M) (v : TangentSpace (model n) x) :
    (fun a ↦ inner ℝ (E x a) v) =
      frameChangeMatrix n M E F x *ᵥ (fun a ↦ inner ℝ (F x a) v) := by
  have h := frameCoordinates_change n M F E x v
  rw [frameChangeMatrix_reverse n M E F x, Matrix.transpose_transpose] at h
  exact h

end GaussBonnetChern
