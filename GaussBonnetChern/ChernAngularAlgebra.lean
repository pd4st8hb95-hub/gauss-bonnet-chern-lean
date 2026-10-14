import GaussBonnetChern.ChernTransgression
import GaussBonnetChern.ExteriorAssociativity
import GaussBonnetChern.PfaffianForm

/-! # Multilinear algebra of the genuine Chern angular polynomial

All products below use the existing normalized exterior product. This file
develops algebraic frame-change and recurrence identities separately from the
geometric proof of the connection and unit-sphere identities.
-/

noncomputable section
open scoped Manifold BigOperators
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section FormLinearAlgebra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

/-- Degree transport as an actual linear map on the form module. -/
def formCastLinear {r s : ℕ} (h : r = s) :
    Form 𝓘(ℝ,E) P r →ₗ[ℝ] Form 𝓘(ℝ,E) P s := by
  subst s
  exact LinearMap.id

@[simp] theorem formCastLinear_apply {r s : ℕ} (h : r = s)
    (α : Form 𝓘(ℝ,E) P r) : formCastLinear h α = degreeCastForm h α := by
  subst s
  rfl

/-- Exterior multiplication is bilinear on genuine manifold forms. -/
def wedgeLinear (r s : ℕ) : Form 𝓘(ℝ,E) P r →ₗ[ℝ]
    Form 𝓘(ℝ,E) P s →ₗ[ℝ] Form 𝓘(ℝ,E) P (r+s) :=
  LinearMap.mk₂ ℝ wedge
    (by intro a b c; funext x; ext v; simp [wedge, wedgeFiber_apply_realSign,
      add_mul, mul_add, Finset.sum_add_distrib])
    (by intro t a b; funext x; ext v; simp [wedge, wedgeFiber_apply_realSign,
      mul_assoc, mul_left_comm, ← Finset.mul_sum])
    (by intro a b c; funext x; ext v; simp [wedge, wedgeFiber_apply_realSign,
      add_mul, mul_add, Finset.sum_add_distrib])
    (by intro t a b; funext x; ext v; simp [wedge, wedgeFiber_apply_realSign,
      mul_assoc, mul_left_comm, ← Finset.mul_sum])

@[simp] theorem wedgeLinear_apply {r s : ℕ}
    (α : Form 𝓘(ℝ,E) P r) (β : Form 𝓘(ℝ,E) P s) :
    wedgeLinear r s α β = wedge α β := rfl

/-- Multiplication of a scalar function and a form, as a bilinear map. -/
def functionSmulLinear (r : ℕ) : (P → ℝ) →ₗ[ℝ]
    Form 𝓘(ℝ,E) P r →ₗ[ℝ] Form 𝓘(ℝ,E) P r :=
  LinearMap.mk₂ ℝ (fun f α x ↦ f x • α x)
    (by intros; funext x; simp [add_smul])
    (by intros; funext x; simp [smul_smul])
    (by intros; funext x; simp [smul_add])
    (by intros; funext x; simp [smul_smul, mul_comm])

end FormLinearAlgebra

section MultilinearBlocks
variable {W A B C : Type*} [AddCommGroup W] [Module ℝ W]
  [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
  [AddCommGroup C] [Module ℝ C]

/-- Compose two genuine multilinear blocks with a bilinear operation. -/
def multilinearBlock {r s : ℕ} (L : A →ₗ[ℝ] B →ₗ[ℝ] C)
    (a : MultilinearMap ℝ (fun _ : Fin r ↦ W) A)
    (b : MultilinearMap ℝ (fun _ : Fin s ↦ W) B) :
    MultilinearMap ℝ (fun _ : Fin (r+s) ↦ W) C :=
  (TensorProduct.lift L).compMultilinearMap ((a.domCoprod b).domDomCongr finSumFinEquiv)

@[simp] theorem multilinearBlock_apply {r s : ℕ} (L : A →ₗ[ℝ] B →ₗ[ℝ] C)
    (a : MultilinearMap ℝ (fun _ : Fin r ↦ W) A)
    (b : MultilinearMap ℝ (fun _ : Fin s ↦ W) B) (w : Fin (r+s) → W) :
    multilinearBlock L a b w =
      L (a (fun i ↦ w (Fin.castAdd s i))) (b (fun i ↦ w (Fin.natAdd r i))) := by
  simp [multilinearBlock, Function.comp_def]

/-- An arbitrary bilinear map as a two-variable multilinear map. -/
def bilinearAsMultilinear (L : W →ₗ[ℝ] W →ₗ[ℝ] A) :
    MultilinearMap ℝ (fun _ : Fin 2 ↦ W) A where
  toFun w := L (w 0) (w 1)
  map_update_add' := by intro _ w i x y; fin_cases i <;> simp
  map_update_smul' := by intro _ w i t x; fin_cases i <;> simp

end MultilinearBlocks

section Products
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The actual ordered one-form product is multilinear in its frame vectors. -/
def oneFormProductMultilinear (θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1) :
    (r : ℕ) → MultilinearMap ℝ (fun _ : Fin r ↦ W) (Form 𝓘(ℝ,E) P r)
  | 0 => MultilinearMap.constOfIsEmpty ℝ _ (ofFunction (fun _ ↦ 1))
  | r+1 => multilinearBlock (wedgeLinear r 1) (oneFormProductMultilinear θ r)
      (MultilinearMap.ofSubsingleton ℝ W _ (0 : Fin 1) θ)

theorem oneFormProductMultilinear_apply (θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (r : ℕ) (w : Fin r → W) :
    oneFormProductMultilinear θ r w = oneFormProduct r (fun i ↦ θ (w i)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [oneFormProductMultilinear, multilinearBlock_apply,
      MultilinearMap.ofSubsingleton, wedgeLinear_apply, oneFormProduct, ih]
    congr 1

/-- The actual ordered two-form product is multilinear in its paired frame vectors. -/
def twoFormProductMultilinear (Ω : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) :
    (k : ℕ) → MultilinearMap ℝ (fun _ : Fin (2*k) ↦ W) (Form 𝓘(ℝ,E) P (2*k))
  | 0 => by
      letI : IsEmpty (Fin (2*0)) := ⟨fun i ↦ by have := i.isLt; omega⟩
      exact MultilinearMap.constOfIsEmpty ℝ _ (ofFunction (fun _ ↦ 1))
  | k+1 => (formCastLinear (show 2*k+2 = 2*(k+1) by omega)).compMultilinearMap
      ((multilinearBlock (wedgeLinear (2*k) 2) (twoFormProductMultilinear Ω k)
        (bilinearAsMultilinear Ω)).domDomCongr (finCongr (by omega)))

theorem twoFormProductMultilinear_apply (Ω : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (k : ℕ) (w : Fin (2*k) → W) :
    twoFormProductMultilinear Ω k w =
      twoFormProduct k (fun j ↦ Ω (w (pairFirst j)) (w (pairSecond j))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [twoFormProductMultilinear, LinearMap.compMultilinearMap_apply,
      MultilinearMap.domDomCongr_apply, multilinearBlock_apply, formCastLinear_apply,
      wedgeLinear_apply, twoFormProduct, ih]
    congr 2

end Products
section AngularPolynomial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The unalternated Chern polynomial, genuinely multilinear in all frame slots. -/
def angularMultilinear (n : ℕ) (k : Fin n)
    (U : W →ₗ[ℝ] (P → ℝ)) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) :
    MultilinearMap ℝ (fun _ : Fin (2*n) ↦ W) (Form 𝓘(ℝ,E) P (2*n-1)) :=
  (formCastLinear (show (2*n-2*k.val-1)+2*k.val = 2*n-1 by
    have := k.isLt; omega)).compMultilinearMap
    ((multilinearBlock (functionSmulLinear _)
      (MultilinearMap.ofSubsingleton ℝ W _ (0 : Fin 1) U)
      (multilinearBlock (wedgeLinear _ _)
        (oneFormProductMultilinear Θ (2*n-2*k.val-1))
        (twoFormProductMultilinear B k.val))).domDomCongr
          (finCongr (show 1+((2*n-2*k.val-1)+2*k.val) = 2*n by have := k.isLt; omega)))

theorem angularMultilinear_apply (n : ℕ) (k : Fin n)
    (U : W →ₗ[ℝ] (P → ℝ)) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) (w : Fin (2*n) → W) :
    angularMultilinear n k U Θ B w = fun x ↦ U (w ⟨0, by have := k.isLt; omega⟩) x •
      degreeCastForm (show (2*n-2*k.val-1)+2*k.val = 2*n-1 by have := k.isLt; omega)
        (wedge (oneFormProduct (2*n-2*k.val-1) (fun i ↦ Θ (w (directionIndex k i))))
          (twoFormProduct k.val (fun j ↦ B (w (curvatureIndexFirst k j))
            (w (curvatureIndexSecond k j))))) x := by
  simp only [angularMultilinear, LinearMap.compMultilinearMap_apply,
    MultilinearMap.domDomCongr_apply, multilinearBlock_apply,
    MultilinearMap.ofSubsingleton, wedgeLinear_apply,
    oneFormProductMultilinear_apply, twoFormProductMultilinear_apply, formCastLinear_apply]
  have hdir (i : Fin (2*n-2*k.val-1)) :
      (finCongr (show 1+((2*n-2*k.val-1)+2*k.val) = 2*n by have := k.isLt; omega))
        (Fin.natAdd 1 (Fin.castAdd (2*k.val) i)) = directionIndex k i := by
    apply Fin.ext
    simp [directionIndex]
    omega
  have hfirst (j : Fin k.val) :
      (finCongr (show 1+((2*n-2*k.val-1)+2*k.val) = 2*n by have := k.isLt; omega))
        (Fin.natAdd 1 (Fin.natAdd (2*n-2*k.val-1) (pairFirst j))) =
          curvatureIndexFirst k j := by
    apply Fin.ext
    simp [curvatureIndexFirst, pairFirst]
    have := k.isLt
    omega
  have hsecond (j : Fin k.val) :
      (finCongr (show 1+((2*n-2*k.val-1)+2*k.val) = 2*n by have := k.isLt; omega))
        (Fin.natAdd 1 (Fin.natAdd (2*n-2*k.val-1) (pairSecond j))) =
          curvatureIndexSecond k j := by
    apply Fin.ext
    simp [curvatureIndexSecond, pairSecond]
    have := k.isLt
    omega
  simp_rw [hdir, hfirst, hsecond]
  funext x
  ext v
  simp only [degreeCastForm_apply_intrinsic, functionSmulLinear, LinearMap.mk₂_apply,
    ContinuousAlternatingMap.smul_apply]
  rfl
/-- Alternation in the frame slots gives exactly the existing `angularTerm`. -/
theorem angularMultilinear_alternatization (n : ℕ) (k : Fin n)
    (U : W →ₗ[ℝ] (P → ℝ)) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) (w : Fin (2*n) → W) :
    (angularMultilinear n k U Θ B).alternatization w =
      angularTerm n k (fun i ↦ U (w i)) (fun i ↦ Θ (w i))
        (fun i j ↦ B (w i) (w j)) := by
  rw [MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply, angularMultilinear_apply,
    Function.comp_def, angularTerm, Units.smul_def]
  apply Finset.sum_congr rfl
  intro σ _
  funext x
  ext v
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, zsmul_eq_mul,
    Int.cast_smul_eq_zsmul]

/-- Evaluation of a form at a point and a tuple, as a linear map. -/
def formEvaluationLinear {r : ℕ} (x : P) (v : Fin r → TangentSpace 𝓘(ℝ,E) x) :
    Form 𝓘(ℝ,E) P r →ₗ[ℝ] ℝ where
  toFun α := α x v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The top-degree determinant law also holds for form-valued alternating maps. -/
theorem alternatingForm_congruence {d r : ℕ}
    (A : W [⋀^Fin d]→ₗ[ℝ] Form 𝓘(ℝ,E) P r)
    (b : Basis (Fin d) ℝ W) (T : W →ₗ[ℝ] W) :
    A (fun i ↦ T (b i)) = LinearMap.det T • A b := by
  funext x
  ext v
  let a := (formEvaluationLinear x v).compAlternatingMap A
  have h := congrArg (fun f : W [⋀^Fin d]→ₗ[ℝ] ℝ ↦ f (fun i ↦ T (b i)))
    (a.eq_smul_basis_det b)
  have hb : b.det (fun i ↦ T (b i)) = LinearMap.det T := by
    change b.det (T ∘ b) = LinearMap.det T
    rw [Basis.det_comp, Basis.det_self, mul_one]
  simpa only [AlternatingMap.smul_apply, smul_eq_mul, hb, mul_comm,
    a, LinearMap.compAlternatingMap_apply, formEvaluationLinear, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.smul_apply, ContinuousAlternatingMap.smul_apply] using h

/-- Full determinant covariance of the actual Chern polynomial in every even
dimension. No invertibility, orthogonality, or smoothness assumption is needed. -/
theorem angularTerm_frame_congruence (n : ℕ) (k : Fin n)
    (U : W →ₗ[ℝ] (P → ℝ)) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (b : Basis (Fin (2*n)) ℝ W) (T : W →ₗ[ℝ] W) :
    angularTerm n k (fun i ↦ U (T (b i))) (fun i ↦ Θ (T (b i)))
      (fun i j ↦ B (T (b i)) (T (b j))) =
      LinearMap.det T • angularTerm n k (fun i ↦ U (b i)) (fun i ↦ Θ (b i))
        (fun i j ↦ B (b i) (b j)) := by
  rw [← angularMultilinear_alternatization, ← angularMultilinear_alternatization]
  exact alternatingForm_congruence _ b T

end AngularPolynomial

section MatrixFrameChange
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

/-- Constant-matrix change of every frame slot of the actual angular term.
The matrix convention is `e'_i = Σ_j A_{ji} e_j`. -/
theorem angularTerm_matrix_congruence (n : ℕ) (k : Fin n)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (Ω : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (A : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) :
    angularTerm n k (fun i ↦ ∑ j, A j i • u j) (fun i ↦ ∑ j, A j i • θ j)
      (fun i j ↦ ∑ a, ∑ b, (A a i * A b j) • Ω a b) =
      A.det • angularTerm n k u θ Ω := by
  let b := Pi.basisFun ℝ (Fin (2*n))
  let U := b.constr ℝ u
  let Θ := b.constr ℝ θ
  let B := b.constr ℝ (fun i ↦ b.constr ℝ (Ω i))
  let T := Matrix.toLin' A
  have hu (i : Fin (2*n)) : U (T (b i)) = ∑ j, A j i • u j := by
    simp [U, T, b, Basis.constr_apply_fintype, Matrix.toLin'_apply]
  have hθ (i : Fin (2*n)) : Θ (T (b i)) = ∑ j, A j i • θ j := by
    simp [Θ, T, b, Basis.constr_apply_fintype, Matrix.toLin'_apply]
  have hB (i j : Fin (2*n)) : B (T (b i)) (T (b j)) =
      ∑ a, ∑ b, (A a i * A b j) • Ω a b := by
    simp [B, T, b, Basis.constr_apply_fintype, Matrix.toLin'_apply,
      Finset.smul_sum, smul_smul]
  have h := angularTerm_frame_congruence n k U Θ B b T
  simp only [hu, hθ, hB] at h
  simpa [U, Θ, B, T, LinearMap.det_toMatrix b] using h

/-- The weighted angular form transforms by the same determinant. -/
theorem angularForm_matrix_congruence (n : ℕ)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (Ω : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (A : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) :
    angularForm n (fun i ↦ ∑ j, A j i • u j) (fun i ↦ ∑ j, A j i • θ j)
      (fun i j ↦ ∑ a, ∑ b, (A a i * A b j) • Ω a b) =
      A.det • angularForm n u θ Ω := by
  simp only [angularForm, angularTerm_matrix_congruence, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact smul_comm _ _ _

end MatrixFrameChange

section PointwiseFrameChange
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

theorem oneFormProduct_congr_at (r : ℕ)
    {θ θ' : Fin r → Form 𝓘(ℝ,E) P 1} (x : P) (h : ∀ i, θ i x = θ' i x) :
    oneFormProduct r θ x = oneFormProduct r θ' x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change wedgeFiber (oneFormProduct r (fun i ↦ θ i.castSucc) x) (θ (Fin.last r) x) =
      wedgeFiber (oneFormProduct r (fun i ↦ θ' i.castSucc) x) (θ' (Fin.last r) x)
    rw [ih (fun i ↦ h i.castSucc), h (Fin.last r)]

theorem twoFormProduct_congr_at (r : ℕ)
    {Ω Ω' : Fin r → Form 𝓘(ℝ,E) P 2} (x : P) (h : ∀ i, Ω i x = Ω' i x) :
    twoFormProduct r Ω x = twoFormProduct r Ω' x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    ext v
    simp only [twoFormProduct, degreeCastForm_apply_intrinsic, wedge]
    rw [ih (fun i ↦ h i.castSucc), h (Fin.last r)]

/-- Chern's polynomial at a point depends only on the actual form fibers there. -/
theorem angularTerm_congr_at (n : ℕ) (k : Fin n) (x : P)
    {u u' : Fin (2*n) → P → ℝ} {θ θ' : Fin (2*n) → Form 𝓘(ℝ,E) P 1}
    {Ω Ω' : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2}
    (hu : ∀ i, u i x = u' i x) (hθ : ∀ i, θ i x = θ' i x)
    (hΩ : ∀ i j, Ω i j x = Ω' i j x) :
    angularTerm n k u θ Ω x = angularTerm n k u' θ' Ω' x := by
  ext v
  simp only [angularTerm, Finset.sum_apply, Pi.smul_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    degreeCastForm_apply_intrinsic, wedge]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hu, oneFormProduct_congr_at _ x (fun i ↦ hθ _),
    twoFormProduct_congr_at _ x (fun j ↦ hΩ _ _)]

/-- A point-dependent change-of-frame matrix acts on scalar components. -/
def frameChangeFunctions {d : ℕ} (A : P → Matrix (Fin d) (Fin d) ℝ)
    (u : Fin d → P → ℝ) : Fin d → P → ℝ :=
  fun i x ↦ ∑ j, A x j i * u j x

/-- The same point-dependent frame matrix acts on one-form components. -/
def frameChangeOneForms {d : ℕ} (A : P → Matrix (Fin d) (Fin d) ℝ)
    (θ : Fin d → Form 𝓘(ℝ,E) P 1) : Fin d → Form 𝓘(ℝ,E) P 1 :=
  fun i x ↦ ∑ j, A x j i • θ j x

/-- Both frame indices of the curvature two-form transform covariantly. -/
def frameChangeTwoForms {d : ℕ} (A : P → Matrix (Fin d) (Fin d) ℝ)
    (Ω : Fin d → Fin d → Form 𝓘(ℝ,E) P 2) :
    Fin d → Fin d → Form 𝓘(ℝ,E) P 2 :=
  fun i j x ↦ ∑ a, ∑ b, (A x a i * A x b j) • Ω a b x

/-- Full pointwise frame covariance, including matrices varying on the domain. -/
theorem angularTerm_frameChange (n : ℕ) (k : Fin n)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (Ω : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (A : P → Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (x : P) :
    angularTerm n k (frameChangeFunctions A u) (frameChangeOneForms A θ)
      (frameChangeTwoForms A Ω) x = (A x).det • angularTerm n k u θ Ω x := by
  calc
    _ = angularTerm n k (fun i ↦ ∑ j, A x j i • u j)
        (fun i ↦ ∑ j, A x j i • θ j)
        (fun i j ↦ ∑ a, ∑ b, (A x a i * A x b j) • Ω a b) x := by
      apply angularTerm_congr_at n k x
      · intro i; simp [frameChangeFunctions]
      · intro i; simp [frameChangeOneForms]
      · intro i j; simp [frameChangeTwoForms]
    _ = _ := congrFun (angularTerm_matrix_congruence n k u θ Ω (A x)) x

theorem angularForm_frameChange (n : ℕ)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (Ω : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (A : P → Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (x : P) :
    angularForm n (frameChangeFunctions A u) (frameChangeOneForms A θ)
      (frameChangeTwoForms A Ω) x = (A x).det • angularForm n u θ Ω x := by
  simp only [angularForm, Finset.sum_apply, Pi.smul_apply,
    angularTerm_frameChange, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact smul_comm _ _ _

/-- Positive orthonormal frame changes (determinant one) preserve the actual angular form. -/
theorem angularForm_frameChange_det_one (n : ℕ)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (Ω : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (A : P → Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (x : P) (hA : (A x).det = 1) :
    angularForm n (frameChangeFunctions A u) (frameChangeOneForms A θ)
      (frameChangeTwoForms A Ω) x = angularForm n u θ Ω x := by
  rw [angularForm_frameChange, hA, one_smul]

end PointwiseFrameChange

end GaussBonnetChern.Chern



