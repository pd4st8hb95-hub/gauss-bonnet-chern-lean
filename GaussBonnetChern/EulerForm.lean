import GaussBonnetChern.OrthonormalFrames
import GaussBonnetChern.PfaffianForm

/-! # The actual Euler curvature form and its two determinant laws

The direction slots are alternatized products of the genuine curvature
two-forms. A second alternatization in the frame slots gives the Pfaffian.
Both normalizations are kept explicit and agree with the statement's double
permutation contraction. Frame independence of the scalar is a consequence of
the two determinant factors for orthonormal changes of basis.
-/

noncomputable section
open Bundle Module InnerProductSpace
open scoped Manifold Topology ContDiff BigOperators

namespace GaussBonnetChern

section Algebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def alternatingEvaluationLinear {k : ℕ} (v : Fin k → E) :
    (E [⋀^Fin k]→ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun a := a v
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem alternating_finset_sum_apply {k : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → E [⋀^Fin k]→ₗ[ℝ] ℝ) (v : Fin k → E) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v :=
  map_sum (alternatingEvaluationLinear v) f s

/-- A product of possibly different bilinear pairings. -/
def bilinearFamilyProduct (n : ℕ) (A : Fin n → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    MultilinearMap ℝ (fun _ : Fin (2 * n) ↦ E) ℝ :=
  ((MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compMultilinearMap
    (fun k ↦ pairingMultilinear (A k))).domDomCongr (pairEquiv n)

theorem bilinearFamilyProduct_apply (n : ℕ) (A : Fin n → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (v : Fin (2 * n) → E) :
    bilinearFamilyProduct n A v = ∏ k, A k (v (pairFirst k)) (v (pairSecond k)) := by
  simp [bilinearFamilyProduct, MultilinearMap.domDomCongr_apply,
    MultilinearMap.compMultilinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    pairingMultilinear, Sigma.curry]

def alternatingFamilyForm (n : ℕ) (A : Fin n → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    E [⋀^Fin (2 * n)]→ₗ[ℝ] ℝ :=
  (bilinearFamilyProduct n A).alternatization

theorem alternatingFamilyForm_apply (n : ℕ) (A : Fin n → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (v : Fin (2 * n) → E) :
    alternatingFamilyForm n A v =
      ∑ σ : Equiv.Perm (Fin (2 * n)), (↑(Equiv.Perm.sign σ) : ℝ) *
        ∏ k, A k (v (σ (pairFirst k))) (v (σ (pairSecond k))) := by
  simp [alternatingFamilyForm, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, bilinearFamilyProduct_apply,
    Units.smul_def, zsmul_eq_mul]

/-- Evaluating any actual top alternating form on a new basis introduces
exactly the determinant of the basis change. -/
theorem topAlternatingForm_eval_basis (n : ℕ) (a : E [⋀^Fin (2 * n)]→ₗ[ℝ] ℝ)
    (b c : Basis (Fin (2 * n)) ℝ E) : a c = b.det c * a b := by
  have h := congrArg (fun f : E [⋀^Fin (2 * n)]→ₗ[ℝ] ℝ ↦ f c)
    (a.eq_smul_basis_det b)
  simpa only [AlternatingMap.smul_apply, smul_eq_mul, mul_comm] using h

end Algebra

universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

/-- The genuine curvature, bilinear in its two direction arguments. -/
def curvatureDirectionPairing (x : M) (a b : TangentSpace (model n) x) :
    TangentSpace (model n) x →ₗ[ℝ] TangentSpace (model n) x →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v ↦ inner ℝ (curvature n M x u v b) a
      map_add' := by intros; simp [curvature_add_second, inner_add_left]
      map_smul' := by intros; simp [curvature_smul_second, real_inner_smul_left] }
  map_add' := by intros; ext v; simp [curvature_add_first, inner_add_left]
  map_smul' := by intros; ext v; simp [curvature_smul_first, real_inner_smul_left]

@[simp] theorem curvatureDirectionPairing_apply (x : M) (a b u v : TangentSpace (model n) x) :
    curvatureDirectionPairing n M x a b u v = inner ℝ (curvature n M x u v b) a := rfl

/-- The same genuine curvature, bilinear in the two frame arguments. -/
def curvatureFramePairing (x : M) (u v : TangentSpace (model n) x) :
    TangentSpace (model n) x →ₗ[ℝ] TangentSpace (model n) x →ₗ[ℝ] ℝ where
  toFun a :=
    { toFun := fun b ↦ inner ℝ (curvature n M x u v b) a
      map_add' := by intros; simp [curvature_add_third, inner_add_left]
      map_smul' := by intros; simp [curvature_smul_third, real_inner_smul_left] }
  map_add' := by intros; ext b; simp [inner_add_right]
  map_smul' := by intros; ext b; simp [inner_smul_right]

@[simp] theorem curvatureFramePairing_apply (x : M) (u v a b : TangentSpace (model n) x) :
    curvatureFramePairing n M x u v a b = inner ℝ (curvature n M x u v b) a := rfl

/-- Euler curvature polynomial, alternating in the direction slots. -/
def frameEulerAlternating (x : M) (e : Fin (2 * n) → TangentSpace (model n) x) :
    (TangentSpace (model n) x) [⋀^Fin (2 * n)]→ₗ[ℝ] ℝ :=
  (4 ^ n * (Nat.factorial n : ℝ) * (2 * Real.pi) ^ n)⁻¹ •
    ∑ σ : Equiv.Perm (Fin (2 * n)), (↑(Equiv.Perm.sign σ) : ℝ) •
      alternatingFamilyForm n (fun k ↦ curvatureDirectionPairing n M x
        (e (σ (pairFirst k))) (e (σ (pairSecond k))))

/-- The same polynomial, alternating in the frame slots. -/
def directionEulerAlternating (x : M) (v : Fin (2 * n) → TangentSpace (model n) x) :
    (TangentSpace (model n) x) [⋀^Fin (2 * n)]→ₗ[ℝ] ℝ :=
  (4 ^ n * (Nat.factorial n : ℝ) * (2 * Real.pi) ^ n)⁻¹ •
    ∑ τ : Equiv.Perm (Fin (2 * n)), (↑(Equiv.Perm.sign τ) : ℝ) •
      alternatingFamilyForm n (fun k ↦ curvatureFramePairing n M x
        (v (τ (pairFirst k))) (v (τ (pairSecond k))))

theorem frameEulerAlternating_apply (x : M)
    (e v : Fin (2 * n) → TangentSpace (model n) x) :
    frameEulerAlternating n M x e v =
      eulerScalar n (fun a b i j ↦ inner ℝ (curvature n M x (v i) (v j) (e b)) (e a)) := by
  simp only [frameEulerAlternating, AlternatingMap.smul_apply, alternating_finset_sum_apply,
    smul_eq_mul, alternatingFamilyForm_apply, curvatureDirectionPairing_apply,
    eulerScalar, curvatureContraction]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  simp_rw [Finset.mul_sum, mul_assoc]

theorem frameEulerAlternating_eq_directionEulerAlternating (x : M)
    (e v : Fin (2 * n) → TangentSpace (model n) x) :
    frameEulerAlternating n M x e v = directionEulerAlternating n M x v e := by
  simp only [frameEulerAlternating, directionEulerAlternating,
    AlternatingMap.smul_apply, alternating_finset_sum_apply, smul_eq_mul,
    alternatingFamilyForm_apply, curvatureDirectionPairing_apply,
    curvatureFramePairing_apply]
  apply congrArg (fun z : ℝ ↦ (4 ^ n * (Nat.factorial n : ℝ) * (2 * Real.pi) ^ n)⁻¹ * z)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- The frozen Euler scalar is evaluation of this actual alternating form
on precisely the same orthonormal frame used in the original statement. -/
theorem eulerDensity_eq_frameEulerAlternating (x : M) :
    eulerDensity n M x = frameEulerAlternating n M x (orthonormalFrame n M x)
      (orthonormalFrame n M x) := by
  rw [frameEulerAlternating_apply]
  rfl

/-- Change of frame affects the curvature form by the frame determinant. -/
theorem frameEulerAlternating_change_frame (x : M)
    (b c : Basis (Fin (2 * n)) ℝ (TangentSpace (model n) x))
    (v : Fin (2 * n) → TangentSpace (model n) x) :
    frameEulerAlternating n M x c v = b.det c * frameEulerAlternating n M x b v := by
  rw [frameEulerAlternating_eq_directionEulerAlternating,
    frameEulerAlternating_eq_directionEulerAlternating]
  exact topAlternatingForm_eval_basis n _ b c

/-- Evaluation on a new direction basis introduces the direction determinant. -/
theorem frameEulerAlternating_change_directions (x : M)
    (e : Fin (2 * n) → TangentSpace (model n) x)
    (b c : Basis (Fin (2 * n)) ℝ (TangentSpace (model n) x)) :
    frameEulerAlternating n M x e c = b.det c * frameEulerAlternating n M x e b :=
  topAlternatingForm_eval_basis n _ b c

/-- The double contraction is independent of every orthonormal frame choice,
including orientation-reversing choices, since the two determinants cancel. -/
theorem frameEulerAlternating_orthonormal_independent (x : M)
    (b c : OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x)) :
    frameEulerAlternating n M x c c = frameEulerAlternating n M x b b := by
  have hframe := frameEulerAlternating_change_frame n M x b.toBasis c.toBasis c
  have hdir := frameEulerAlternating_change_directions n M x b b.toBasis c.toBasis
  simp only [OrthonormalBasis.coe_toBasis] at hframe hdir
  rw [hframe, hdir]
  rcases b.det_to_matrix_orthonormalBasis_real c with h | h <;> simp [h]

/-- The actual scalar in the frozen statement can be computed in any
orthonormal basis of the actual tangent metric. -/
theorem eulerDensity_eq_eulerScalar_orthonormalBasis (x : M)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x)) :
    eulerDensity n M x = eulerScalar n
      (fun a c i j ↦ inner ℝ (curvature n M x (b i) (b j) (b c)) (b a)) := by
  rw [eulerDensity_eq_frameEulerAlternating,
    ← frameEulerAlternating_orthonormal_independent n M x (orthonormalFrame n M x) b,
    frameEulerAlternating_apply]

/-- The local formula in a Gram--Schmidt frame agrees with the statement's
possibly discontinuous pointwise choice of an orthonormal frame. -/
theorem eulerDensity_eq_localOrthonormalFrame (p : M) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    eulerDensity n M x = eulerScalar n
      (fun a b i j ↦ inner ℝ (curvature n M x
        (localOrthonormalFrame n M p i x) (localOrthonormalFrame n M p j x)
        (localOrthonormalFrame n M p b x)) (localOrthonormalFrame n M p a x)) := by
  have h := eulerDensity_eq_eulerScalar_orthonormalBasis n M x (localOrthonormalBasis n M p x)
  simpa only [localOrthonormalBasis_apply n M p hx] using h

theorem contMDiffAt_eulerScalar_fields
    {X : Fin (2 * n) → (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (X i)) x) :
    ContMDiffAt (model n) 𝓘(ℝ) ∞
      (fun y ↦ eulerScalar n
        (fun a b i j ↦ inner ℝ (curvature n M y (X i y) (X j y) (X b y)) (X a y))) x := by
  unfold eulerScalar curvatureContraction
  apply ContMDiffAt.div_const
  apply ContMDiffAt.sum
  intro σ _
  apply ContMDiffAt.sum
  intro τ _
  apply ContMDiffAt.mul contMDiffAt_const
  apply ContMDiffAt.prod
  intro k _
  exact (contMDiffAt_curvature_apply n M (hX _) (hX _) (hX _)).inner_bundle (hX _)

/-- The genuine Euler density is smooth. Its definition used a pointwise
choice; frame independence permits replacement by a smooth local frame. -/
theorem contMDiff_eulerDensity : ContMDiff (model n) 𝓘(ℝ) ∞ (eulerDensity n M) := by
  intro x
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have h := contMDiffAt_eulerScalar_fields n M
    (fun i ↦ contMDiffAt_localOrthonormalFrame n M x i hx)
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact eulerDensity_eq_localOrthonormalFrame n M x hy

theorem continuous_frameEulerAlternating (x : M)
    (e : Fin (2 * n) → TangentSpace (model n) x) :
    Continuous (fun v ↦ frameEulerAlternating n M x e v) := by
    simp_rw [frameEulerAlternating_apply]
    unfold eulerScalar curvatureContraction
    apply Continuous.div_const
    apply continuous_finsetSum
    intro σ _
    apply continuous_finsetSum
    intro τ _
    apply Continuous.mul continuous_const
    apply continuous_finsetProd
    intro k _
    have hR : Continuous (fun v : Fin (2 * n) → TangentSpace (model n) x ↦
        curvatureTensor n M x (v (τ (pairFirst k))) (v (τ (pairSecond k)))
          (e (σ (pairSecond k)))) :=
      ((continuous_const.clm_apply (continuous_apply _)).clm_apply
        (continuous_apply _)).clm_apply continuous_const
    simpa only [curvatureTensor_apply] using hR.inner
      (continuous_const (y := e (σ (pairFirst k))))

/-- The frame-relative Pfaffian is an actual continuous alternating top form. -/
def frameEulerForm (x : M) (e : Fin (2 * n) → TangentSpace (model n) x) :
    ContinuousAlternatingMap ℝ (TangentSpace (model n) x) ℝ (Fin (2 * n)) where
  toAlternatingMap := frameEulerAlternating n M x e
  cont := continuous_frameEulerAlternating n M x e

@[simp] theorem frameEulerForm_apply (x : M)
    (e v : Fin (2 * n) → TangentSpace (model n) x) :
    frameEulerForm n M x e v = frameEulerAlternating n M x e v := rfl

theorem frameEulerForm_change_frame (x : M)
    (b c : Basis (Fin (2 * n)) ℝ (TangentSpace (model n) x)) :
    frameEulerForm n M x c = b.det c • frameEulerForm n M x b := by
  ext v
  exact frameEulerAlternating_change_frame n M x b c v

/-- Positively compatible orthonormal frames give the same Euler form. -/
theorem frameEulerForm_eq_of_positive (x : M)
    (b c : OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x))
    (h : 0 < b.toBasis.det c) :
    frameEulerForm n M x c = frameEulerForm n M x b := by
  have hd : b.toBasis.det c = 1 := by
    rcases b.det_to_matrix_orthonormalBasis_real c with hc | hc
    · exact hc
    · linarith
  have heq := frameEulerForm_change_frame n M x b.toBasis c.toBasis
  simpa only [OrthonormalBasis.coe_toBasis, hd, one_smul] using heq

/-- In any orthonormal frame, the Euler form's coefficient is exactly the
frozen Euler curvature density, with all factorial and pi factors retained. -/
theorem frameEulerForm_on_orthonormalBasis (x : M)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x)) :
    frameEulerForm n M x b b = eulerDensity n M x := by
  rw [frameEulerForm_apply, frameEulerAlternating_apply]
  exact (eulerDensity_eq_eulerScalar_orthonormalBasis n M x b).symm

/-- Evaluation of the curvature form on arbitrary smooth tangent fields is
smooth, provided that its frame fields are smooth on the same germ. -/
theorem contMDiffAt_frameEulerForm_fields
    {X Y : Fin (2 * n) → (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (X i)) x)
    (hY : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (Y i)) x) :
    ContMDiffAt (model n) 𝓘(ℝ) ∞
      (fun y ↦ frameEulerForm n M y (fun i ↦ X i y) (fun i ↦ Y i y)) x := by
  simp_rw [frameEulerForm_apply, frameEulerAlternating_apply]
  unfold eulerScalar curvatureContraction
  apply ContMDiffAt.div_const
  apply ContMDiffAt.sum
  intro σ _
  apply ContMDiffAt.sum
  intro τ _
  apply ContMDiffAt.mul contMDiffAt_const
  apply ContMDiffAt.prod
  intro k _
  exact (contMDiffAt_curvature_apply n M (hY _) (hY _) (hX _)).inner_bundle (hX _)

/-- Local smoothness of the true Euler form in the constructed local
orthonormal frame, against arbitrary smooth direction fields. -/
theorem contMDiffAt_localFrameEulerForm_fields (p : M)
    {Y : Fin (2 * n) → (y : M) → TangentSpace (model n) y} {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (hY : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (Y i)) x) :
    ContMDiffAt (model n) 𝓘(ℝ) ∞
      (fun y ↦ frameEulerForm n M y (fun i ↦ localOrthonormalFrame n M p i y)
        (fun i ↦ Y i y)) x :=
  contMDiffAt_frameEulerForm_fields n M
    (fun i ↦ contMDiffAt_localOrthonormalFrame n M p i hx) hY

/-- Exact identification with the volume determinant of an orthonormal
basis. No unspecified scalar or volume functional enters the identity. -/
theorem frameEulerForm_eq_density_mul_det (x : M)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x))
    (v : Fin (2 * n) → TangentSpace (model n) x) :
    frameEulerForm n M x b v = eulerDensity n M x * b.toBasis.det v := by
  have h := congrArg
    (fun a : (TangentSpace (model n) x) [⋀^Fin (2 * n)]→ₗ[ℝ] ℝ ↦ a v)
    ((frameEulerForm n M x b).toAlternatingMap.eq_smul_basis_det b.toBasis)
  change frameEulerForm n M x b v = frameEulerForm n M x b b.toBasis * b.toBasis.det v at h
  simpa only [OrthonormalBasis.coe_toBasis, frameEulerForm_on_orthonormalBasis] using h

end GaussBonnetChern
