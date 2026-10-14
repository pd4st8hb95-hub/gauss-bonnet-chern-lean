import GaussBonnetChern.ChernFrameGeometry
import GaussBonnetChern.FrameGauge
import GaussBonnetChern.ScalarDifferential
import GaussBonnetChern.ChernAngularAlgebra
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle
open scoped Manifold ContDiff Topology BigOperators Matrix
namespace GaussBonnetChern

private theorem derivative_sum_mul_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type*} [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℝ,E) ∞ P]
    {ι : Type*} [Fintype ι]
    (f g : ι → P → ℝ) (x : P) (w : TangentSpace 𝓘(ℝ,E) x)
    (hf : ∀ i, MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ) (f i) x)
    (hg : ∀ i, MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ) (g i) x) :
    mvfderiv 𝓘(ℝ,E) (fun z ↦ ∑ i, f i z * g i z) x w =
      ∑ i, (f i x * mvfderiv 𝓘(ℝ,E) (g i) x w +
        g i x * mvfderiv 𝓘(ℝ,E) (f i) x w) := by
  classical
  have hs := DifferentialForm.scalarDifferential_sum_at Finset.univ
    (fun i z ↦ f i z * g i z) x (fun i _ ↦ (hf i).mul (hg i))
  have heval := congrArg (fun α ↦ α ![w]) hs
  simp only [ContinuousAlternatingMap.sum_apply,
    DifferentialForm.scalarDifferential_apply, Matrix.cons_val_zero] at heval
  rw [heval]
  apply Finset.sum_congr rfl
  intro i _
  rw [mvfderiv_fun_mul (hf i) (hg i)]
  rfl

/-- Algebra of the homogeneous covariant-direction transformation. This
lemma only eliminates the actual derivative identities supplied separately. -/
theorem direction_change_matrix_algebra {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P A B D : Matrix ι ι ℝ) (u v du dv : ι → ℝ)
    (hu : u = P *ᵥ v) (hdu : du = D *ᵥ v + P *ᵥ dv)
    (hD : D = P * B - A * P) :
    du + A *ᵥ u = P *ᵥ (dv + B *ᵥ v) := by
  rw [hu, hdu, hD, Matrix.sub_mulVec, Matrix.mulVec_add]
  simp only [Matrix.mulVec_mulVec]
  abel

universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]
variable (b c : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x))

theorem frameTangentCurvatureForm_change (v : TangentBundle (model n) M) (i j : Fin (2*n)) :
    frameTangentCurvatureForm n M c i j v =
      ∑ a, ∑ d, (frameChangeMatrix n M b c v.1 a i * frameChangeMatrix n M b c v.1 d j) •
        frameTangentCurvatureForm n M b a d v := by
  ext w
  have h := congrArg (fun α ↦ α (fun k ↦ mfderiv (model n).tangent (model n)
    (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) v (w k)))
    (smoothFrameCurvatureTwoForm_gauge n M b c v.1 i j)
  simpa only [frameTangentCurvatureForm, DifferentialForm.pullback_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply] using h

theorem frameDirectionCoordinate_reverse_change (i : Fin (2*n)) :
    frameDirectionCoordinate n M b i = fun v ↦
      ∑ j, frameChangeMatrix n M b c v.1 i j * frameDirectionCoordinate n M c j v := by
  funext v
  rw [frameDirectionCoordinate_change n M c b i v]
  apply Finset.sum_congr rfl
  intro j _
  change inner ℝ (c v.1 j) (b v.1 i) * _ = inner ℝ (b v.1 i) (c v.1 j) * _
  rw [real_inner_comm (c v.1 j) (b v.1 i)]

/-- Differentiate the actual normalized frame-coordinate relation.
The derivative of the matrix is taken on the base in the projected tangent
direction; all regularity hypotheses are local genuine frame smoothness. -/
theorem frameDirectionCoordinate_derivative_change (v : TangentBundle (model n) M)
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ b x i)) v.1)
    (hc : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ c x i)) v.1)
    (hv : v.2 ≠ 0) (w : TangentSpace (model n).tangent v) :
    (fun i ↦ mvfderiv (model n).tangent (frameDirectionCoordinate n M b i) v w) =
      frameChangeDerivative n M b c v.1
          (mfderiv (model n).tangent (model n)
            (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) v w) *ᵥ
        (fun j ↦ frameDirectionCoordinate n M c j v) +
      frameChangeMatrix n M b c v.1 *ᵥ
        (fun j ↦ mvfderiv (model n).tangent (frameDirectionCoordinate n M c j) v w) := by
  classical
  let πₜ : TangentBundle (model n) M → M := Bundle.TotalSpace.proj
  have hπ : MDifferentiableAt (model n).tangent (model n) πₜ v :=
    (contMDiffAt_proj (n := ∞) (TangentSpace (model n) : M → Type _)).mdifferentiableAt (by simp)
  funext i
  let Pj := fun j (z : TangentBundle (model n) M) ↦ frameChangeMatrix n M b c z.1 i j
  let Uj := frameDirectionCoordinate n M c
  have hPb (j : Fin (2*n)) : MDifferentiableAt (model n) 𝓘(ℝ)
      (fun x ↦ frameChangeMatrix n M b c x i j) v.1 :=
    ((hb i).inner_bundle (hc j)).mdifferentiableAt (by simp)
  have hP (j : Fin (2*n)) : MDifferentiableAt 𝓘(ℝ, Model n × Model n) 𝓘(ℝ) (Pj j) v := by
    rw [modelWithCornersSelf_prod]
    exact (hPb j).comp v hπ
  have hU (j : Fin (2*n)) : MDifferentiableAt 𝓘(ℝ, Model n × Model n) 𝓘(ℝ) (Uj j) v := by
    rw [modelWithCornersSelf_prod]
    exact (contMDiffAt_frameDirectionCoordinate n M c j v hc hv).mdifferentiableAt (by simp)
  have hPderiv (j : Fin (2*n)) : mvfderiv (model n).tangent (Pj j) v w =
      frameChangeDerivative n M b c v.1 (mfderiv (model n).tangent (model n) πₜ v w) i j := by
    unfold frameChangeDerivative
    change mvfderiv (model n).tangent ((fun x ↦ frameChangeMatrix n M b c x i j) ∘ πₜ) v w = _
    unfold mvfderiv
    rw [mfderiv_comp v (hPb j) hπ]
    rfl
  have hs := derivative_sum_mul_at Pj Uj v w hP hU
  have heq : (fun z ↦ ∑ j, Pj j z * Uj j z) = frameDirectionCoordinate n M b i :=
    (frameDirectionCoordinate_reverse_change n M b c i).symm
  rw [heq] at hs
  change mvfderiv 𝓘(ℝ, Model n × Model n) (frameDirectionCoordinate n M b i) v w =
    (∑ j, frameChangeDerivative n M b c v.1 (mfderiv (model n).tangent (model n) πₜ v w) i j * Uj j v) +
      ∑ j, Pj j v * mvfderiv 𝓘(ℝ, Model n × Model n) (Uj j) v w
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hdj : mvfderiv 𝓘(ℝ, Model n × Model n) (Pj j) v w =
      frameChangeDerivative n M b c v.1 (mfderiv (model n).tangent (model n) πₜ v w) i j :=
    hPderiv j
  rw [hdj]
  ring

/-- Covariant direction forms obey the homogeneous frame-change rule,
proved from the actual derivative of the change-of-frame matrix. -/
theorem frameTangentDirectionForm_change (v : TangentBundle (model n) M)
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ b x i)) v.1)
    (hc : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ c x i)) v.1)
    (hv : v.2 ≠ 0) (j : Fin (2*n)) :
    frameTangentDirectionForm n M c j v =
      ∑ i, frameChangeMatrix n M b c v.1 i j • frameTangentDirectionForm n M b i v := by
  classical
  ext W
  let P := frameChangeMatrix n M b c v.1
  let V := mfderiv (model n).tangent (model n)
    (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) v (W 0)
  let A := frameConnectionMatrix n M b v.1 V
  let B := frameConnectionMatrix n M c v.1 V
  let D := frameChangeDerivative n M b c v.1 V
  let ub := fun i ↦ frameDirectionCoordinate n M b i v
  let uc := fun i ↦ frameDirectionCoordinate n M c i v
  let dub := fun i ↦ mvfderiv (model n).tangent (frameDirectionCoordinate n M b i) v (W 0)
  let duc := fun i ↦ mvfderiv (model n).tangent (frameDirectionCoordinate n M c i) v (W 0)
  have hu : ub = P *ᵥ uc := by
    funext i
    exact congrFun (frameDirectionCoordinate_reverse_change n M b c i) v
  have hdu : dub = D *ᵥ uc + P *ᵥ duc :=
    frameDirectionCoordinate_derivative_change n M b c v hb hc hv (W 0)
  have hd : D = P*B-A*P := frameChangeDerivative_eq n M b c hb hc V
  have hθ := direction_change_matrix_algebra P A B D ub uc dub duc hu hdu hd
  have hθb : (fun i ↦ frameTangentDirectionForm n M b i v W) = dub + A *ᵥ ub := by
    funext i
    simp only [frameTangentDirectionForm_apply, Pi.add_apply, Matrix.mulVec, dotProduct,
      dub, A, ub, frameConnectionMatrix]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    change _ * smoothFrameCoefficient n M b i k v.1 V = _
    ring
  have hθc : (fun i ↦ frameTangentDirectionForm n M c i v W) = duc + B *ᵥ uc := by
    funext i
    simp only [frameTangentDirectionForm_apply, Pi.add_apply, Matrix.mulVec, dotProduct,
      duc, B, uc, frameConnectionMatrix]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    change _ * smoothFrameCoefficient n M c i k v.1 V = _
    ring
  have hθrev : (fun i ↦ frameTangentDirectionForm n M b i v W) =
      P *ᵥ (fun i ↦ frameTangentDirectionForm n M c i v W) := by
    rw [hθb, hθc]
    exact hθ
  have hforward : (fun i ↦ frameTangentDirectionForm n M c i v W) =
      P.transpose *ᵥ (fun i ↦ frameTangentDirectionForm n M b i v W) := by
    have horth : P.transpose * P = 1 := frameChangeMatrix_transpose_mul n M b c v.1
    rw [hθrev, Matrix.mulVec_mulVec, horth, Matrix.one_mulVec]
  have hcomponent := congrFun hforward j
  simpa only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, P, smul_eq_mul] using hcomponent

/-- The actual local angular forms obey the determinant covariance law.
Their inputs are the original metric connection, curvature and normalized
tautological vector, and the change of their inputs has been proved above. -/
theorem frameTangentAngularForm_change (v : TangentBundle (model n) M)
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ b x i)) v.1)
    (hc : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ c x i)) v.1)
    (hv : v.2 ≠ 0) :
    frameTangentAngularForm n M c v =
      (frameChangeMatrix n M b c v.1).det • frameTangentAngularForm n M b v := by
  let A := fun z : TangentBundle (model n) M ↦ frameChangeMatrix n M b c z.1
  have hterm (k : Fin n) :
      Chern.angularTerm (E := Model n × Model n) n k (frameDirectionCoordinate n M c) (frameTangentDirectionForm n M c)
        (frameTangentCurvatureForm n M c) v =
      Chern.angularTerm (E := Model n × Model n) n k (Chern.frameChangeFunctions A (frameDirectionCoordinate n M b))
        (Chern.frameChangeOneForms A (frameTangentDirectionForm n M b))
        (Chern.frameChangeTwoForms A (frameTangentCurvatureForm n M b)) v := by
    apply Chern.angularTerm_congr_at
    · intro i
      exact frameDirectionCoordinate_change n M b c i v
    · intro i
      exact frameTangentDirectionForm_change n M b c v hb hc hv i
    · intro i j
      exact frameTangentCurvatureForm_change n M b c v i j
  calc
    _ = Chern.angularForm (E := Model n × Model n) n (Chern.frameChangeFunctions A (frameDirectionCoordinate n M b))
        (Chern.frameChangeOneForms A (frameTangentDirectionForm n M b))
        (Chern.frameChangeTwoForms A (frameTangentCurvatureForm n M b)) v := by
      simp only [frameTangentAngularForm, Chern.angularForm, Finset.sum_apply, Pi.smul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [hterm k]
    _ = _ := Chern.angularForm_frameChange (E := Model n × Model n) n _ _ _ A v

variable [Fact (0<n)]

theorem frameSphereAngularForm_change (v : UnitTangentSphere n M)
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ b x i)) v.1.1)
    (hc : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ c x i)) v.1.1) :
    frameSphereAngularForm n M c v =
      (frameChangeMatrix n M b c v.1.1).det • frameSphereAngularForm n M b v := by
  ext w
  have h := congrArg (fun α ↦ α (fun j ↦ mfderiv (sphereBundleModel n) 𝓘(ℝ,Model n × Model n)
    ((↑) : UnitTangentSphere n M → TangentBundle (model n) M) v (w j)))
    (frameTangentAngularForm_change n M b c v.1 hb hc (UnitTangentSphere.vector_ne_zero n M v))
  simpa only [frameSphereAngularForm_apply, ContinuousAlternatingMap.smul_apply] using h

theorem frameSphereAngularForm_eq_of_orientation (v : UnitTangentSphere n M)
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ b x i)) v.1.1)
    (hc : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ c x i)) v.1.1)
    (hor : (b v.1.1).toBasis.orientation = (c v.1.1).toBasis.orientation) :
    frameSphereAngularForm n M c v = frameSphereAngularForm n M b v := by
  rw [frameSphereAngularForm_change n M b c v hb hc,
    frameChangeMatrix_det_eq_one_of_orientation n M b c v.1.1 hor, one_smul]

end GaussBonnetChern
