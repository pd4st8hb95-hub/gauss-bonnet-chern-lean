import GaussBonnetChern.SphereBundleManifold
import GaussBonnetChern.ChernTransgression
import GaussBonnetChern.SmoothFrameStructure

/-! # Genuine Chern geometry in a specified orthonormal frame

The normalized direction, connection, and curvature are constructed from the
original tangent bundle and its fixed metric. The frame family may be chosen
from a positive atlas chart; its actual local smoothness remains explicit.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle
open scoped Manifold ContDiff Topology BigOperators
namespace GaussBonnetChern
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]
variable (b : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x))

instance tangentBundleChartedSpaceSelf :
    ChartedSpace (Model n × Model n) (TangentBundle (model n) M) :=
  inferInstanceAs (ChartedSpace (ModelProd (Model n) (Model n)) (TangentBundle (model n) M))

instance tangentBundle_isManifold_self :
    IsManifold 𝓘(ℝ, Model n × Model n) ∞ (TangentBundle (model n) M) := by
  simpa only [modelWithCornersSelf_prod] using
    (Bundle.TotalSpace.isManifold (IB := model n) (n := ∞) (F := Model n)
      (E := (TangentSpace (model n) : M → Type _)))

/-- Actual radially normalized vector coordinate in any specified genuine
orthonormal frame family, including the positive atlas frames. -/
def frameDirectionCoordinate (i : Fin (2*n)) (v : TangentBundle (model n) M) : ℝ :=
  ‖v.2‖⁻¹ * inner ℝ (b v.1 i) v.2

theorem contMDiffAt_frameDirectionCoordinate (i : Fin (2*n))
    (v : TangentBundle (model n) M)
    (hb : ∀ j, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ b x j)) v.1)
    (hv : v.2 ≠ 0) :
    ContMDiffAt (model n).tangent 𝓘(ℝ) ∞ (frameDirectionCoordinate n M b i) v := by
  have hinner := ((hb i).comp v (contMDiffAt_proj (TangentSpace (model n) : M → Type _))).inner_bundle
    (contMDiffAt_id : ContMDiffAt (model n).tangent (model n).tangent ∞
      (id : TangentBundle (model n) M → _) v)
  exact ((contMDiffAt_tangentNorm n M v hv).inv₀ (norm_ne_zero_iff.mpr hv)).mul hinner

theorem sum_sq_frameDirectionCoordinate (v : TangentBundle (model n) M) (hv : v.2 ≠ 0) :
    ∑ i, frameDirectionCoordinate n M b i v ^ 2 = 1 := by
  have hi : (∑ i, inner ℝ (b v.1 i) v.2 ^ 2) = ‖v.2‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (b v.1).sum_sq_norm_inner_right v.2
  simp only [frameDirectionCoordinate, mul_pow, ← Finset.mul_sum]
  rw [hi]
  field_simp

theorem frameDirection_differential_orthogonal (v : TangentBundle (model n) M)
    (hb : ∀ j, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ b x j)) v.1)
    (hv : v.2 ≠ 0) (w : TangentSpace (model n).tangent v) :
    ∑ i, frameDirectionCoordinate n M b i v *
      mvfderiv (model n).tangent (frameDirectionCoordinate n M b i) v w = 0 := by
  let U := frameDirectionCoordinate n M b
  have hU (i : Fin (2*n)) : MDifferentiableAt (model n).tangent 𝓘(ℝ) (U i) v :=
    (contMDiffAt_frameDirectionCoordinate n M b i v hb hv).mdifferentiableAt (by simp)
  have hzero : ∀ᶠ q : TangentBundle (model n) M in 𝓝 v, q.2 ≠ 0 :=
    (isOpen_nonzeroTangentBundle n M).mem_nhds hv
  have heq : (fun q ↦ ∑ i, U i q * U i q) =ᶠ[𝓝 v] (fun _ ↦ (1:ℝ)) := by
    filter_upwards [hzero] with q hq
    simpa only [U, ← pow_two] using sum_sq_frameDirectionCoordinate n M b q hq
  have hderivZero : mvfderiv (model n).tangent (fun q ↦ ∑ i, U i q * U i q) v = 0 := by
    calc
      _ = mvfderiv (model n).tangent (fun _ : TangentBundle (model n) M ↦ (1:ℝ)) v :=
        heq.mfderiv_eq
      _ = 0 := mvfderiv_const _
  have hsum : mvfderiv (model n).tangent (fun q ↦ ∑ i, U i q * U i q) v =
      ∑ i, mvfderiv (model n).tangent (fun q ↦ U i q * U i q) v := by
    have h := (HasMFDerivAt.sum (t := Finset.univ)
      (fun i _ ↦ ((hU i).mul (hU i)).hasMFDerivAt)).mfderiv
    have hfun : (fun q ↦ ∑ i, U i q * U i q) = (∑ i, U i * U i) := by
      funext q
      simp
    rw [hfun]
    ext z
    simp only [ContinuousLinearMap.sum_apply]
    change mfderiv (model n).tangent 𝓘(ℝ) (∑ i, U i * U i) v z =
      ∑ i, mfderiv (model n).tangent 𝓘(ℝ) (U i * U i) v z
    rw [h]
    simp only [ContinuousLinearMap.sum_apply]
    rfl
  have hsumw := congrArg (fun L ↦ L w) hsum
  rw [hderivZero] at hsumw
  simp only [zero_apply, ContinuousLinearMap.sum_apply,
    mvfderiv_fun_mul (hU _) (hU _), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hsumw
  have hdouble : (2:ℝ) * (∑ i, U i v * mvfderiv (model n).tangent (U i) v w) = 0 := by
    rw [Finset.mul_sum]
    convert hsumw.symm using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  change ∑ i, U i v * mvfderiv (model n).tangent (U i) v w = 0
  linarith

def frameTangentConnectionForm (i j : Fin (2*n)) :
    DifferentialForm.Form (model n).tangent (TangentBundle (model n) M) 1 :=
  DifferentialForm.pullback (I := (model n).tangent)
    (Bundle.TotalSpace.proj : TangentBundle (model n) M → M)
    (smoothFrameConnectionOneForm n M b i j)

def frameTangentCurvatureForm (i j : Fin (2*n)) :
    DifferentialForm.Form (model n).tangent (TangentBundle (model n) M) 2 :=
  DifferentialForm.pullback (I := (model n).tangent)
    (Bundle.TotalSpace.proj : TangentBundle (model n) M → M)
    (smoothFrameCurvatureTwoForm n M b i j)

def frameTangentDirectionForm (i : Fin (2*n)) :
    DifferentialForm.Form (model n).tangent (TangentBundle (model n) M) 1 :=
  (fun v ↦ ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0:Fin 1)
    (mvfderiv (model n).tangent (frameDirectionCoordinate n M b i) v)) +
      ∑ j, fun v ↦ frameDirectionCoordinate n M b j v • frameTangentConnectionForm n M b i j v

@[simp] theorem frameTangentDirectionForm_apply (i : Fin (2*n))
    (v : TangentBundle (model n) M) (w : Fin 1 → TangentSpace (model n).tangent v) :
    frameTangentDirectionForm n M b i v w =
      mvfderiv (model n).tangent (frameDirectionCoordinate n M b i) v (w 0) +
        ∑ j, frameDirectionCoordinate n M b j v * frameTangentConnectionForm n M b i j v w := by
  simp [frameTangentDirectionForm, ContinuousAlternatingMap.ofSubsingleton_apply_apply, smul_eq_mul]

theorem frameTangentConnectionForm_skew (i j : Fin (2*n))
    (v : TangentBundle (model n) M)
    (hb : ∀ k, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ b x k)) v.1) :
    frameTangentConnectionForm n M b i j v = -frameTangentConnectionForm n M b j i v := by
  ext w
  simp only [frameTangentConnectionForm, DifferentialForm.pullback_apply,
    ContinuousAlternatingMap.neg_apply]
  exact congrArg (fun α ↦ α (fun k ↦ mfderiv (model n).tangent (model n)
    (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) v (w k)))
    (smoothFrameConnectionOneForm_skew n M b i j hb)

private theorem real_weighted_skew_sum_zero {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (A : ι → ι → ℝ) (hA : ∀ i j, A i j = -A j i) :
    ∑ i, ∑ j, u i * u j * A i j = 0 := by
  have hs : (∑ i, ∑ j, u i * u j * A i j) = -(∑ i, ∑ j, u i * u j * A i j) := by
    nth_rw 1 [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA j i]
    ring
  linarith

theorem frameTangentDirectionForm_orthogonal (v : TangentBundle (model n) M)
    (hb : ∀ k, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ b x k)) v.1)
    (hv : v.2 ≠ 0) :
    (∑ i, frameDirectionCoordinate n M b i v • frameTangentDirectionForm n M b i v) = 0 := by
  ext w
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    frameTangentDirectionForm_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  rw [frameDirection_differential_orthogonal n M b v hb hv (w 0), zero_add]
  simp only [Finset.mul_sum, ← mul_assoc]
  apply real_weighted_skew_sum_zero
  intro i j
  exact congrArg (fun α ↦ α w) (frameTangentConnectionForm_skew n M b i j v hb)

/-- The actual normalized coordinates obey the expected transpose law
under an arbitrary orthonormal frame change, pointwise and in all dimensions. -/
theorem frameDirectionCoordinate_change
    (c : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x))
    (j : Fin (2*n)) (v : TangentBundle (model n) M) :
    frameDirectionCoordinate n M c j v =
      ∑ i, inner ℝ (b v.1 i) (c v.1 j) * frameDirectionCoordinate n M b i v := by
  unfold frameDirectionCoordinate
  rw [← (b v.1).sum_inner_mul_inner (c v.1 j) v.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (c v.1 j) (b v.1 i)]
  ring

/-- The genuine open part of the punctured tangent bundle over a local
frame domain. It carries the inherited manifold structure. -/
def frameNonzeroDomain (s : TopologicalSpace.Opens M) :
    TopologicalSpace.Opens (TangentBundle (model n) M) :=
  ⟨{v | v.1 ∈ s ∧ v.2 ≠ 0},
    (s.isOpen.preimage (FiberBundle.continuous_proj (Model n)
      (TangentSpace (model n) : M → Type _))).inter (isOpen_nonzeroTangentBundle n M)⟩

def framePatchDirectionCoordinate (s : TopologicalSpace.Opens M) (i : Fin (2*n)) :
    frameNonzeroDomain n M s → ℝ :=
  fun v ↦ frameDirectionCoordinate n M b i v.1

/-- Actual normalized direction coordinates are globally smooth on the
actual open patch. No global smooth extension of the frame is assumed. -/
theorem contMDiff_framePatchDirectionCoordinate (s : TopologicalSpace.Opens M)
    (hb : ∀ j, ContMDiffOn (model n) (model n).tangent ∞ (T% (fun x ↦ b x j)) s)
    (i : Fin (2*n)) :
    ContMDiff (model n).tangent 𝓘(ℝ) ∞ (framePatchDirectionCoordinate n M b s i) := by
  intro v
  have hbase : ∀ j, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun x ↦ b x j)) v.1.1 :=
    fun j ↦ (hb j).contMDiffAt (s.isOpen.mem_nhds v.2.1)
  exact (contMDiffAt_frameDirectionCoordinate n M b i v.1 hbase v.2.2).comp v
    (contMDiff_subtype_val (I := (model n).tangent) (U := frameNonzeroDomain n M s)).contMDiffAt

/-- The actual local angular polynomial on the tangent bundle, assembled
only after differentiating the specified genuine frame family. It is smooth
on that frame's domain away from the zero section; that regularity is a theorem
to be proved, not a field of this definition. -/
def frameTangentAngularForm :
    DifferentialForm.Form 𝓘(ℝ, Model n × Model n) (TangentBundle (model n) M) (2*n-1) :=
  Chern.angularForm n (frameDirectionCoordinate n M b) (frameTangentDirectionForm n M b)
    (frameTangentCurvatureForm n M b)

section Sphere
variable [Fact (0<n)]

/-- Restrict the genuine local angular form to the genuine sphere bundle
using its already proved smooth inclusion. -/
def frameSphereAngularForm :
    DifferentialForm.Form (sphereBundleModel n) (UnitTangentSphere n M) (2*n-1) :=
  DifferentialForm.pullback (I := sphereBundleModel n)
    ((↑) : UnitTangentSphere n M → TangentBundle (model n) M) (frameTangentAngularForm n M b)

@[simp] theorem frameSphereAngularForm_apply (v : UnitTangentSphere n M)
    (w : Fin (2*n-1) → TangentSpace (sphereBundleModel n) v) :
    frameSphereAngularForm n M b v w = frameTangentAngularForm n M b v.1
      (fun j ↦ mfderiv (sphereBundleModel n) 𝓘(ℝ, Model n × Model n)
        ((↑) : UnitTangentSphere n M → TangentBundle (model n) M) v (w j)) := rfl

end Sphere

end GaussBonnetChern
