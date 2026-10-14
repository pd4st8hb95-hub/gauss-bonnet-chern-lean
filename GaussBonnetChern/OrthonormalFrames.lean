import GaussBonnetChern.CovariantCurvature
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Genuine local smooth orthonormal frames

Gram--Schmidt is performed in each tangent fiber using the registered metric.
Linear independence of the input guarantees that every normalization denominator
is nonzero. Smoothness is proved from the recursive formula, rather than imposed
on a pointwise choice of orthonormal bases.
-/

noncomputable section

open Bundle Filter InnerProductSpace Module
open scoped Manifold Topology ContDiff BigOperators

namespace GaussBonnetChern

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

/-- The norm of a nonvanishing smooth tangent section is smooth. -/
theorem contMDiffAt_norm_tangent
    {X : (x : M) → TangentSpace (model n) x} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hx : X x ≠ 0) :
    ContMDiffAt (model n) 𝓘(ℝ) ∞ (fun y ↦ ‖X y‖) x := by
  have h := (Real.contDiffAt_sqrt (by simpa using hx : inner ℝ (X x) (X x) ≠ 0)).comp_contMDiffAt
    (f := fun y : M ↦ inner ℝ (X y) (X y))
    (hX.inner_bundle hX)
  simpa only [Function.comp_def, ← norm_eq_sqrt_real_inner] using h

/-- Fiberwise Gram--Schmidt preserves the smooth germ of a finite family of
linearly independent tangent sections. -/
theorem contMDiffAt_gramSchmidt_tangent {k : ℕ}
    {X : Fin k → (x : M) → TangentSpace (model n) x} {x : M}
    (hX : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (X i)) x)
    (hlin : LinearIndependent ℝ (fun i ↦ X i x)) (i : Fin k) :
    ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun y ↦ gramSchmidt ℝ (fun j ↦ X j y) i)) x := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have heq (y : M) : gramSchmidt ℝ (fun j ↦ X j y) i =
        X i y - ∑ j ∈ Finset.Iio i,
          (ℝ ∙ gramSchmidt ℝ (fun a ↦ X a y) j).starProjection (X i y) :=
      gramSchmidt_def ℝ (fun j ↦ X j y) i
    simp_rw [heq]
    simp_rw [Submodule.starProjection_singleton]
    apply (hX i).sub_section
    apply ContMDiffAt.sum_section
    intro j hj
    have hj' := ih j (Finset.mem_Iio.mp hj)
    have hn := contMDiffAt_norm_tangent n M hj' (gramSchmidt_ne_zero j hlin)
    exact (((hj'.inner_bundle (hX i)).mul
      ((hn.pow 2).inv₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero j hlin))))).smul_section
        hj').congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
          simp [div_eq_mul_inv])

/-- Normalized Gram--Schmidt is smooth wherever the original smooth family
is linearly independent. -/
theorem contMDiffAt_gramSchmidtNormed_tangent {k : ℕ}
    {X : Fin k → (x : M) → TangentSpace (model n) x} {x : M}
    (hX : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (X i)) x)
    (hlin : LinearIndependent ℝ (fun i ↦ X i x)) (i : Fin k) :
    ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun y ↦ gramSchmidtNormed ℝ (fun j ↦ X j y) i)) x := by
  have h := contMDiffAt_gramSchmidt_tangent n M hX hlin i
  exact ((contMDiffAt_norm_tangent n M h (gramSchmidt_ne_zero i hlin)).inv₀
    (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hlin))).smul_section h

/-- The canonical local tangent frame before orthonormalization. -/
def localTangentFrame (p : M) (i : Fin (2 * n)) :
    (x : M) → TangentSpace (model n) x :=
  localFrameVector n M p (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)

theorem localTangentFrame_linearIndependent (p : M) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    LinearIndependent ℝ (fun i ↦ localTangentFrame n M p i x) := by
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p
  have h := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis.linearIndependent.map'
    (e.continuousLinearEquivAt ℝ x hx).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr (e.continuousLinearEquivAt ℝ x hx).symm.injective)
  convert h using 1
  funext i
  change e.symmL ℝ x _ = (e.continuousLinearEquivAt ℝ x hx).symm _
  rw [e.symm_continuousLinearEquivAt_eq hx]
  simp only [OrthonormalBasis.coe_toBasis]

/-- A smooth orthonormal frame on the base set of a fixed trivialization.
Outside that set only a total extension is specified; no global frame is asserted. -/
def localOrthonormalFrame (p : M) (i : Fin (2 * n)) :
    (x : M) → TangentSpace (model n) x :=
  fun x ↦ gramSchmidtNormed ℝ (fun j ↦ localTangentFrame n M p j x) i

theorem localOrthonormalFrame_orthonormal (p : M) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    Orthonormal ℝ (fun i ↦ localOrthonormalFrame n M p i x) :=
  gramSchmidtNormed_orthonormal (localTangentFrame_linearIndependent n M p hx)

theorem contMDiffAt_localOrthonormalFrame (p : M) (i : Fin (2 * n)) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ContMDiffAt (model n) (model n).tangent ∞ (T% (localOrthonormalFrame n M p i)) x :=
  contMDiffAt_gramSchmidtNormed_tangent n M
    (fun j ↦ contMDiffAt_localFrameVector_of_mem n M p _ hx)
    (localTangentFrame_linearIndependent n M p hx) i

theorem contMDiffOn_localOrthonormalFrame (p : M) (i : Fin (2 * n)) :
    ContMDiffOn (model n) (model n).tangent ∞ (T% (localOrthonormalFrame n M p i))
      (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet :=
  fun _ hx ↦ (contMDiffAt_localOrthonormalFrame n M p i hx).contMDiffWithinAt

/-- The local orthonormal family is a basis of the whole tangent space. -/
def localOrthonormalBasis (p x : M) :
    OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x) :=
  gramSchmidtOrthonormalBasis
    (by change Module.finrank ℝ (Model n) = Fintype.card (Fin (2 * n)); simp [Model])
    (fun i ↦ localTangentFrame n M p i x)

theorem localOrthonormalBasis_apply (p : M) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (i : Fin (2 * n)) :
    localOrthonormalBasis n M p x i = localOrthonormalFrame n M p i x := by
  apply gramSchmidtOrthonormalBasis_apply
  apply norm_ne_zero_iff.mp
  rw [gramSchmidtNormed_unit_length i (localTangentFrame_linearIndependent n M p hx)]
  norm_num

theorem localOrthonormalFrame_span (p : M) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    Submodule.span ℝ (Set.range (fun i ↦ localOrthonormalFrame n M p i x)) = ⊤ := by
  simp_rw [← localOrthonormalBasis_apply n M p hx]
  exact (localOrthonormalBasis n M p x).toBasis.span_eq

/-- The diagonal pairing in Gram--Schmidt is a squared norm. -/
theorem inner_gramSchmidt_input {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (v : Fin k → E) (i : Fin k) :
    inner ℝ (gramSchmidt ℝ v i) (v i) = ‖gramSchmidt ℝ v i‖ ^ 2 := by
  calc
    _ = inner ℝ (gramSchmidt ℝ v i) (gramSchmidt ℝ v i +
        ∑ j ∈ Finset.Iio i, (inner ℝ (gramSchmidt ℝ v j) (v i) /
          ‖gramSchmidt ℝ v j‖ ^ 2) • gramSchmidt ℝ v j) := by
      congr 1
      exact gramSchmidt_def'' ℝ v i
    _ = _ := by
      rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq]
      have hs : (∑ j ∈ Finset.Iio i,
          inner ℝ (gramSchmidt ℝ v i) ((inner ℝ (gramSchmidt ℝ v j) (v i) /
            ‖gramSchmidt ℝ v j‖ ^ 2) • gramSchmidt ℝ v j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [inner_smul_right, gramSchmidt_orthogonal ℝ v (Finset.mem_Iio.mp hj).ne']
        simp
      rw [hs, add_zero]

/-- The diagonal pairing after normalization is a nonnegative norm. -/
theorem inner_gramSchmidtNormed_input {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {k : ℕ} (v : Fin k → E) (i : Fin k) :
    inner ℝ (gramSchmidtNormed ℝ v i) (v i) = ‖gramSchmidt ℝ v i‖ := by
  rw [gramSchmidtNormed, real_inner_smul_left, inner_gramSchmidt_input]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  by_cases h : ‖gramSchmidt ℝ v i‖ = 0
  · simp [h]
  · rw [pow_two, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- Gram--Schmidt preserves the orientation of a linearly independent family
of full dimension: its triangular change-of-frame determinant is positive. -/
theorem gramSchmidtOrthonormalBasis_det_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}
    (hd : Module.finrank ℝ E = Fintype.card (Fin k)) (v : Fin k → E)
    (hv : LinearIndependent ℝ v) :
    0 < (gramSchmidtOrthonormalBasis hd v).toBasis.det v := by
  rw [gramSchmidtOrthonormalBasis_det]
  apply Finset.prod_pos
  intro i _
  have hn : gramSchmidtNormed ℝ v i ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [gramSchmidtNormed_unit_length i hv]
    norm_num
  rw [gramSchmidtOrthonormalBasis_apply hd hn, inner_gramSchmidtNormed_input]
  exact norm_pos_iff.mpr (gramSchmidt_ne_zero i hv)

/-- Positivity is relative to the original tangent trivialization, so the
orthonormalization does not reverse its chosen orientation. -/
theorem localOrthonormalBasis_det_pos (p : M) {x : M}
    (hx : x ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    0 < (localOrthonormalBasis n M p x).toBasis.det
      (fun i ↦ localTangentFrame n M p i x) :=
  gramSchmidtOrthonormalBasis_det_pos _ _ (localTangentFrame_linearIndependent n M p hx)

/-- Every point has an open neighborhood carrying an actual smooth
orthonormal basis in every fiber. The construction is local and does not
assume parallelizability. -/
theorem exists_localSmoothOrthonormalFrame (p : M) :
    ∃ (s : Set M) (X : Fin (2 * n) → (x : M) → TangentSpace (model n) x),
      IsOpen s ∧ p ∈ s ∧
      (∀ i, ContMDiffOn (model n) (model n).tangent ∞ (T% (X i)) s) ∧
      (∀ x ∈ s, Orthonormal ℝ (fun i ↦ X i x)) ∧
      (∀ x ∈ s, Submodule.span ℝ (Set.range (fun i ↦ X i x)) = ⊤) := by
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p
  exact ⟨e.baseSet, localOrthonormalFrame n M p, e.open_baseSet,
    FiberBundle.mem_baseSet_trivializationAt' p,
    contMDiffOn_localOrthonormalFrame n M p,
    fun _ hx ↦ localOrthonormalFrame_orthonormal n M p hx,
    fun _ hx ↦ localOrthonormalFrame_span n M p hx⟩

end GaussBonnetChern
