import GaussBonnetChern.MorseHessian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Basic.Real.Sign

/-! # Hessian index and determinant sign

The index counts the negative eigenvalues of the actual covariant Hessian,
with multiplicity. The determinant is that of the covariant derivative of
the metric gradient. Identifying this map with the coordinate derivative at
a zero, and constructing Morse coordinates, are separate obligations.
-/

noncomputable section

open Bundle
open scoped BigOperators Manifold ContDiff

namespace GaussBonnetChern

theorem real_sign_mul (a b : ℝ) : Real.sign (a * b) = Real.sign a * Real.sign b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha <;>
    rcases lt_trichotomy b 0 with hb | rfl | hb <;>
    simp [Real.sign_of_neg, Real.sign_of_pos, *, mul_pos_of_neg_of_neg,
      mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg, mul_pos]

theorem real_sign_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    Real.sign (∏ i ∈ s, a i) = ∏ i ∈ s, Real.sign (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, real_sign_mul, ih]

/-- All factors are nonzero; the negative factors are counted with multiplicity. -/
theorem real_sign_prod_eq_neg_one_pow {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    Real.sign (∏ i ∈ s, a i) = (-1 : ℝ) ^ (s.filter (fun i ↦ a i < 0)).card := by
  classical
  rw [real_sign_prod]
  have h : ∀ i ∈ s, Real.sign (a i) = if a i < 0 then (-1 : ℝ) else 1 := by
    intro i hi
    rcases (ha i hi).lt_or_gt with hn | hp
    · simp [hn, Real.sign_of_neg hn]
    · simp [hp.not_gt, Real.sign_of_pos hp]
  rw [Finset.prod_congr rfl h, ← Finset.prod_filter]
  exact Finset.prod_const _

def negativeEigenvalueCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter (fun i ↦ hA.eigenvalues i < 0)).card

theorem sign_det_eq_negativeEigenvalueCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (hdet : A.det ≠ 0) :
    Real.sign A.det = (-1 : ℝ) ^ negativeEigenvalueCount hA := by
  have he : ∀ i, hA.eigenvalues i ≠ 0 := by
    simpa [hA.det_eq_prod_eigenvalues, Finset.prod_ne_zero_iff] using hdet
  rw [hA.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  exact real_sign_prod_eq_neg_one_pow Finset.univ _ (fun i _ ↦ he i)

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

/-- Matrix columns are gradient-derivative vectors in the original pointwise
orthonormal basis. No smoothness of the arbitrary pointwise basis is assumed. -/
def hessianMatrix (f : M → ℝ) (x : M) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun i j ↦ hessian n M f x (orthonormalFrame n M x j) (orthonormalFrame n M x i)

theorem hessianMatrix_isHermitian {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) : (hessianMatrix n M f x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simpa only [star_trivial, hessianMatrix] using
    hessian_symm n M hf (orthonormalFrame n M x i) (orthonormalFrame n M x j)

def morseIndex {f : M → ℝ} {x : M} (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) : ℕ :=
  negativeEigenvalueCount (hessianMatrix_isHermitian n M hf)

theorem hessianMatrix_eq_toMatrix (f : M → ℝ) (x : M) :
    hessianMatrix n M f x =
      LinearMap.toMatrix (orthonormalFrame n M x).toBasis (orthonormalFrame n M x).toBasis
        (connection n M (gradient n M f) x).toLinearMap := by
  ext i j
  simp only [hessianMatrix, hessian, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
  exact real_inner_comm _ _

theorem hessianMatrix_det (f : M → ℝ) (x : M) :
    (hessianMatrix n M f x).det =
      LinearMap.det (connection n M (gradient n M f) x).toLinearMap := by
  rw [hessianMatrix_eq_toMatrix, LinearMap.det_toMatrix]

theorem sign_hessianMatrix_det {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) (hdet : (hessianMatrix n M f x).det ≠ 0) :
    Real.sign (hessianMatrix n M f x).det = (-1 : ℝ) ^ morseIndex n M hf :=
  sign_det_eq_negativeEigenvalueCount (hessianMatrix_isHermitian n M hf) hdet

/-- The intrinsic derivative at a gradient zero will be identified with this
covariant derivative in the linearization module. -/
theorem sign_gradient_covariant_det {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x)
    (hdet : LinearMap.det (connection n M (gradient n M f) x).toLinearMap ≠ 0) :
    Real.sign (LinearMap.det (connection n M (gradient n M f) x).toLinearMap) =
      (-1 : ℝ) ^ morseIndex n M hf := by
  rw [← hessianMatrix_det] at hdet ⊢
  exact sign_hessianMatrix_det n M hf hdet

end GaussBonnetChern
