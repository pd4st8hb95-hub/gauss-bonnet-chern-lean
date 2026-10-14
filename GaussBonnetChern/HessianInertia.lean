import GaussBonnetChern.MorseIndex
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Inertia of the actual Hermitian Hessian

The eigenvalue count in `MorseIndex` agrees with the intrinsic negative
signature of the associated quadratic form. Consequently it is invariant
under every invertible change of coordinates, including degenerate forms
and zero-dimensional spaces.
-/

noncomputable section

open scoped BigOperators Matrix

namespace GaussBonnetChern

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixQuadraticForm_apply (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    A.toQuadraticForm' x = x ⬝ᵥ A *ᵥ x := by
  exact Matrix.toLinearMap₂'_apply' _ _ _

theorem matrixQuadraticForm_diagonal (w : ι → ℝ) :
    (Matrix.diagonal w).toQuadraticForm' = QuadraticMap.weightedSumSquares ℝ w := by
  ext x
  simp only [matrixQuadraticForm_apply,
    dotProduct, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Actual pullback of a quadratic form by an invertible matrix. -/
theorem matrixQuadraticForm_equivalent_congruence (A P : Matrix ι ι ℝ)
    (hP : P.det ≠ 0) :
    A.toQuadraticForm'.Equivalent (Pᵀ * A * P).toQuadraticForm' := by
  let e := P.toLinearEquiv (Pi.basisFun ℝ ι) (isUnit_iff_ne_zero.mpr hP)
  have he (x : ι → ℝ) : e x = P *ᵥ x := by
    simp [e, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin']
  have hQ : (Pᵀ * A * P).toQuadraticForm' =
      A.toQuadraticForm'.comp e.toLinearMap := by
    ext x
    simp only [matrixQuadraticForm_apply, QuadraticMap.comp_apply,
      LinearEquiv.coe_coe, he, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [hQ]
  exact ⟨A.toQuadraticForm'.isometryEquivOfCompLinearEquiv e⟩

/-- Spectral diagonalization identifies the count with a basis-free signature. -/
theorem negativeEigenvalueCount_eq_sigNeg {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    negativeEigenvalueCount hA = sigNeg A.toQuadraticForm' := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  have hU : U.det ≠ 0 := by
    exact (Matrix.isUnit_det_of_left_inverse (Unitary.coe_star_mul_self
      hA.eigenvectorUnitary)).ne_zero
  have hd : Uᵀ * A * U = Matrix.diagonal hA.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, Function.id_comp, U] using
        hA.conjStarAlgAut_star_eigenvectorUnitary
  have hs := (matrixQuadraticForm_equivalent_congruence A U hU).sigNeg_eq
  rw [hd, matrixQuadraticForm_diagonal, QuadraticForm.sigNeg_weightedSumSquares] at hs
  rw [hs]
  simpa only [negativeEigenvalueCount, Set.ncard_eq_toFinset_card',
    Set.toFinset_ofPred]

/-- Sylvester's law for the original eigenvalue-count definition. -/
theorem negativeEigenvalueCount_congruence {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (P : Matrix ι ι ℝ) (hP : P.det ≠ 0)
    (hPAP : (Pᵀ * A * P).IsHermitian) :
    negativeEigenvalueCount hPAP = negativeEigenvalueCount hA := by
  rw [negativeEigenvalueCount_eq_sigNeg, negativeEigenvalueCount_eq_sigNeg]
  exact (matrixQuadraticForm_equivalent_congruence A P hP).sigNeg_eq.symm

theorem isHermitian_congruence {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (P : Matrix ι ι ℝ) : (Pᵀ * A * P).IsHermitian := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_mul P hA

theorem negativeEigenvalueCount_congruence' {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (P : Matrix ι ι ℝ) (hP : P.det ≠ 0) :
    negativeEigenvalueCount (isHermitian_congruence hA P) = negativeEigenvalueCount hA :=
  negativeEigenvalueCount_congruence hA P hP _

/-- Positive rescaling does not change negative-definite subspaces. -/
theorem sigNeg_smul_pos {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (Q : QuadraticForm ℝ E) {c : ℝ} (hc : 0 < c) :
    sigNeg (c • Q) = sigNeg Q := by
  have hV (V : Submodule ℝ E) :
      ((-(c • Q)).restrict V).PosDef ↔ ((-Q).restrict V).PosDef := by
    simp only [QuadraticMap.PosDef, QuadraticMap.restrict_apply, QuadraticMap.neg_apply,
      QuadraticMap.smul_apply, smul_eq_mul, ← mul_neg,
      mul_pos_iff_of_pos_left hc]
  apply le_antisymm
  · obtain ⟨V, hr, hpos⟩ := exists_finrank_eq_sigNeg_and_negDef (c • Q)
    rw [← hr]
    exact le_sigNeg_of_negDef Q ((hV V).mp hpos)
  · obtain ⟨V, hr, hpos⟩ := exists_finrank_eq_sigNeg_and_negDef Q
    rw [← hr]
    exact le_sigNeg_of_negDef (c • Q) ((hV V).mpr hpos)

theorem matrixQuadraticForm_smul (A : Matrix ι ι ℝ) (c : ℝ) :
    (c • A).toQuadraticForm' = c • A.toQuadraticForm' := by
  ext x
  simp [matrixQuadraticForm_apply, Matrix.smul_mulVec]

theorem negativeEigenvalueCount_smul_pos {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    {c : ℝ} (hc : 0 < c) :
    negativeEigenvalueCount (hA.smul (IsSelfAdjoint.all c)) = negativeEigenvalueCount hA := by
  rw [negativeEigenvalueCount_eq_sigNeg, negativeEigenvalueCount_eq_sigNeg,
    matrixQuadraticForm_smul, sigNeg_smul_pos _ hc]

theorem negativeEigenvalueCount_diagonal (w : ι → ℝ) :
    negativeEigenvalueCount (Matrix.isHermitian_diagonal w) =
      (Finset.univ.filter (fun i ↦ w i < 0)).card := by
  rw [negativeEigenvalueCount_eq_sigNeg, matrixQuadraticForm_diagonal,
    QuadraticForm.sigNeg_weightedSumSquares]
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- Normalized negative squares are counted exactly, including both endpoints. -/
theorem negativeEigenvalueCount_diagonal_sign (s : Finset ι) :
    negativeEigenvalueCount (Matrix.isHermitian_diagonal
      (fun i ↦ if i ∈ s then (-1 : ℝ) else 1)) = s.card := by
  rw [negativeEigenvalueCount_diagonal]
  congr 1
  ext i
  by_cases hi : i ∈ s <;> simp [hi]

theorem negativeEigenvalueCount_positive_identity :
    negativeEigenvalueCount (Matrix.isHermitian_diagonal (fun _ : ι ↦ (1 : ℝ))) = 0 := by
  simp [negativeEigenvalueCount_diagonal]

theorem negativeEigenvalueCount_negative_identity :
    negativeEigenvalueCount (Matrix.isHermitian_diagonal (fun _ : ι ↦ (-1 : ℝ))) =
      Fintype.card ι := by
  simp [negativeEigenvalueCount_diagonal]

section Bilinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem matrixQuadraticForm_bilinForm (B : LinearMap.BilinForm ℝ E)
    (b : Module.Basis ι ℝ E) :
    (B.toMatrix b).toQuadraticForm' = B.toQuadraticMap.comp b.equivFun.symm.toLinearMap := by
  ext x
  rw [matrixQuadraticForm_apply, QuadraticMap.comp_apply,
    LinearMap.BilinMap.toQuadraticMap_apply]
  exact B.dotProduct_toMatrix_mulVec b x x

/-- The eigenvalue count in any basis is the signature used by real Morse normal forms. -/
theorem negativeEigenvalueCount_bilinForm (B : LinearMap.BilinForm ℝ E)
    (b : Module.Basis ι ℝ E) (hB : (B.toMatrix b).IsHermitian) :
    negativeEigenvalueCount hB = sigNeg B.toQuadraticMap := by
  rw [negativeEigenvalueCount_eq_sigNeg, matrixQuadraticForm_bilinForm]
  exact (show B.toQuadraticMap.Equivalent
    (B.toQuadraticMap.comp b.equivFun.symm.toLinearMap) from
      ⟨B.toQuadraticMap.isometryEquivOfCompLinearEquiv b.equivFun.symm⟩).sigNeg_eq.symm

end Bilinear

section MetricHessian

open Bundle
open scoped Manifold ContDiff

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

theorem hessianMatrix_eq_bilinForm_toMatrix {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) :
    hessianMatrix n M f x = (hessianBilinear n M f x).toBilinForm.toMatrix
      (orthonormalFrame n M x).toBasis := by
  ext i j
  simp only [hessianMatrix, LinearMap.BilinForm.toMatrix_apply,
    ContinuousLinearMap.toBilinForm_apply, hessianBilinear_apply,
    OrthonormalBasis.coe_toBasis]
  exact hessian_symm n M hf _ _

/-- The original metric Morse index equals the signature used in Morse coordinates. -/
theorem morseIndex_eq_sigNeg_hessian {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) :
    morseIndex n M hf = sigNeg (hessianBilinear n M f x).toBilinForm.toQuadraticMap := by
  have hb : ((hessianBilinear n M f x).toBilinForm.toMatrix
      (orthonormalFrame n M x).toBasis).IsHermitian := by
    rw [← hessianMatrix_eq_bilinForm_toMatrix n M hf]
    exact hessianMatrix_isHermitian n M hf
  simpa only [← hessianMatrix_eq_bilinForm_toMatrix n M hf, morseIndex] using
    negativeEigenvalueCount_bilinForm (hessianBilinear n M f x).toBilinForm
      (orthonormalFrame n M x).toBasis hb

/-- The Taylor coefficient `1/2` preserves the original Morse index. -/
theorem morseIndex_eq_sigNeg_half_hessian {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) :
    morseIndex n M hf =
      sigNeg ((1 / 2 : ℝ) • (hessianBilinear n M f x).toBilinForm.toQuadraticMap) := by
  rw [sigNeg_smul_pos _ (by norm_num), morseIndex_eq_sigNeg_hessian n M hf]

end MetricHessian

end GaussBonnetChern
