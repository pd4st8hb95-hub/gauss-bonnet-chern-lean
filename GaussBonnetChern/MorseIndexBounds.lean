import GaussBonnetChern.MorseIndex

/-! # The uniform bound on the actual metric Morse index

This supplies the common homological degree bound for the finite Morse
filtration. It follows from the actual eigenvalue-count definition.
-/

noncomputable section
open Bundle
open scoped Manifold ContDiff
namespace GaussBonnetChern

theorem negativeEigenvalueCount_le_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : negativeEigenvalueCount hA ≤ Fintype.card ι := by
  unfold negativeEigenvalueCount
  exact (Finset.card_filter_le _ _).trans (by simp)

universe u
theorem morseIndex_le (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
    [IsManifold (model n) ∞ M]
    [RiemannianBundle (TangentSpace (model n) : M → Type _)]
    [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) :
    morseIndex n M hf ≤ 2 * n := by
  simpa only [morseIndex, Fintype.card_fin] using
    negativeEigenvalueCount_le_card (hessianMatrix_isHermitian n M hf)

end GaussBonnetChern
