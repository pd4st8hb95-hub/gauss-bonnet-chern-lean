import GaussBonnetChern.Geometry
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! # Nonvacuous atlas integration and positive chart volume density

The integration choices in the main statement exist. Each actual inverse chart
has independent coordinate tangent vectors, so its metric matrix is positive
definite and has positive determinant. No positivity assumption is added to
the statement's Riemannian metrics.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace GaussBonnetChern

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

theorem FiniteOrientedAtlas.exists_partition (a : FiniteOrientedAtlas n M)
    [T2Space M] [CompactSpace M] :
    ∃ ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ,
      ρ.IsSubordinate (fun i ↦ (a.chart i).source) := by
  apply SmoothPartitionOfUnity.exists_isSubordinate (model n) isClosed_univ
    (fun i ↦ (a.chart i).source) (fun i ↦ (a.chart i).open_source)
  intro x _
  obtain ⟨i, hi⟩ := a.covers x
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

variable [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

omit [IsManifold (model n) ∞ M]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)] in
theorem chartMetric_posDef (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (y : Model n) (hy : y ∈ e.target) :
    Matrix.PosDef (chartMetric n M e y) := by
  have hdiff : e.MDifferentiable (model n) (model n) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have hi := hdiff.symm.mfderiv_injective hy
  change Matrix.PosDef (Matrix.gram ℝ (fun i ↦
    mfderiv (model n) (model n) e.symm y (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)))
  apply Matrix.posDef_gram_of_linearIndependent
  exact (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis.linearIndependent.map'
    (mfderiv (model n) (model n) e.symm y).toLinearMap (LinearMap.ker_eq_bot.mpr hi)

theorem chartMetric_det_pos (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (y : Model n) (hy : y ∈ e.target) :
    0 < (chartMetric n M e y).det :=
  (chartMetric_posDef e he y hy).det_pos

theorem chartVolumeDensity_pos (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M)
    (y : Model n) (hy : y ∈ e.target) :
    0 < chartVolumeDensity n M e y :=
  Real.sqrt_pos.mpr (chartMetric_det_pos e he y hy)

end GaussBonnetChern
