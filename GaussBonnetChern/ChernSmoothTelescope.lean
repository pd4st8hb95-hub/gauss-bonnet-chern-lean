import GaussBonnetChern.ChernAngularDifferential

/-! Telescoping of the actual smooth angular family. The totalized exterior
derivative is never declared linear on the space of arbitrary forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm

theorem recurrence_telescope_fin {V : Type*} [AddCommGroup V] [Module ℝ V]
    (n : ℕ) (Y : Fin (n+1) → V) (hY : Y 0 = 0) :
    (∑ k : Fin n, angularCoefficient n k.val •
      (Y k.castSucc - recurrenceCoefficient n k.val • Y k.succ)) =
      -(angularCoefficient n n • Y (Fin.last n)) := by
  let Z : Fin (n+1) → V := fun k ↦ angularCoefficient n k.val • Y k
  have hterm (k : Fin n) : angularCoefficient n k.val •
      (Y k.castSucc - recurrenceCoefficient n k.val • Y k.succ) =
        Z k.castSucc - Z k.succ := by
    rw [smul_sub, smul_smul, ← angularCoefficient_succ k.isLt]
    rfl
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  have hl : (∑ k : Fin n, Z k.castSucc) = (∑ k : Fin (n+1), Z k) - Z (Fin.last n) := by
    apply eq_sub_iff_add_eq.mpr
    exact (Fin.sum_univ_castSucc Z).symm
  have hr : (∑ k : Fin n, Z k.succ) = (∑ k : Fin (n+1), Z k) - Z 0 := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (Fin.sum_univ_succ Z).symm
  rw [hl,hr]
  have hz : Z 0 = 0 := by simp only [Z, Fin.val_zero, hY, smul_zero]
  have hlast : Z (Fin.last n) = angularCoefficient n n • Y (Fin.last n) := rfl
  rw [hz,hlast]
  abel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℝ,E) ∞ P]

/-- Differentiate the actual smooth finite family by the proved finite
sum and constant-scalar rules, and only then apply algebraic telescoping.
The actual geometric recurrence remains an explicit input. -/
theorem exteriorDerivative_angularForm_of_recurrence (n : ℕ) (hn : 0<n)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (hu : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (u i))
    (hθ : ∀ i, IsSmooth (θ i)) (hB : ∀ i j, IsSmooth (B i j))
    (Y : Fin (n+1) → Form 𝓘(ℝ,E) P (2*n)) (hY : Y 0 = 0)
    (hrec : ∀ k : Fin n,
      degreeCastForm (show (2*n-1)+1=2*n by omega)
        (exteriorDerivative (angularTerm n k u θ B)) =
        Y k.castSucc - recurrenceCoefficient n k.val • Y k.succ) :
    degreeCastForm (show (2*n-1)+1=2*n by omega)
      (exteriorDerivative (angularForm n u θ B)) =
      -(angularCoefficient n n • Y (Fin.last n)) := by
  rw [← formCastLinear_apply]
  unfold angularForm
  rw [exteriorDerivative_sum Finset.univ _ (fun k _ ↦
    (isSmooth_angularTerm n k u θ B hu hθ hB).const_smul _)]
  simp only [map_sum, exteriorDerivative_smul, map_smul, formCastLinear_apply, hrec]
  exact recurrence_telescope_fin n Y hY

end GaussBonnetChern.Chern
