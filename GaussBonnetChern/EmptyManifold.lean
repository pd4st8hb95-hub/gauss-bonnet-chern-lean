import GaussBonnetChern.Statement
import GaussBonnetChern.BasicHomology

/-! # The empty case of the original target

This proves the original metric and atlas formula when the manifold is empty.
The nonempty case of the all-dimensional main theorem remains separate.
-/

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace GaussBonnetChern
universe u

theorem statementFor_isEmpty (n : ℕ) (M : Type u)
    [TopologicalSpace M] [ChartedSpace (Model n) M] [IsManifold (model n) ∞ M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M] [IsEmpty M]
    (a : FiniteOrientedAtlas n M) (g : SmoothMetric n M) : StatementFor n M a g := by
  letI : IsEmpty (Fin a.card) := ⟨fun i ↦ isEmptyElim ((a.chart i).symm 0)⟩
  unfold StatementFor
  intro ρ hρ
  simp [curvatureIntegral, topologicalEulerCharacteristic_of_isEmpty]

end GaussBonnetChern
