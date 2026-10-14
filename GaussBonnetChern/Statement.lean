import GaussBonnetChern.Geometry
import GaussBonnetChern.Topology

/-! # The full, unproved Gauss–Bonnet–Chern target

This file defines a proposition to be proved. It does not declare the proposition
as an axiom, or introduce an unproved theorem into Lean's environment.

No connectedness, global frame, constant curvature, positive
curvature, embedding, or cohomological comparison hypothesis is imposed.
-/

noncomputable section

universe u

open Bundle
open scoped Manifold ContDiff

namespace GaussBonnetChern

/-- A precise proof target for a fixed closed, oriented, smooth Riemannian
`2*n`-manifold. All subordinate smooth partitions are covered; their existence
follows from Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`.

The metric is registered once and used for the connection, orthonormal frame,
curvature contraction, and chartwise Riemannian volume density.
This declaration defines a proposition; it supplies no proof of that proposition. -/
def StatementFor (n : ℕ) (M : Type u)
    [TopologicalSpace M] [ChartedSpace (Model n) M] [IsManifold (model n) ∞ M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    (a : FiniteOrientedAtlas n M) (g : SmoothMetric n M) : Prop :=
  letI : RiemannianBundle (TangentSpace (model n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  ∀ ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ,
    ρ.IsSubordinate (fun i ↦ (a.chart i).source) →
      curvatureIntegral n M a ρ = (topologicalEulerCharacteristic M : ℝ)

/-- The all-positive-even-dimensional Gauss–Bonnet–Chern proposition.

`Model n` is the full Euclidean space, not a half-space, so the manifold has
no boundary. The finite positively compatible smooth atlas represents the
chosen orientation. The empty manifold and disconnected manifolds are allowed.

The future main theorem must inhabit this `Prop`. Its proof is not supplied
in this statement-only stage. -/
def GaussBonnetChernStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
      [IsManifold (model n) ∞ M] [CompactSpace M] [T2Space M]
      [SecondCountableTopology M]
      (a : FiniteOrientedAtlas n M) (g : SmoothMetric n M),
      StatementFor n M a g

end GaussBonnetChern
