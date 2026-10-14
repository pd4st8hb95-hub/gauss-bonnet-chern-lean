import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.EulerCharacteristic

/-! # The topological side of the target

The Euler characteristic is computed from actual singular homology with real
coefficients. It is independent of every metric, curvature, and integral.
For closed smooth manifolds the homology is finite-dimensional and vanishes
above the dimension. Proving those facts is part of the future proof work.
-/

noncomputable section

universe u

namespace GaussBonnetChern

open CategoryTheory

/-- Singular chains with real coefficients, lifted to the space's universe. -/
def singularChains (M : Type u) [TopologicalSpace M] :
    ChainComplex (ModuleCat.{u} ℝ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℝ)).obj
    (ModuleCat.of ℝ (ULift.{u} ℝ))).obj (TopCat.of M)

/-- The homological Euler characteristic, not the Euler characteristic of the
usually infinite-dimensional singular chain groups. -/
def topologicalEulerCharacteristic (M : Type u) [TopologicalSpace M] : ℤ :=
  (singularChains M).homologyEulerChar

end GaussBonnetChern
