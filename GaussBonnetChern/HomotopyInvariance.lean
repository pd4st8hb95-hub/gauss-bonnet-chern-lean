import GaussBonnetChern.RelativeHomology
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Equiv

/-! # Homotopy invariance for the actual real singular chains

The coefficients and universe are exactly those used in `singularChains`.
Mathlib's topological-to-simplicial homotopy construction supplies an actual
chain homotopy; no preservation of topological pushouts is asserted.
-/

noncomputable section

universe u

namespace GaussBonnetChern

open CategoryTheory HomologicalComplex
open scoped ContinuousMap

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- The chain map induced by an actual continuous map. -/
def singularChainsMap (f : C(X, Y)) : singularChains X ⟶ singularChains Y :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℝ)).obj
    realHomologyCoefficients).map (TopCat.ofHom f)

@[simp]
theorem singularChainsMap_id : singularChainsMap (ContinuousMap.id X) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

@[simp]
theorem singularChainsMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    singularChainsMap (g.comp f) = singularChainsMap f ≫ singularChainsMap g :=
  Functor.map_comp _ _ _

/-- An actual continuous homotopy induces a chain homotopy of the actual
singular chain maps, with all components defined in the locked library. -/
def singularChainsHomotopy {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    _root_.Homotopy (singularChainsMap f) (singularChainsMap g) :=
  (show TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) from H).singularChainComplexFunctorObjMap
    realHomologyCoefficients

/-- The homology map associated to `singularChainsMap`. -/
def singularHomologyMap (f : C(X, Y)) (k : ℕ) :
    singularHomology X k ⟶ singularHomology Y k :=
  homologyMap (singularChainsMap f) k

@[simp]
theorem singularHomologyMap_id (k : ℕ) :
    singularHomologyMap (ContinuousMap.id X) k = 𝟙 _ := by
  simp [singularHomologyMap]

@[simp]
theorem singularHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z)) (k : ℕ) :
    singularHomologyMap (g.comp f) k =
      singularHomologyMap f k ≫ singularHomologyMap g k := by
  simp [singularHomologyMap, homologyMap_comp]

/-- Homotopic maps act equally on each actual real singular homology group. -/
theorem singularHomologyMap_eq_of_homotopic {f g : C(X, Y)}
    (H : f.Homotopic g) (k : ℕ) : singularHomologyMap f k = singularHomologyMap g k := by
  obtain ⟨H⟩ := H
  exact (singularChainsHomotopy H).homologyMap_eq k

/-- A topological homotopy equivalence induces an isomorphism on actual
singular homology, with the forward and inverse maps explicitly given. -/
def singularHomologyIsoOfHomotopyEquiv (e : X ≃ₕ Y) (k : ℕ) :
    singularHomology X k ≅ singularHomology Y k where
  hom := singularHomologyMap e.toFun k
  inv := singularHomologyMap e.invFun k
  hom_inv_id := by
    rw [← singularHomologyMap_comp,
      singularHomologyMap_eq_of_homotopic e.left_inv, singularHomologyMap_id]
  inv_hom_id := by
    rw [← singularHomologyMap_comp,
      singularHomologyMap_eq_of_homotopic e.right_inv, singularHomologyMap_id]

/-- Homeomorphisms are a special case of the same genuine induced maps. -/
def singularHomologyIsoOfHomeomorph (e : X ≃ₜ Y) (k : ℕ) :
    singularHomology X k ≅ singularHomology Y k :=
  singularHomologyIsoOfHomotopyEquiv e.toHomotopyEquiv k

/-- Finite dimensionality transports along a homotopy equivalence. -/
theorem singularHomology_finiteDimensional_of_homotopyEquiv
    (e : X ≃ₕ Y) (k : ℕ) [FiniteDimensional ℝ (singularHomology Y k)] :
    FiniteDimensional ℝ (singularHomology X k) :=
  (singularHomologyIsoOfHomotopyEquiv e k).toLinearEquiv.symm.finiteDimensional

/-- The rank identity is separated from the finite-dimensionality theorem. -/
theorem singularHomology_finrank_eq_of_homotopyEquiv (e : X ≃ₕ Y) (k : ℕ) :
    Module.finrank ℝ (singularHomology X k) = Module.finrank ℝ (singularHomology Y k) :=
  (singularHomologyIsoOfHomotopyEquiv e k).toLinearEquiv.finrank_eq

end GaussBonnetChern
