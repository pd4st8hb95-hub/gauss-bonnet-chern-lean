import GaussBonnetChern.Statement
import GaussBonnetChern.IntegrationAssembly
import GaussBonnetChern.NormalizedFieldTransgression
import GaussBonnetChern.ChernLocalIndexSuccTransport
import GaussBonnetChern.PuncturedStokes

/-! # Gauss–Bonnet–Chern

The positive dimension is represented once as a successor in order to use
the punctured Stokes coordinate convention. The Morse function, all local
indices, and both limits are those of the original metric and manifold.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle Filter Set Metric MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern
open DifferentialForm ManifoldBoundaryStokes PuncturedManifold
  BoundarySphereTrace StokesLocalization FiniteChartStokes ChernLocalIndex

universe u

private theorem angularDegree_succ (k : ℕ) : 2*(k+1)-1 = 2*k+1 := by omega

private theorem integralTopFormOn_neg
    {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
    [IsManifold (model n) ∞ M]
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (Ω : Set M) (α : Form (model n) M (2*n)) :
    integralTopFormOn a ρ Ω (-α) = -integralTopFormOn a ρ Ω α := by
  unfold integralTopFormOn
  simp only [topFormIntegrand, topFormCoefficient, chartRepresentation,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    pullback_apply, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
    mul_neg, integral_neg, Finset.sum_neg_distrib]

section Successor
variable (k : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model (k+1)) M]
  [IsManifold (model (k+1)) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (TangentSpace (model (k+1)) : M → Type _)]
  [IsContMDiffRiemannianBundle (model (k+1)) ∞ (Model (k+1))
    (TangentSpace (model (k+1)) : M → Type _)]

local instance successorPositive : Fact (0 < k+1) := ⟨by omega⟩
local instance successorSphereDimension : Fact (Module.finrank ℝ (Model (k+1)) = (2*k+1)+1) :=
  ⟨by simp [Model, Nat.mul_add, Nat.add_assoc]⟩

/-- The actual curvature integral equals the actual singular-homology
Euler characteristic, with no auxiliary transgression hypothesis. -/
theorem curvatureIntegral_eq_topologicalEulerCharacteristic
    (a : FiniteOrientedAtlas (k+1) M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model (k+1)) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source)) :
    curvatureIntegral (k+1) M a ρ = (topologicalEulerCharacteristic M : ℝ) := by
  classical
  obtain ⟨f, hf, hfin, j, hj, hballs, hboundary, hcurvature⟩ :=
    exists_morse_punctured_integral_limits (k+1) M a ρ hρ
  let P := ↥hfin.toFinset
  let X := gradient (k+1) M f
  have hX : ContMDiff (model (k+1)) (model (k+1)).tangent ∞ (T% X) :=
    contMDiff_gradient (k+1) M hf
  let β : Form (model (k+1)) M (2*k+1) := normalizedFieldAngularForm (k+1) M a X hX
  let e := atlasEulerForm (k+1) M a (by omega)
  let c : P → Model (k+1) := fun p ↦ (a.chart (j p)) p.val
  let Ω : ℝ → Set M := fun r ↦ puncturedDomain (fun p ↦ a.chart (j p)) c (fun _ ↦ r)
  have hd (x : M) (hx : X x ≠ 0) : exteriorDerivative β x = -e x := by
    have h := normalizedFieldAngularForm_transgression (k+1) M a X hX x hx
    simpa only [β, e, angularDegree_succ k, degreeCastForm] using h
  have hs (x : M) (hx : X x ≠ 0) : IsSmoothAtInCharts β x := by
    have h := isSmoothAtInCharts_normalizedFieldAngularForm (k+1) M a X hX x hx
    simpa only [β, angularDegree_succ k] using h
  have heq : (fun r : ℝ ↦ integralTopFormOn a ρ (Ω r) e) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r ↦ ∑ p : P, sphereFormIntegral
        ((EuclideanSpace.basisFun (Fin (2*(k+1))) ℝ).reindex
          (AngularVertical.evenSuccEquiv (k+1) Fact.out).symm)
        (positiveChartAngularBoundary (k+1) M a (j p) X p.val r)) := by
    filter_upwards [hballs, self_mem_nhdsWithin] with r hr hrpos
    obtain ⟨hcover, hdis, hnonzero⟩ := hr
    have hstokes := PuncturedStokes.stokes_puncturedDomain a j c (fun _ ↦ r)
      (fun _ ↦ hrpos) hcover hdis ρ hρ
      (nonzeroFieldDomain (k+1) M X hX) (nonzeroFieldDomain (k+1) M X hX).isOpen
      hnonzero β (fun x hx ↦ hs x hx)
    have hderiv : integralTopFormOn a ρ (Ω r) (exteriorDerivative β) =
        -integralTopFormOn a ρ (Ω r) e := by
      rw [integralTopFormOn_congr a ρ (Ω r) (isClosed_puncturedDomain _ _ _)
        (exteriorDerivative β) (-e) (fun x hx ↦ hd x (hnonzero hx))]
      exact integralTopFormOn_neg a ρ (Ω r) e
    rw [hderiv] at hstokes
    apply neg_injective
    rw [hstokes]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    have hnz : ∀ u : sphere (0 : Model (k+1)) 1,
        X (centeredInverseChart (k+1) M (a.chart (j p)) p.val
          (r • (u : Model (k+1)))) ≠ 0 := by
      intro u
      exact hnonzero (PuncturedStokes.sphereEmbedding_mem_domain a j c (fun _ ↦ r)
        (fun _ ↦ hrpos) hcover hdis p u)
    exact (ChernLocalIndexSuccTransport.successor_boundary_integral_eq_ambient
      k M a (j p) X hX p.val r hrpos (hcover p) hnz).symm
  exact tendsto_nhds_unique hcurvature (hboundary.congr' heq.symm)

end Successor

/-- The full frozen target: every positive even dimension, arbitrary universe,
and compact oriented smooth Riemannian manifold, including empty and disconnected
manifolds. -/
theorem gaussBonnetChern : GaussBonnetChernStatement.{u} := by
  intro n hn M _ _ _ _ _ _ a g
  cases n with
  | zero => omega
  | succ k =>
    unfold StatementFor
    letI : RiemannianBundle (TangentSpace (model (k+1)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle (model (k+1)) ∞ (Model (k+1))
        (TangentSpace (model (k+1)) : M → Type _) := inferInstance
    intro ρ hρ
    exact curvatureIntegral_eq_topologicalEulerCharacteristic k M a ρ hρ

end GaussBonnetChern
