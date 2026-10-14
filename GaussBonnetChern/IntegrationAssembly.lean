import GaussBonnetChern.MorseTopologicalIndex
import GaussBonnetChern.ChernLocalIndexLimit
import GaussBonnetChern.VanishingBallIntegral

/-! # Actual Morse boundary and curvature limits

All data in this file are constructed from the given metric and atlas. The two
limits have respectively the actual singular-homology Euler characteristic and
the frozen statement's curvature integral as their endpoints. Identifying their
integrands by normalized-section transgression and punctured Stokes is a separate
proof obligation; this file does not declare the main theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Filter Set Metric Module
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern
open DifferentialForm PuncturedManifold ChernLocalIndex ManifoldBoundaryStokes
universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] [Fact (0 < n)]

/-- The original positive charts can be selected at all actual critical
points so that their common shrinking radius gives disjoint valid balls.
The actual angular boundary integrals then tend to the actual topological
Euler characteristic. Neither connectedness nor nonemptiness is required. -/
theorem exists_morse_punctured_integral_limits
    (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source)) :
    ∃ (f : M → ℝ) (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
      (hfin : {p : M | mvfderiv (model n) f p = 0}.Finite)
      (j : ↥hfin.toFinset → Fin a.card),
      (∀ p, p.val ∈ (a.chart (j p)).source) ∧
      (∀ᶠ r in 𝓝[>] (0 : ℝ),
        (∀ p, closedBall ((a.chart (j p)) p.val) r ⊆ (a.chart (j p)).target) ∧
        Pairwise (fun p q ↦ Disjoint
          (coordinateClosedBall (a.chart (j p)) ((a.chart (j p)) p.val) r)
          (coordinateClosedBall (a.chart (j q)) ((a.chart (j q)) q.val) r)) ∧
        puncturedDomain (fun p ↦ a.chart (j p))
          (fun p ↦ (a.chart (j p)) p.val) (fun _ ↦ r) ⊆
            {x | gradient n M f x ≠ 0}) ∧
      Tendsto (fun r : ℝ ↦ ∑ p : ↥hfin.toFinset,
        sphereFormIntegral
          ((EuclideanSpace.basisFun (Fin (2*n)) ℝ).reindex
            (AngularVertical.evenSuccEquiv n Fact.out).symm)
          (positiveChartAngularBoundary n M a (j p) (gradient n M f) p.val r))
        (𝓝[>] (0 : ℝ)) (𝓝 (topologicalEulerCharacteristic M : ℝ)) ∧
      Tendsto (fun r : ℝ ↦ integralTopFormOn a ρ
        (puncturedDomain (fun p ↦ a.chart (j p))
          (fun p ↦ (a.chart (j p)) p.val) (fun _ ↦ r))
        (atlasEulerForm n M a Fact.out))
        (𝓝[>] (0 : ℝ)) (𝓝 (curvatureIntegral n M a ρ)) := by
  classical
  obtain ⟨f, hf, hfin, _, hdet, hindex⟩ :=
    exists_morse_gradient_topological_index n M
  let P := ↥hfin.toFinset
  let X := gradient n M f
  have hX : ContMDiff (model n) (model n).tangent ∞ (T% X) :=
    contMDiff_gradient n M hf
  have hz (p : P) : X p.val = 0 :=
    (gradient_eq_zero_iff n M f p.val).mpr (hfin.mem_toFinset.mp p.property)
  have hinj (p : P) : Function.Injective (fieldLinearization n M p.val X) := by
    apply LinearMap.ker_eq_bot.mp
    by_contra hker
    exact hdet p.val (hfin.mem_toFinset.mp p.property)
      (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)
  have hlocal (p : P) := exists_positiveChartAngularBoundaryIntegral_limit
    n M a hX (hz p) (hinj p)
  choose j hj hnz hlim using hlocal
  obtain ⟨R, hR, htarget, hdis⟩ := exists_disjoint_coordinateBalls
    (fun p : P ↦ p.val) Subtype.val_injective
    (fun p ↦ a.chart (j p)) hj
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ p : P, r ≤ R p := by
    apply eventually_all.mpr
    intro p
    exact ((gt_mem_nhds (hR p)).filter_mono nhdsWithin_le_nhds).mono
      (fun _ hr ↦ hr.le)
  refine ⟨f, hf, hfin, j, hj, ?_, ?_, ?_⟩
  · filter_upwards [hsmall, self_mem_nhdsWithin] with r hr hrpos
    refine ⟨fun p ↦ (closedBall_subset_closedBall (hr p)).trans (htarget p), ?_, ?_⟩
    · intro p q hpq
      apply (hdis hpq).mono
      · exact fun x hx ↦ ⟨hx.1, (closedBall_subset_closedBall (hr p)) hx.2⟩
      · exact fun x hx ↦ ⟨hx.1, (closedBall_subset_closedBall (hr q)) hx.2⟩
    · intro x hx hzero
      have hxcrit := (gradient_eq_zero_iff n M f x).mp hzero
      let p : P := ⟨x, hfin.mem_toFinset.mpr hxcrit⟩
      apply hx
      apply mem_iUnion.mpr
      refine ⟨p, hj p, ?_⟩
      exact mem_ball_self hrpos
  · have hs := tendsto_finsetSum Finset.univ (fun p _ ↦ hlim p)
    have he : (∑ p : P, Real.sign (fieldLinearization n M p.val X).det) =
        (topologicalEulerCharacteristic M : ℝ) := by
      rw [hindex]
      exact Finset.sum_coe_sort hfin.toFinset
        (fun p ↦ Real.sign (fieldLinearization n M p X).det)
    simpa only [he] using hs
  · exact tendsto_integralTopFormOn_puncturedEuler Fact.out a ρ hρ
      (fun p : P ↦ a.chart (j p)) (fun p ↦ (a.chart (j p)) p.val)
      (fun _ r ↦ r) (fun _ ↦ tendsto_id.mono_left nhdsWithin_le_nhds)

end GaussBonnetChern
