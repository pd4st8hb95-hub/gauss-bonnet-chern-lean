import GaussBonnetChern.ManifoldBoundaryStokes

/-! # Actual Stokes identities in one interior or boundary chart

These statements use the proved Euclidean Stokes formulas and actual chart
coefficients. The domain hypothesis is the local geometric equality with a
half-space; there is no assumed integral identity.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff BigOperators Topology
namespace GaussBonnetChern.LocalChartStokes
open DifferentialForm CoordinateStokes ManifoldBoundaryStokes
variable {d : ℕ}

/-- Full-space Stokes in the same Euclidean model and normalized Lebesgue
measure as the frozen manifold statement. -/
theorem stokes_euclidean_univ
    (α : EuclideanSpace ℝ (Fin (d+1)) →
      ContinuousAlternatingMap ℝ (EuclideanSpace ℝ (Fin (d+1))) ℝ (Fin d))
    (hα : ContDiff ℝ ∞ α) (hcompact : HasCompactSupport α) :
    (∫ x, extDeriv α x (EuclideanSpace.basisFun (Fin (d+1)) ℝ)) = 0 := by
  have h := stokes_univ (euclideanCoordinateForm α)
    (contDiff_euclideanCoordinateForm α hα) (hasCompactSupport_euclideanCoordinateForm α hcompact)
  have heval (x : CoordinateStokes.CoordinateSpace (d+1)) :
      extDeriv (euclideanCoordinateForm α) x (coordinateBasis (d+1)) =
        extDeriv α (toEuclidean (d+1) x) (EuclideanSpace.basisFun (Fin (d+1)) ℝ) := by
    rw [extDeriv_euclideanCoordinateForm α hα]
    change extDeriv α (toEuclidean (d+1) x)
      (fun j ↦ toEuclidean (d+1) (coordinateBasis (d+1) j)) = _
    simp only [toEuclidean_coordinateBasis]
  simp_rw [heval] at h
  have hvol := (PiLp.volume_preserving_toLp (Fin (d+1))).integral_comp
    (MeasurableEquiv.toLp 2 (Fin (d+1) → ℝ)).measurableEmbedding
    (fun x ↦ extDeriv α x (EuclideanSpace.basisFun (Fin (d+1)) ℝ))
  change (∫ x : CoordinateStokes.CoordinateSpace (d+1),
    extDeriv α (toEuclidean (d+1) x) (EuclideanSpace.basisFun (Fin (d+1)) ℝ)) = _ at hvol
  exact hvol.symm.trans h

theorem stokes_local_univ
    (s K : Set (EuclideanSpace ℝ (Fin (d+1)))) (hs : IsOpen s)
    (hK : IsCompact K) (hKs : K ⊆ s)
    (α : EuclideanSpace ℝ (Fin (d+1)) →
      ContinuousAlternatingMap ℝ (EuclideanSpace ℝ (Fin (d+1))) ℝ (Fin d))
    (hα : ContDiffOn ℝ ∞ α s) (hsupp : Function.support α ∩ s ⊆ K) :
    (∫ x in s, extDeriv α x (EuclideanSpace.basisFun (Fin (d+1)) ℝ)) = 0 := by
  classical
  have h := stokes_euclidean_univ (s.indicator α)
    (contDiff_indicator_of_compact_support s K hs hK hKs α hα hsupp)
    (hasCompactSupport_indicator_of_compact_support s K hK α hsupp)
  rw [extDeriv_indicator_eq s K hs hK hKs α hsupp] at h
  have heval (x : EuclideanSpace ℝ (Fin (d+1))) :
      (s.indicator (extDeriv α) x) (EuclideanSpace.basisFun (Fin (d+1)) ℝ) =
        s.indicator (fun x ↦ extDeriv α x (EuclideanSpace.basisFun (Fin (d+1)) ℝ)) x := by
    by_cases hx : x ∈ s <;> simp [hx]
  simp_rw [heval] at h
  rwa [integral_indicator hs.measurableSet] at h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (d+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (d+1))) ∞ M]

private theorem coordinate_support
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))))
    (α : Form 𝓘(ℝ, EuclideanSpace ℝ (Fin (d+1))) M d) (K : Set M)
    (hαK : ∀ x, x ∉ K → α x = 0) :
    Function.support (chartRepresentation e α) ∩ e.target ⊆ e '' K := by
  rintro y ⟨hyα, hy⟩
  have hxK : e.symm y ∈ K := by
    by_contra hxK
    apply hyα
    rw [chartRepresentation_eq, hαK _ hxK]
    rfl
  exact ⟨e.symm y, hxK, e.right_inv hy⟩

theorem stokes_interior_chart
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin (d+1))) ∞ M)
    (Ω : Set M) (hΩ : e.source ⊆ Ω)
    (α : Form 𝓘(ℝ, EuclideanSpace ℝ (Fin (d+1))) M d) (hα : IsSmooth α)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hαK : ∀ x, x ∉ K → α x = 0) :
    (∫ y in e.target ∩ e.symm ⁻¹' Ω,
      chartRepresentation e (exteriorDerivative α) y (EuclideanSpace.basisFun (Fin (d+1)) ℝ)) = 0 := by
  have hset : e.target ∩ e.symm ⁻¹' Ω = e.target := by
    ext y
    exact ⟨And.left, fun hy ↦ ⟨hy, hΩ (e.map_target hy)⟩⟩
  rw [hset]
  calc
    _ = ∫ y in e.target,
        extDeriv (chartRepresentation e α) y (EuclideanSpace.basisFun (Fin (d+1)) ℝ) := by
      apply setIntegral_congr_fun e.open_target.measurableSet
      intro y hy
      dsimp only
      rw [chartRepresentation_exteriorDerivative e he α hα y hy]
    _ = 0 := stokes_local_univ e.target (e '' K) e.open_target
      (hK.image_of_continuousOn (e.continuousOn.mono hKs))
      (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hKs hx))
      (chartRepresentation e α) (hα e he) (coordinate_support e α K hαK)

theorem stokes_boundary_chart
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin (d+1))) ∞ M)
    (Ω : Set M) (hΩ : ∀ x ∈ e.source, x ∈ Ω ↔ 0 ≤ e x 0)
    (α : Form 𝓘(ℝ, EuclideanSpace ℝ (Fin (d+1))) M d) (hα : IsSmooth α)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hαK : ∀ x, x ∉ K → α x = 0) :
    (∫ y in e.target ∩ e.symm ⁻¹' Ω,
      chartRepresentation e (exteriorDerivative α) y (EuclideanSpace.basisFun (Fin (d+1)) ℝ)) =
      -(∫ y in {y : CoordinateStokes.CoordinateSpace d |
          toEuclidean (d+1) (Fin.cons 0 y) ∈ e.target},
        chartRepresentation e α (toEuclidean (d+1) (Fin.cons 0 y))
          (fun j ↦ EuclideanSpace.basisFun (Fin (d+1)) ℝ j.succ)) := by
  have hset : e.target ∩ e.symm ⁻¹' Ω =
      {y : EuclideanSpace ℝ (Fin (d+1)) | 0 ≤ y 0} ∩ e.target := by
    ext y
    by_cases hy : y ∈ e.target
    · have h := hΩ (e.symm y) (e.map_target hy)
      rw [e.right_inv hy] at h
      simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, hy, true_and, and_true, h]
    · simp [hy]
  rw [hset]
  calc
    _ = ∫ y in {y : EuclideanSpace ℝ (Fin (d+1)) | 0 ≤ y 0} ∩ e.target,
        extDeriv (chartRepresentation e α) y (EuclideanSpace.basisFun (Fin (d+1)) ℝ) := by
      have h0 : Continuous (fun y : EuclideanSpace ℝ (Fin (d+1)) ↦ y 0) :=
        PiLp.continuous_apply 2 (fun _ : Fin (d+1) ↦ ℝ) 0
      apply setIntegral_congr_fun ((isClosed_le continuous_const h0).measurableSet.inter
        e.open_target.measurableSet)
      intro y hy
      dsimp only
      rw [chartRepresentation_exteriorDerivative e he α hα y hy.2]
    _ = _ := by
      have h := stokes_local_halfspace e.target (e '' K) e.open_target
        (hK.image_of_continuousOn (e.continuousOn.mono hKs))
        (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hKs hx))
        (chartRepresentation e α) (hα e he) (coordinate_support e α K hαK) (0 : Fin (d+1))
      simpa using h

end GaussBonnetChern.LocalChartStokes
