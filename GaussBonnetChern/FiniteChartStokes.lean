import GaussBonnetChern.StokesLocalization
import GaussBonnetChern.LocalChartStokes

/-! # Stokes assembled from a finite collection of actual adapted charts

The chart-position fields describe only the subset in coordinates. Every
integral identity is proved from coordinate Stokes and finite localization.
Construction of these charts for the punctured domain is a separate geometric
step; no Stokes formula is assumed in the data.
-/

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace GaussBonnetChern.FiniteChartStokes
open DifferentialForm CoordinateStokes ManifoldBoundaryStokes StokesLocalization

inductive ChartPosition where
  | outside
  | interior
  | boundary

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Model (n+1)) M]
  [IsManifold (model (n+1)) ∞ M]

/-- A finite positive smooth atlas with an actual local description of the
closed integration domain in every chart. -/
structure AdaptedAtlas (Ω : Set M) where
  atlas : FiniteOrientedAtlas (n+1) M
  position : Fin atlas.card → ChartPosition
  domain : ∀ i (x : M), x ∈ (atlas.chart i).source →
    match position i with
    | .outside => x ∉ Ω
    | .interior => x ∈ Ω
    | .boundary => x ∈ Ω ↔ 0 ≤ atlas.chart i x 0

/-- The induced outward flux in a height-first chart for the domain height≥0.
The minus sign is the lower face's outward-normal-first orientation. -/
def lowerFaceIntegral (e : OpenPartialHomeomorph M (Model (n+1)))
    (α : Form (model (n+1)) M (2*n+1)) : ℝ :=
  -(∫ y in {y : CoordinateStokes.CoordinateSpace (2*n+1) |
      toEuclidean (2*n+1+1) (Fin.cons 0 y) ∈ e.target},
    chartRepresentation e α (toEuclidean (2*n+1+1) (Fin.cons 0 y))
      (fun j ↦ EuclideanSpace.basisFun (Fin (2*n+1+1)) ℝ j.succ))

theorem topFormCoefficient_sum {ι : Type*} (s : Finset ι)
    (e : OpenPartialHomeomorph M (Model (n+1)))
    (α : ι → Form (model (n+1)) M (2*(n+1))) (y : Model (n+1)) :
    topFormCoefficient e (∑ i ∈ s, α i) y = ∑ i ∈ s, topFormCoefficient e (α i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, topFormCoefficient_add]
    exact congrArg (fun z ↦ topFormCoefficient e (α i) y + z) ih

theorem integralTopFormOn_sum [CompactSpace M] {ι : Type*} [Fintype ι]
    (a : FiniteOrientedAtlas (n+1) M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model (n+1)) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (Ω : Set M) (α : ι → Form (model (n+1)) M (2*(n+1)))
    (hα : ∀ i, IsSmooth (α i)) :
    integralTopFormOn a ρ Ω (∑ i, α i) = ∑ i, integralTopFormOn a ρ Ω (α i) := by
  classical
  simp only [integralTopFormOn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    simp only [topFormIntegrand, topFormCoefficient_sum, Finset.mul_sum]
  · intro i _
    exact integrableOn_topFormIntegrand_chartDomain a ρ hρ Ω (α i) (hα i) j

/-- Each localized form satisfies Stokes in its actual adapted chart. -/
theorem integral_localized_piece [CompactSpace M]
    (Ω : Set M) (hΩ : IsClosed Ω) (a : AdaptedAtlas (n := n) Ω)
    (ρ : SmoothPartitionOfUnity (Fin a.atlas.card) (model (n+1)) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.atlas.chart i).source))
    (α : Form (model (n+1)) M (2*n+1)) (hα : IsSmooth α) (i : Fin a.atlas.card) :
    integralTopFormOn a.atlas ρ Ω (exteriorDerivative (weightForm (ρ i) α)) =
      match a.position i with
      | .outside => 0
      | .interior => 0
      | .boundary => lowerFaceIntegral (a.atlas.chart i) (weightForm (ρ i) α) := by
  have hpiece : IsSmooth (weightForm (ρ i) α) := isSmooth_weightForm (ρ i) (ρ i).contMDiff α hα
  have hsupport : ∀ x, x ∉ tsupport (ρ i) →
      exteriorDerivative (weightForm (ρ i) α) x = 0 :=
    exteriorDerivative_weightForm_eq_zero_of_notMem_tsupport (ρ i) α
  rw [integralTopFormOn_eq_single_chart a.atlas ρ hρ (a.atlas.chart i) (a.atlas.smooth i)
    (fun j x hxj hxi ↦ a.atlas.positive_transition j i x hxj hxi)
    Ω hΩ _ hpiece.exteriorDerivative (tsupport (ρ i)) (isClosed_tsupport _).isCompact (hρ i) hsupport]
  have hsupportα : ∀ x, x ∉ tsupport (ρ i) → weightForm (ρ i) α x = 0 := by
    intro x hx
    simp [weightForm, image_eq_zero_of_notMem_tsupport hx]
  cases hp : a.position i with
  | outside =>
    have hempty : chartDomain (a.atlas.chart i) Ω = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      have h := a.domain i ((a.atlas.chart i).symm y) ((a.atlas.chart i).map_target hy.1)
      rw [hp] at h
      exact h hy.2
    simp [hempty]
  | interior =>
    have hinside : (a.atlas.chart i).source ⊆ Ω := by
      intro x hx
      simpa [hp] using a.domain i x hx
    exact LocalChartStokes.stokes_interior_chart (a.atlas.chart i) (a.atlas.smooth i)
      Ω hinside _ hpiece (tsupport (ρ i)) (isClosed_tsupport _).isCompact (hρ i) hsupportα
  | boundary =>
    have hboundary : ∀ x ∈ (a.atlas.chart i).source, x ∈ Ω ↔ 0 ≤ a.atlas.chart i x 0 := by
      intro x hx
      simpa [hp] using a.domain i x hx
    exact LocalChartStokes.stokes_boundary_chart (a.atlas.chart i) (a.atlas.smooth i)
      Ω hboundary _ hpiece (tsupport (ρ i)) (isClosed_tsupport _).isCompact (hρ i) hsupportα

/-- Finite Stokes for actual adapted charts and a subordinate smooth partition.
This identity is deduced entirely from local Stokes, with no integral premise. -/
theorem stokes_finite_adapted_atlas [CompactSpace M]
    (Ω : Set M) (hΩ : IsClosed Ω) (a : AdaptedAtlas (n := n) Ω)
    (ρ : SmoothPartitionOfUnity (Fin a.atlas.card) (model (n+1)) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.atlas.chart i).source))
    (α : Form (model (n+1)) M (2*n+1)) (hα : IsSmooth α) :
    integralTopFormOn a.atlas ρ Ω (exteriorDerivative α) =
      ∑ i, match a.position i with
        | .outside => 0
        | .interior => 0
        | .boundary => lowerFaceIntegral (a.atlas.chart i) (weightForm (ρ i) α) := by
  classical
  have hsum : ∀ x, ∑ i, ρ i x = 1 := by
    intro x
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  rw [← sum_exteriorDerivative_weightForm (fun i ↦ ρ i) hsum (fun i ↦ (ρ i).contMDiff) α hα]
  rw [integralTopFormOn_sum a.atlas ρ hρ Ω _
    (fun i ↦ (isSmooth_weightForm (ρ i) (ρ i).contMDiff α hα).exteriorDerivative)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_localized_piece Ω hΩ a ρ hρ α hα i

theorem integralTopFormOn_congr
    (a : FiniteOrientedAtlas (n+1) M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model (n+1)) M univ)
    (Ω : Set M) (hΩ : IsClosed Ω)
    (α β : Form (model (n+1)) M (2*(n+1))) (h : ∀ x ∈ Ω, α x = β x) :
    integralTopFormOn a ρ Ω α = integralTopFormOn a ρ Ω β := by
  unfold integralTopFormOn
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun (measurableSet_chartDomain (a.chart i) Ω hΩ)
  intro y hy
  dsimp only [topFormIntegrand, topFormCoefficient]
  rw [chartRepresentation_eq, chartRepresentation_eq, h _ hy.2]

theorem lowerFaceIntegral_congr
    (e : OpenPartialHomeomorph M (Model (n+1))) (Ω : Set M)
    (hΩ : ∀ x ∈ e.source, x ∈ Ω ↔ 0 ≤ e x 0)
    (α β : Form (model (n+1)) M (2*n+1)) (h : ∀ x ∈ Ω, α x = β x) :
    lowerFaceIntegral e α = lowerFaceIntegral e β := by
  have hinc : Continuous (fun y : CoordinateStokes.CoordinateSpace (2*n+1) ↦
      toEuclidean (2*n+1+1) (Fin.cons 0 y)) := by
    have hcons : Continuous (fun z : CoordinateStokes.CoordinateSpace (2*n+1) ↦
        (Fin.cons (0 : ℝ) z : CoordinateStokes.CoordinateSpace (2*n+1+1))) := by
      simpa only [Fin.insertNth_zero'] using
        (contDiff_faceInclusion (0 : Fin (2*n+1+1)) 0).continuous
    exact (toEuclidean (2*n+1+1)).continuous.comp
      hcons
  unfold lowerFaceIntegral
  congr 1
  apply setIntegral_congr_fun (e.open_target.preimage hinc).measurableSet
  intro y hy
  have hxΩ : e.symm (toEuclidean (2*n+1+1) (Fin.cons 0 y)) ∈ Ω := by
    apply (hΩ _ (e.map_target hy)).mpr
    rw [e.right_inv hy]
    change (0 : ℝ) ≤ 0
    exact le_rfl
  dsimp only
  rw [chartRepresentation_eq, chartRepresentation_eq, h _ hxΩ]

/-- The finite-chart formula also holds for a form smooth only near the
closed domain. The global smooth representative is constructed internally. -/
theorem stokes_finite_adapted_atlas_of_local_smooth [CompactSpace M] [T2Space M]
    (Ω U : Set M) (hΩ : IsClosed Ω) (hU : IsOpen U) (hΩU : Ω ⊆ U)
    (a : AdaptedAtlas (n := n) Ω)
    (ρ : SmoothPartitionOfUnity (Fin a.atlas.card) (model (n+1)) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.atlas.chart i).source))
    (α : Form (model (n+1)) M (2*n+1))
    (hα : ∀ x ∈ U, IsSmoothAtInCharts α x) :
    integralTopFormOn a.atlas ρ Ω (exteriorDerivative α) =
      ∑ i, match a.position i with
        | .outside => 0
        | .interior => 0
        | .boundary => lowerFaceIntegral (a.atlas.chart i) (weightForm (ρ i) α) := by
  classical
  obtain ⟨β, hβ, hgerm, hderiv⟩ :=
    exists_global_smooth_form_eq_near_closed_domain Ω U hΩ hU hΩU α hα
  rw [← integralTopFormOn_congr a.atlas ρ Ω hΩ (exteriorDerivative β)
    (exteriorDerivative α) hderiv, stokes_finite_adapted_atlas Ω hΩ a ρ hρ β hβ]
  apply Finset.sum_congr rfl
  intro i _
  cases hp : a.position i with
  | outside => rfl
  | interior => rfl
  | boundary =>
    apply lowerFaceIntegral_congr (a.atlas.chart i) Ω
      (fun x hx ↦ by simpa [hp] using a.domain i x hx)
    intro x hx
    exact congrArg (fun η ↦ ρ i x • η) ((hgerm x hx).self_of_nhds)

end GaussBonnetChern.FiniteChartStokes
