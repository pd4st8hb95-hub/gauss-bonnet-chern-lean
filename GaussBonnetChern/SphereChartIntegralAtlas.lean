import GaussBonnetChern.SphereChartIntegral
import GaussBonnetChern.SphereOrientedAtlas

/-! # Integration through actual positive finite sphere atlases

The atlas, partition and intrinsic coefficient were constructed and verified
separately. These theorems connect them, and internally supply all atlas and
partition choices for a sphere of positive dimension.
-/

noncomputable section
open Module Metric
open scoped Manifold ContDiff BigOperators

namespace GaussBonnetChern

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {d : ℕ} [Fact (finrank ℝ E = d+1)]

theorem FiniteSphereOrientedAtlas.integral_eq_sphereFormIntegral
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (a : FiniteSphereOrientedAtlas b)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (𝓡 d) (sphere (0:E) 1) Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) (hα : DifferentialForm.IsSmooth α) :
    GenericFormIntegration.integral a.chart (fun i ↦ ρ i) α = sphereFormIntegral b α := by
  apply sphereFormIntegral_eq_finite_chart_integral b a.chart a.smooth a.positive_density
    (fun i ↦ ρ i) (fun i ↦ (ρ i).contMDiff.continuous) _ _ α hα
  · intro i x hx
    exact hρ i (subset_tsupport (ρ i) hx)
  · intro u
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ u)

theorem exists_sphere_form_chart_integral
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (hd : 0 < d)
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) (hα : DifferentialForm.IsSmooth α) :
    ∃ a : FiniteSphereOrientedAtlas b,
      ∃ ρ : SmoothPartitionOfUnity (Fin a.card) (𝓡 d) (sphere (0:E) 1) Set.univ,
        ρ.IsSubordinate (fun i ↦ (a.chart i).source) ∧
        GenericFormIntegration.integral a.chart (fun i ↦ ρ i) α = sphereFormIntegral b α := by
  let a := sphereOrientedAtlas b hd
  obtain ⟨ρ,hρ⟩ := a.exists_partition b
  exact ⟨a,ρ,hρ,a.integral_eq_sphereFormIntegral b ρ hρ α hα⟩

theorem FiniteSphereOrientedAtlas.integral_independent
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (a a' : FiniteSphereOrientedAtlas b)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (𝓡 d) (sphere (0:E) 1) Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (τ : SmoothPartitionOfUnity (Fin a'.card) (𝓡 d) (sphere (0:E) 1) Set.univ)
    (hτ : τ.IsSubordinate (fun i ↦ (a'.chart i).source))
    (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) (hα : DifferentialForm.IsSmooth α) :
    GenericFormIntegration.integral a.chart (fun i ↦ ρ i) α =
      GenericFormIntegration.integral a'.chart (fun i ↦ τ i) α := by
  rw [a.integral_eq_sphereFormIntegral b ρ hρ α hα,
    a'.integral_eq_sphereFormIntegral b τ hτ α hα]

end GaussBonnetChern
