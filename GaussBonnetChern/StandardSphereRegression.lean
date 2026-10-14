import GaussBonnetChern.StandardSphereGeometry

/-! # Explicit S² and S⁴ regressions for the constructed standard geometry

Both spheres are literal Euclidean unit spheres. Their inner products come
from StandardSphereGeometry.inducedMetric, whose exact identity is the
ambient inner product paired on the actual sphere-inclusion derivatives.
Their actual outward finite atlases and subordinate smooth partitions exist.

These are instances of the uniform GBC theorem with actual singular homology.
They do not independently compute constant-curvature Pfaffians or sphere area.
Writer status: SOURCE_READY, pending root checks.
-/

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace GaussBonnetChern.StandardSphereRegression
open StandardSphereGeometry

abbrev TwoSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
abbrev FourSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1

def twoSphereAtlas : FiniteOrientedAtlas 1 TwoSphere := orientedAtlas 1 (by norm_num)
def fourSphereAtlas : FiniteOrientedAtlas 2 FourSphere := orientedAtlas 2 (by norm_num)

/-- S² uses the very same induced metric and actual outward atlas as the
uniform theorem, and every subordinate partition has curvature integral two. -/
theorem twoSphere_curvatureIntegral :
    letI : RiemannianBundle (TangentSpace (model 1) : TwoSphere → Type _) :=
      ⟨(inducedMetric 1).toRiemannianMetric⟩
    ∀ ρ : SmoothPartitionOfUnity (Fin twoSphereAtlas.card) (model 1) TwoSphere Set.univ,
      ρ.IsSubordinate (fun i ↦ (twoSphereAtlas.chart i).source) →
        curvatureIntegral 1 TwoSphere twoSphereAtlas ρ = 2 :=
  standardSphere_curvatureIntegral 1 (by norm_num)

/-- S⁴ likewise uses the constructed induced metric, not an arbitrary metric
parameter or a hypothesis stating a desired curvature value. -/
theorem fourSphere_curvatureIntegral :
    letI : RiemannianBundle (TangentSpace (model 2) : FourSphere → Type _) :=
      ⟨(inducedMetric 2).toRiemannianMetric⟩
    ∀ ρ : SmoothPartitionOfUnity (Fin fourSphereAtlas.card) (model 2) FourSphere Set.univ,
      ρ.IsSubordinate (fun i ↦ (fourSphereAtlas.chart i).source) →
        curvatureIntegral 2 FourSphere fourSphereAtlas ρ = 2 :=
  standardSphere_curvatureIntegral 2 (by norm_num)

/-- A real subordinate partition is supplied on S², so the integral regression
does not only quantify over an unconstructed family of integration data. -/
theorem twoSphere_exists_subordinate_integral :
    letI : RiemannianBundle (TangentSpace (model 1) : TwoSphere → Type _) :=
      ⟨(inducedMetric 1).toRiemannianMetric⟩
    ∃ ρ : SmoothPartitionOfUnity (Fin twoSphereAtlas.card) (model 1) TwoSphere Set.univ,
      ρ.IsSubordinate (fun i ↦ (twoSphereAtlas.chart i).source) ∧
        curvatureIntegral 1 TwoSphere twoSphereAtlas ρ = 2 := by
  letI : RiemannianBundle (TangentSpace (model 1) : TwoSphere → Type _) :=
    ⟨(inducedMetric 1).toRiemannianMetric⟩
  obtain ⟨ρ, hρ⟩ := orientedAtlas_exists_partition 1 (by norm_num)
  exact ⟨ρ, hρ, twoSphere_curvatureIntegral ρ hρ⟩

/-- The corresponding actual subordinate integration data also exist on S⁴. -/
theorem fourSphere_exists_subordinate_integral :
    letI : RiemannianBundle (TangentSpace (model 2) : FourSphere → Type _) :=
      ⟨(inducedMetric 2).toRiemannianMetric⟩
    ∃ ρ : SmoothPartitionOfUnity (Fin fourSphereAtlas.card) (model 2) FourSphere Set.univ,
      ρ.IsSubordinate (fun i ↦ (fourSphereAtlas.chart i).source) ∧
        curvatureIntegral 2 FourSphere fourSphereAtlas ρ = 2 := by
  letI : RiemannianBundle (TangentSpace (model 2) : FourSphere → Type _) :=
    ⟨(inducedMetric 2).toRiemannianMetric⟩
  obtain ⟨ρ, hρ⟩ := orientedAtlas_exists_partition 2 (by norm_num)
  exact ⟨ρ, hρ, fourSphere_curvatureIntegral ρ hρ⟩

end GaussBonnetChern.StandardSphereRegression
