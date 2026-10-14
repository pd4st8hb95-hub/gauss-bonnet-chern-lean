import GaussBonnetChern.CurvatureTensor
import GaussBonnetChern.NormalizationRegression

/-! # The two-dimensional normalization of the original Euler density

This specializes the frozen, all-dimensional definition to an actual
Levi-Civita curvature component. It is a normalization check, not the
Gauss--Bonnet theorem for surfaces.
-/

noncomputable section
open Bundle
open scoped Manifold ContDiff
namespace GaussBonnetChern
universe u

theorem eulerDensity_surface (M : Type u) [TopologicalSpace M] [ChartedSpace (Model 1) M]
    [IsManifold (model 1) ∞ M]
    [RiemannianBundle (TangentSpace (model 1) : M → Type _)]
    [IsContMDiffRiemannianBundle (model 1) ∞ (Model 1) (TangentSpace (model 1) : M → Type _)]
    (x : M) : eulerDensity 1 M x = curvatureComponents 1 M x 0 1 0 1 / (2 * Real.pi) :=
  eulerScalar_one_of_skew (curvatureComponents 1 M x)
    (fun a b i j ↦ curvatureComponents_swap_frame 1 M x b a i j)
    (fun a b i j ↦ curvatureComponents_swap_directions 1 M x a b j i)

end GaussBonnetChern
