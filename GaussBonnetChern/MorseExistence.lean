import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import GaussBonnetChern.NormalEndpoint
import GaussBonnetChern.ImmersionGraphCharts

/-! # Squared distances along the actual compact Euclidean embedding

The family used in the Morse-existence argument is the squared ambient
distance to a parameter. Criticality is proved equivalent to orthogonality to
the actual derivative image. The normal bundle below is its genuine carrier;
its smooth local parametrizations are a separate proof obligation.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace GaussBonnetChern.Morse

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def squaredDistance (e : M → F) (a : F) (x : M) : ℝ := ‖e x - a‖ ^ 2

theorem contMDiff_squaredDistance {e : M → F}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (a : F) :
    ContMDiff I 𝓘(ℝ) ∞ (squaredDistance e a) :=
  (contDiff_norm_sq ℝ).contMDiff.comp (he.sub contMDiff_const)

theorem mvfderiv_squaredDistance {e : M → F} {x : M}
    (he : MDifferentiableAt I 𝓘(ℝ, F) e x) (a : F) :
    mvfderiv I (squaredDistance e a) x =
      (2 : ℝ) • (innerSL ℝ (e x - a)).comp (mvfderiv I e x) := by
  change mvfderiv I ((fun y : F => ‖y‖ ^ 2) ∘ (e - fun _ => a)) x = _
  rw [mvfderiv_comp x (hasStrictFDerivAt_norm_sq (e x - a)).differentiableAt.mdifferentiableAt
    (he.sub mdifferentiableAt_const)]
  rw [mvfderiv_eq_fderiv, fderiv_norm_sq_apply]
  ext v
  simp [two_smul, mvfderiv, mfderiv_sub he mdifferentiableAt_const]
  change
    (inner ℝ (e x) (mvfderiv I e x v - 0) - inner ℝ a (mvfderiv I e x v - 0)) +
      (inner ℝ (e x) (mvfderiv I e x v - 0) - inner ℝ a (mvfderiv I e x v - 0)) = _
  simp only [sub_zero]
  rfl

/-- The ambient orthogonal complement of the actual derivative image. -/
def normalSpace (e : M → F) (x : M) : Submodule ℝ F :=
  (LinearMap.range (mvfderiv I e x).toLinearMap)ᗮ

theorem mem_normalSpace_iff {e : M → F} {x : M} {v : F} :
    v ∈ normalSpace (I := I) e x ↔
      ∀ u : TangentSpace I x, inner ℝ (mvfderiv I e x u) v = 0 := by
  simp [normalSpace, Submodule.mem_orthogonal, LinearMap.mem_range]

theorem critical_squaredDistance_iff_normal {e : M → F} {x : M}
    (he : MDifferentiableAt I 𝓘(ℝ, F) e x) (a : F) :
    mvfderiv I (squaredDistance e a) x = 0 ↔ a - e x ∈ normalSpace (I := I) e x := by
  rw [mvfderiv_squaredDistance he, mem_normalSpace_iff]
  constructor
  · intro h u
    have hu := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L u) h
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, smul_eq_mul, ContinuousLinearMap.zero_apply] at hu
    rw [inner_sub_left] at hu
    rw [inner_sub_right, real_inner_comm a (mvfderiv I e x u),
      real_inner_comm (e x) (mvfderiv I e x u)]
    linarith
  · intro h
    ext u
    have hu := h u
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, smul_eq_mul, ContinuousLinearMap.zero_apply]
    rw [inner_sub_right] at hu
    rw [inner_sub_left, real_inner_comm (mvfderiv I e x u) (e x),
      real_inner_comm (mvfderiv I e x u) a]
    linarith

/-- Carrier of the normal bundle of `e`, before constructing its smooth atlas. -/
def NormalBundle (e : M → F) := (x : M) × normalSpace (I := I) e x

def normalEndpoint (e : M → F) (z : NormalBundle (I := I) e) : F := e z.1 + z.2

theorem critical_of_normalEndpoint {e : M → F} (z : NormalBundle (I := I) e)
    (he : MDifferentiableAt I 𝓘(ℝ, F) e z.1) :
    mvfderiv I (squaredDistance e (normalEndpoint e z)) z.1 = 0 := by
  rw [critical_squaredDistance_iff_normal he]
  simpa [normalEndpoint] using z.2.property

theorem exists_normalEndpoint_of_critical {e : M → F} {x : M} {a : F}
    (he : MDifferentiableAt I 𝓘(ℝ, F) e x)
    (hcrit : mvfderiv I (squaredDistance e a) x = 0) :
    ∃ z : NormalBundle (I := I) e, z.1 = x ∧ normalEndpoint e z = a := by
  refine ⟨⟨x, ⟨a - e x, (critical_squaredDistance_iff_normal he a).mp hcrit⟩⟩, rfl, ?_⟩
  simp [normalEndpoint]

/-- The existing compact embedding theorem provides the smooth map and its
injective differential required by the squared-distance construction. -/
theorem exists_compact_embedding [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] :
    ∃ (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N)),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ e ∧ IsClosedEmbedding e ∧
      ∀ x, Function.Injective (mvfderiv I e x) := by
  obtain ⟨N, e, hs, ht, hd⟩ := exists_embedding_euclidean_of_compact (I := I) (M := M)
  exact ⟨N, e, hs, ht, hd⟩


open Filter MeasureTheory MeasureTheory.Measure

section Global

variable {E A M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M]

theorem exists_distance_parameter_nondegenerate_graph_charts
    (μ : Measure A) [IsAddHaarMeasure μ] {e : M → A}
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, A) ∞ e)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, A) e x)) :
    ∃ (a : A) (Γ : Finset (OrthogonalGraphChart (E := E) e)),
      (∀ x, ∃ q ∈ Γ, x ∈ q.chart.source) ∧
      ∀ q ∈ Γ, ∀ x ∈ q.chart.source,
        mvfderiv 𝓘(ℝ, E) (squaredDistance e a) x = 0 →
        Injective (fderiv ℝ (fderiv ℝ ((squaredDistance e a) ∘ q.chart.symm)) (q.chart x)) := by
  classical
  obtain ⟨Γ, hΓ⟩ := exists_finite_orthogonalGraphCharts he hi
  let U : Γ → Type _ := fun q => q.val.tangent
  let V : Γ → Type _ := fun q => q.val.tangentᗮ
  let r : ∀ q : Γ, A ≃ₗᵢ[ℝ] WithLp 2 (U q × V q) :=
    fun q => q.val.tangent.orthogonalDecomposition
  obtain ⟨a, ha⟩ := exists_nondegenerate_isometric_graphs μ U V r
    (fun q => q.val.graph) (fun q => q.val.chart.target)
    (fun q u hu => ((q.val.smooth_graph u hu).contDiffAt
      (q.val.chart.open_target.mem_nhds hu)).of_le (by simp))
  refine ⟨a, Γ, hΓ, ?_⟩
  intro q hq x hx hcrit
  let qi : Γ := ⟨q, hq⟩
  let u := q.chart x
  have hu : u ∈ q.chart.target := q.chart.map_source hx
  have hfun : (squaredDistance e a) ∘ q.chart.symm =ᶠ[𝓝 u]
      graphSquaredDistance q.graph (WithLp.ofLp (r qi a)) := by
    filter_upwards [q.chart.open_target.mem_nhds hu] with y hy
    exact squaredDistance_in_isometric_graph (r qi) q.graph (e (q.chart.symm y)) a y
      (q.graph_eq y hy)
  have hInv : MDifferentiableAt 𝓘(ℝ, q.tangent) 𝓘(ℝ, E) q.chart.symm u :=
    ((q.smooth_inverse u hu).contMDiffAt (q.chart.open_target.mem_nhds hu)).mdifferentiableAt (by simp)
  have hf := contMDiff_squaredDistance he a
  have hdf := mvfderiv_comp u ((hf (q.chart.symm u)).mdifferentiableAt (by simp)) hInv
  have hzero : mvfderiv 𝓘(ℝ, E) (squaredDistance e a) (q.chart.symm u) = 0 := by
    have hxu : q.chart.symm u = x := q.chart.left_inv hx
    rw [hxu]
    exact hcrit
  rw [hzero, ContinuousLinearMap.zero_comp, mvfderiv_eq_fderiv] at hdf
  have hgraph : fderiv ℝ (graphSquaredDistance q.graph (WithLp.ofLp (r qi a))) u = 0 := by
    rw [← hfun.fderiv_eq]
    exact hdf
  have hH := ha qi u hu hgraph
  rw [hfun.fderiv.fderiv_eq]
  exact hH


end Global

/-- A compact smooth manifold admits a smooth function with nondegenerate
critical points, expressed in genuine smooth graph coordinates. The map,
distance parameter, and finite coordinate cover are all constructed internally. -/
theorem exists_smooth_function_nondegenerate_graph_charts
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] :
    ∃ (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N)) (a : EuclideanSpace ℝ (Fin N))
      (Γ : Finset (OrthogonalGraphChart (E := E) e)),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (squaredDistance e a) ∧
      (∀ x, ∃ q ∈ Γ, x ∈ q.chart.source) ∧
      ∀ q ∈ Γ, ∀ x ∈ q.chart.source,
        mvfderiv 𝓘(ℝ, E) (squaredDistance e a) x = 0 →
        Injective (fderiv ℝ (fderiv ℝ ((squaredDistance e a) ∘ q.chart.symm)) (q.chart x)) := by
  obtain ⟨N, e, he, _, hi⟩ := exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)
  obtain ⟨a, Γ, hΓ, hH⟩ := exists_distance_parameter_nondegenerate_graph_charts volume he hi
  exact ⟨N, e, a, Γ, contMDiff_squaredDistance he a, hΓ, hH⟩

end GaussBonnetChern.Morse


