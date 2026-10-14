import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.LinearAlgebra.Determinant
import GaussBonnetChern.EqualDimSard

/-! # Normal endpoint maps in graph coordinates

For a graph `(x,g x)`, all normal vectors have the form `(-Dg(x)† v,v)`.
The endpoint map is therefore `(x - Dg(x)† v, g x + v)`.  Its derivative
and the half Hessian of squared distance have the same kernel after eliminating
the normal variable. All derivatives in the analytic lemmas are actual
Fréchet derivatives.
-/

noncomputable section

open Function Filter
open scoped Topology
open scoped InnerProduct

namespace GaussBonnetChern.Morse

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace E] [CompleteSpace F]

def adjointReal : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
  ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem adjointReal_apply (L : E →L[ℝ] F) : adjointReal L = L† := rfl

def secondAdjoint (B : E →L[ℝ] E →L[ℝ] F) (v : F) : E →L[ℝ] E :=
  (adjointReal.comp B).flip v

@[simp] theorem secondAdjoint_apply (B : E →L[ℝ] E →L[ℝ] F) (v : F) (u : E) :
    secondAdjoint B v u = ((B u)†) v := rfl

/-- Half of the distance Hessian at the endpoint determined by `v`. -/
def graphHessianOperator (L : E →L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] F) (v : F) :
    E →L[ℝ] E := ContinuousLinearMap.id ℝ E + (L†).comp L - secondAdjoint B v

@[simp] theorem graphHessianOperator_apply (L : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) (v : F) (u : E) :
    graphHessianOperator L B v u = u + (L†) (L u) - ((B u)†) v := rfl

def graphEndpointDerivative (L : E →L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] F) (v : F) :
    (E × F) →L[ℝ] (E × F) :=
  ((ContinuousLinearMap.fst ℝ E F - (secondAdjoint B v).comp
      (ContinuousLinearMap.fst ℝ E F)) - (L†).comp (ContinuousLinearMap.snd ℝ E F)).prod
    (L.comp (ContinuousLinearMap.fst ℝ E F) + ContinuousLinearMap.snd ℝ E F)

@[simp] theorem graphEndpointDerivative_apply (L : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) (v : F) (z : E × F) :
    graphEndpointDerivative L B v z = (z.1 - ((B z.1)†) v - (L†) z.2, L z.1 + z.2) := rfl

theorem graphEndpointDerivative_eq_zero_iff (L : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) (v : F) (u : E) (w : F) :
    graphEndpointDerivative L B v (u, w) = 0 ↔
      w = -L u ∧ graphHessianOperator L B v u = 0 := by
  change (u - ((B u)†) v - (L†) w, L u + w) = ((0 : E), (0 : F)) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hw : w = -L u := eq_neg_of_add_eq_zero_right h₂
    refine ⟨hw, ?_⟩
    rw [hw, map_neg] at h₁
    simp only [graphHessianOperator_apply]
    calc
      u + (L†) (L u) - ((B u)†) v = u - ((B u)†) v - -(L†) (L u) := by abel
      _ = 0 := h₁
  · rintro ⟨rfl, h⟩
    refine ⟨?_, by simp⟩
    rw [map_neg]
    simpa only [graphHessianOperator_apply, sub_neg_eq_add, sub_add_eq_add_sub] using h

theorem graphEndpointDerivative_injective_iff (L : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) (v : F) :
    Injective (graphEndpointDerivative L B v) ↔ Injective (graphHessianOperator L B v) := by
  change Injective (graphEndpointDerivative L B v).toLinearMap ↔
    Injective (graphHessianOperator L B v).toLinearMap
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot]
  simp only [LinearMap.ker_eq_bot']
  constructor
  · intro h u hu
    have hz := h (u, -L u) ((graphEndpointDerivative_eq_zero_iff L B v u (-L u)).mpr ⟨rfl, hu⟩)
    exact congrArg Prod.fst hz
  · intro h z hz
    obtain ⟨hw, hu⟩ := (graphEndpointDerivative_eq_zero_iff L B v z.1 z.2).mp hz
    have hx := h z.1 hu
    ext <;> simp [hx, hw]

theorem graphEndpointDerivative_det_ne_zero_iff [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (L : E →L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] F) (v : F) :
    (graphEndpointDerivative L B v).det ≠ 0 ↔ (graphHessianOperator L B v).det ≠ 0 := by
  have h₁ : (graphEndpointDerivative L B v).det ≠ 0 ↔
      Injective (graphEndpointDerivative L B v) := by
    have h := not_congr (LinearMap.det_eq_zero_iff_ker_ne_bot
      (f := (graphEndpointDerivative L B v).toLinearMap))
    simpa only [ContinuousLinearMap.det, not_not, LinearMap.ker_eq_bot] using! h
  have h₂ : (graphHessianOperator L B v).det ≠ 0 ↔
      Injective (graphHessianOperator L B v) := by
    have h := not_congr (LinearMap.det_eq_zero_iff_ker_ne_bot
      (f := (graphHessianOperator L B v).toLinearMap))
    simpa only [ContinuousLinearMap.det, not_not, LinearMap.ker_eq_bot] using! h
  rw [h₁, h₂]
  exact graphEndpointDerivative_injective_iff L B v

/-- Actual normal endpoint map of the graph of `g`. -/
def graphNormalEndpoint (g : E → F) (z : E × F) : E × F :=
  (z.1 - ((fderiv ℝ g z.1)†) z.2, g z.1 + z.2)

/-- Ambient squared distance restricted to the graph. The ambient Euclidean
norm squared is the sum of the two factor norms squared. -/
def graphSquaredDistance (g : E → F) (a : E × F) (x : E) : ℝ :=
  ‖x - a.1‖ ^ 2 + ‖g x - a.2‖ ^ 2

theorem graphSquaredDistance_eq_norm_sq (g : E → F) (a : E × F) (x : E) :
    graphSquaredDistance g a x =
      ‖WithLp.toLp 2 (x, g x) - WithLp.toLp 2 a‖ ^ 2 := by
  simp [graphSquaredDistance, WithLp.prod_norm_sq_eq_of_L2]

theorem squaredDistance_in_isometric_graph {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] (r : A ≃ₗᵢ[ℝ] WithLp 2 (E × F))
    (g : E → F) (p a : A) (x : E) (hp : r p = WithLp.toLp 2 (x, g x)) :
    ‖p - a‖ ^ 2 = graphSquaredDistance g (WithLp.ofLp (r a)) x := by
  rw [graphSquaredDistance_eq_norm_sq, ← r.norm_map (p - a), map_sub, hp]

theorem graph_normal_orthogonal (L : E →L[ℝ] F) (v : F) (u : E) :
    inner ℝ (-(L†) v) u + inner ℝ v (L u) = 0 := by
  rw [inner_neg_left, ContinuousLinearMap.adjoint_inner_left]
  simp

/-- The Riesz representative of half the actual graph distance differential. -/
def graphHalfGradient (g : E → F) (a : E × F) (x : E) : E :=
  x - a.1 + ((fderiv ℝ g x)†) (g x - a.2)

theorem graphHalfGradient_endpoint (g : E → F) (x : E) (v : F) :
    graphHalfGradient g (graphNormalEndpoint g (x, v)) x = 0 := by
  simp [graphHalfGradient, graphNormalEndpoint]

theorem fderiv_graphSquaredDistance {g : E → F} {x : E}
    (hg : DifferentiableAt ℝ g x) (a : E × F) :
    fderiv ℝ (graphSquaredDistance g a) x = (2 : ℝ) • innerSL ℝ (graphHalfGradient g a x) := by
  have hd := (((hasFDerivAt_id x).sub_const a.1).norm_sq).add
    ((hg.hasFDerivAt.sub_const a.2).norm_sq)
  change fderiv ℝ ((fun y => ‖id y - a.1‖ ^ 2) + (fun y => ‖g y - a.2‖ ^ 2)) x = _
  rw [hd.fderiv]
  ext u
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
    smul_eq_mul, graphHalfGradient, inner_add_left, ContinuousLinearMap.adjoint_inner_left, id_eq]
  ring

theorem critical_graphSquaredDistance_iff {g : E → F} {x : E}
    (hg : DifferentiableAt ℝ g x) (a : E × F) :
    fderiv ℝ (graphSquaredDistance g a) x = 0 ↔ graphHalfGradient g a x = 0 := by
  rw [fderiv_graphSquaredDistance hg]
  constructor
  · intro h
    have hu := congrArg (fun L : E →L[ℝ] ℝ => L (graphHalfGradient g a x)) h
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
      ContinuousLinearMap.zero_apply] at hu
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp (by linarith)
  · intro h
    simp [h]

theorem hasFDerivAt_graphHalfGradient_endpoint {g : E → F} {x : E}
    (hg : DifferentiableAt ℝ g x) {B : E →L[ℝ] E →L[ℝ] F}
    (hB : HasFDerivAt (fderiv ℝ g) B x) (v : F) :
    HasFDerivAt (graphHalfGradient g (graphNormalEndpoint g (x, v)))
      (graphHessianOperator (fderiv ℝ g x) B v) x := by
  have ha := (adjointReal (E := E) (F := F)).hasFDerivAt.comp x hB
  have hp := ha.clm_apply (hg.hasFDerivAt.sub_const (g x + v))
  convert ((hasFDerivAt_id x).sub_const (x - ((fderiv ℝ g x)†) v)).add hp using 1
  · rfl
  · ext u
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      adjointReal_apply, graphHessianOperator_apply]
    simp only [Function.comp_apply, adjointReal_apply, sub_add_cancel_left, map_neg]
    abel

theorem hasFDerivAt_graphNormalEndpoint {g : E → F} {x : E}
    (hg : DifferentiableAt ℝ g x) {B : E →L[ℝ] E →L[ℝ] F}
    (hB : HasFDerivAt (fderiv ℝ g) B x) (v : F) :
    HasFDerivAt (graphNormalEndpoint g)
      (graphEndpointDerivative (fderiv ℝ g x) B v) (x, v) := by
  let p : E × F →L[ℝ] E := ContinuousLinearMap.fst ℝ E F
  let q : E × F →L[ℝ] F := ContinuousLinearMap.snd ℝ E F
  have ha := (adjointReal (E := E) (F := F)).hasFDerivAt.comp (x, v)
    (hB.comp (x, v) p.hasFDerivAt)
  have hp := ha.clm_apply q.hasFDerivAt
  have hg' := hg.hasFDerivAt.comp (x, v) p.hasFDerivAt
  convert (p.hasFDerivAt.sub hp).prodMk (hg'.add q.hasFDerivAt) using 1
  · rfl
  · ext z <;> simp [graphEndpointDerivative, secondAdjoint, p, q, sub_add_eq_sub_sub]

theorem fderiv_graphNormalEndpoint_injective_iff {g : E → F} {x : E}
    (hg : DifferentiableAt ℝ g x) {B : E →L[ℝ] E →L[ℝ] F}
    (hB : HasFDerivAt (fderiv ℝ g) B x) (v : F) :
    Injective (fderiv ℝ (graphNormalEndpoint g) (x, v)) ↔
      Injective (fderiv ℝ (graphHalfGradient g (graphNormalEndpoint g (x, v))) x) := by
  rw [(hasFDerivAt_graphNormalEndpoint hg hB v).fderiv,
    (hasFDerivAt_graphHalfGradient_endpoint hg hB v).fderiv]
  exact graphEndpointDerivative_injective_iff _ _ _

theorem graphNormalEndpoint_of_critical {g : E → F} {x : E} {a : E × F}
    (hg : DifferentiableAt ℝ g x)
    (hcrit : fderiv ℝ (graphSquaredDistance g a) x = 0) :
    graphNormalEndpoint g (x, a.2 - g x) = a := by
  have h := (critical_graphSquaredDistance_iff hg a).mp hcrit
  change x - a.1 + ((fderiv ℝ g x)†) (g x - a.2) = 0 at h
  apply Prod.ext
  · change x - ((fderiv ℝ g x)†) (a.2 - g x) = a.1
    rw [map_sub] at h ⊢
    apply sub_eq_zero.mp
    calc
      (x - (((fderiv ℝ g x)†) a.2 - ((fderiv ℝ g x)†) (g x))) - a.1 =
          x - a.1 + (((fderiv ℝ g x)†) (g x) - ((fderiv ℝ g x)†) a.2) := by abel
      _ = 0 := h
  · simp [graphNormalEndpoint]

/-- Twice the Riesz map, so that the actual differential of squared distance
is this bounded linear map applied to the half gradient. -/
def twiceInner : E →L[ℝ] (E →L[ℝ] ℝ) := (2 : ℝ) • innerSL ℝ

theorem twiceInner_injective : Injective (twiceInner (E := E)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro u hu
  have h := congrArg (fun L : E →L[ℝ] ℝ => L u) hu
  change 2 * inner ℝ u u = 0 at h
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (by linarith)

theorem hasFDerivAt_fderiv_graphSquaredDistance_endpoint {g : E → F} {x : E}
    (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y) {B : E →L[ℝ] E →L[ℝ] F}
    (hB : HasFDerivAt (fderiv ℝ g) B x) (v : F) :
    HasFDerivAt (fderiv ℝ (graphSquaredDistance g (graphNormalEndpoint g (x, v))))
      (twiceInner.comp (graphHessianOperator (fderiv ℝ g x) B v)) x := by
  have hfun : fderiv ℝ (graphSquaredDistance g (graphNormalEndpoint g (x, v))) =ᶠ[𝓝 x]
      twiceInner ∘ graphHalfGradient g (graphNormalEndpoint g (x, v)) := by
    filter_upwards [hg] with y hy
    exact fderiv_graphSquaredDistance hy _
  exact (twiceInner.hasFDerivAt.comp x
    (hasFDerivAt_graphHalfGradient_endpoint hg.self_of_nhds hB v)).congr_of_eventuallyEq hfun

/-- The actual distance Hessian is nondegenerate exactly when the actual
normal endpoint derivative is injective. -/
theorem hessian_graphSquaredDistance_endpoint_injective_iff {g : E → F} {x : E}
    (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y) {B : E →L[ℝ] E →L[ℝ] F}
    (hB : HasFDerivAt (fderiv ℝ g) B x) (v : F) :
    Injective (fderiv ℝ (fderiv ℝ (graphSquaredDistance g (graphNormalEndpoint g (x, v)))) x) ↔
      Injective (fderiv ℝ (graphNormalEndpoint g) (x, v)) := by
  rw [(hasFDerivAt_fderiv_graphSquaredDistance_endpoint hg hB v).fderiv,
    (hasFDerivAt_graphNormalEndpoint hg.self_of_nhds hB v).fderiv]
  change Injective (twiceInner ∘ graphHessianOperator (fderiv ℝ g x) B v) ↔ _
  rw [twiceInner_injective.of_comp_iff]
  exact (graphEndpointDerivative_injective_iff _ _ _).symm

theorem differentiableAt_graphNormalEndpoint {g : E → F} {x : E}
    (hg : ContDiffAt ℝ 2 g x) (v : F) :
    DifferentiableAt ℝ (graphNormalEndpoint g) (x, v) := by
  exact (hasFDerivAt_graphNormalEndpoint (hg.differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt v).differentiableAt

theorem hessian_graphSquaredDistance_injective_of_regular_endpoint {g : E → F} {x : E}
    (hg : ContDiffAt ℝ 2 g x) {a : E × F}
    (hcrit : fderiv ℝ (graphSquaredDistance g a) x = 0)
    (hreg : Injective (fderiv ℝ (graphNormalEndpoint g) (x, a.2 - g x))) :
    Injective (fderiv ℝ (fderiv ℝ (graphSquaredDistance g a)) x) := by
  have hd := hg.differentiableAt (by norm_num)
  have he := graphNormalEndpoint_of_critical hd hcrit
  have hg' : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by norm_num)).mono fun _ hy => hy.differentiableAt (by norm_num)
  have hB := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h := (hessian_graphSquaredDistance_endpoint_injective_iff hg' hB (a.2 - g x)).mpr hreg
  simpa only [he] using h

/-- A single parameter makes all critical points nondegenerate in countably
many graph patches. The patches may be noncompact; no critical-point finiteness
or Morse-existence conclusion for an unconstructed manifold atlas is assumed. -/
theorem exists_nondegenerate_graphSquaredDistances [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (μ : MeasureTheory.Measure (E × F)) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {ι : Type*} [Countable ι] (g : ι → E → F) (s : ι → Set E)
    (hg : ∀ i x, x ∈ s i → ContDiffAt ℝ 2 (g i) x) :
    ∃ a : E × F, ∀ i x, x ∈ s i → fderiv ℝ (graphSquaredDistance (g i) a) x = 0 →
      Injective (fderiv ℝ (fderiv ℝ (graphSquaredDistance (g i) a)) x) := by
  obtain ⟨a, ha⟩ := exists_regularValue_countable μ (fun i => graphNormalEndpoint (g i))
    (fun i => {z : E × F | z.1 ∈ s i})
    (fun i z hz => differentiableAt_graphNormalEndpoint (hg i z.1 hz) z.2)
  refine ⟨a, ?_⟩
  intro i x hx hcrit
  apply hessian_graphSquaredDistance_injective_of_regular_endpoint (hg i x hx) hcrit
  apply (det_ne_zero_iff_injective _).mp
  exact ha i (x, a.2 - g i x) hx
    (graphNormalEndpoint_of_critical ((hg i x hx).differentiableAt (by norm_num)) hcrit)

/-- The regular parameter can be chosen in one fixed ambient Euclidean space
even when the tangent and normal subspaces differ between graph charts. -/
theorem exists_nondegenerate_isometric_graphs
    {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A]
    (μ : MeasureTheory.Measure A) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {ι : Type*} [Countable ι] (U V : ι → Type*)
    [∀ i, NormedAddCommGroup (U i)] [∀ i, InnerProductSpace ℝ (U i)]
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, CompleteSpace (U i)] [∀ i, CompleteSpace (V i)]
    (r : ∀ i, A ≃ₗᵢ[ℝ] WithLp 2 (U i × V i))
    (g : ∀ i, U i → V i) (s : ∀ i, Set (U i))
    (hg : ∀ i x, x ∈ s i → ContDiffAt ℝ 2 (g i) x) :
    ∃ a : A, ∀ i x, x ∈ s i →
      fderiv ℝ (graphSquaredDistance (g i) (WithLp.ofLp (r i a))) x = 0 →
      Injective (fderiv ℝ (fderiv ℝ (graphSquaredDistance (g i) (WithLp.ofLp (r i a)))) x) := by
  let c : ∀ i, (U i × V i) ≃L[ℝ] A := fun i =>
    (WithLp.prodContinuousLinearEquiv 2 ℝ (U i) (V i)).symm.trans
      (r i).symm.toContinuousLinearEquiv
  let f : ∀ i, (U i × V i) → A := fun i => c i ∘ graphNormalEndpoint (g i)
  obtain ⟨a, ha⟩ := exists_injective_fderiv_fibers_countable μ (fun i => U i × V i) c f
    (fun i => {z | z.1 ∈ s i}) (fun i z hz =>
      (c i).differentiableAt.comp z (differentiableAt_graphNormalEndpoint (hg i z.1 hz) z.2))
  refine ⟨a, ?_⟩
  intro i x hx hcrit
  let b : U i × V i := WithLp.ofLp (r i a)
  have he : graphNormalEndpoint (g i) (x, b.2 - g i x) = b :=
    graphNormalEndpoint_of_critical ((hg i x hx).differentiableAt (by norm_num)) hcrit
  have he' : f i (x, b.2 - g i x) = a := by
    simp only [f, Function.comp_apply, he]
    change (r i).symm (WithLp.toLp 2 (WithLp.ofLp (r i a))) = a
    simp
  have hreg := ha i (x, b.2 - g i x) hx he'
  have hd : fderiv ℝ (f i) (x, b.2 - g i x) =
      (c i : (U i × V i) →L[ℝ] A).comp
        (fderiv ℝ (graphNormalEndpoint (g i)) (x, b.2 - g i x)) :=
    (c i).comp_fderiv
  rw [hd] at hreg
  change Injective ((c i) ∘ fderiv ℝ (graphNormalEndpoint (g i)) (x, b.2 - g i x)) at hreg
  exact hessian_graphSquaredDistance_injective_of_regular_endpoint (hg i x hx) hcrit hreg.of_comp

end GaussBonnetChern.Morse


