import GaussBonnetChern.PuncturedBoundaryRegularity
import GaussBonnetChern.FiniteChartStokes
import GaussBonnetChern.GenericFormIntegration

/-! # The actual sphere trace of a deleted-ball boundary chart

The boundary is the height-zero slice of a concrete radial chart. Its
induced outward normal for the punctured domain points towards the removed
ball, so its lower-face integral has the negative of the outward-sphere sign.
All maps and derivatives below are the actual chart maps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.BoundarySphereTrace

open RadialBoundaryCharts PuncturedManifold DifferentialForm CoordinateStokes

section Embedding
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M]

/-- The actual coordinate sphere in the ambient manifold. -/
def sphereEmbedding (e : OpenPartialHomeomorph M E) (center : E) (r : ℝ) :
    sphere (0:E) 1 → M := fun u ↦ e.symm (center + r • (u:E))

theorem centered_sphere_mem (center : E) (r : ℝ) (hr : 0 < r) (u : sphere (0:E) 1) :
    center + r • (u:E) ∈ sphere center r := by
  have hu : ‖(u:E)‖ = 1 := norm_eq_of_mem_sphere u
  simp [mem_sphere, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu]

theorem centered_sphere_mem_closedBall (center : E) (r : ℝ) (hr : 0 < r)
    (u : sphere (0:E) 1) : center + r • (u:E) ∈ closedBall center r :=
  (centered_sphere_mem center r hr u).le

theorem sphereEmbedding_mem_coordinateSphere (e : OpenPartialHomeomorph M E)
    (center : E) (r : ℝ) (hr : 0 < r) (hcover : closedBall center r ⊆ e.target)
    (u : sphere (0:E) 1) : sphereEmbedding e center r u ∈ coordinateSphere e center r := by
  have ht := hcover (centered_sphere_mem_closedBall center r hr u)
  refine ⟨e.map_target ht, ?_⟩
  change e (e.symm (center + r • (u:E))) ∈ sphere center r
  rw [e.right_inv ht]
  exact centered_sphere_mem center r hr u

theorem sphereEmbedding_mem_coordinateClosedBall (e : OpenPartialHomeomorph M E)
    (center : E) (r : ℝ) (hr : 0 < r) (hcover : closedBall center r ⊆ e.target)
    (u : sphere (0:E) 1) : sphereEmbedding e center r u ∈ coordinateClosedBall e center r := by
  have h := sphereEmbedding_mem_coordinateSphere e center r hr hcover u
  exact ⟨h.1,h.2.le⟩

theorem sphereEmbedding_injective (e : OpenPartialHomeomorph M E)
    (center : E) (r : ℝ) (hr : 0 < r) (hcover : closedBall center r ⊆ e.target) :
    Function.Injective (sphereEmbedding e center r) := by
  intro u v huv
  have h := congrArg e huv
  change e (e.symm (center+r•(u:E))) = e (e.symm (center+r•(v:E))) at h
  rw [e.right_inv (hcover (centered_sphere_mem_closedBall center r hr u)),
    e.right_inv (hcover (centered_sphere_mem_closedBall center r hr v))] at h
  apply Subtype.ext
  exact smul_right_injective E hr.ne' (add_left_cancel h)

end Embedding

/-- Height-first insertion of the zero face, as an actual continuous linear map. -/
def heightZeroInclusion (d : ℕ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (d+1)) :=
  (heightFirstEquiv d).toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))).prod 0)

@[simp] theorem heightZeroInclusion_apply (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) :
    heightZeroInclusion d y = heightFirstEquiv d (y,0) := rfl

theorem heightZeroInclusion_basis (d : ℕ) (j : Fin d) :
    heightZeroInclusion d (EuclideanSpace.basisFun (Fin d) ℝ j) =
      EuclideanSpace.basisFun (Fin (d+1)) ℝ j.succ := by
  ext i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simp [heightZeroInclusion_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  · simp [heightZeroInclusion_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem heightZeroInclusion_toEuclidean (d : ℕ) (y : Fin d → ℝ) :
    heightZeroInclusion d (toEuclidean d y) = toEuclidean (d+1) (Fin.cons 0 y) := by
  ext i
  refine Fin.cases rfl (fun _ ↦ rfl) i

section RadialSlice
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] {d : ℕ}

theorem radialEuclideanChart_zero_symm (r : ℝ) (hr : 0 < r) (u : sphere (0:E) 1)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) :
    (radialEuclideanChart r hr u c).symm (heightZeroInclusion d y) = r • (c.symm y:E) := by
  change (radialProductChart r hr u c).symm
    ((heightFirstEquiv d).symm (heightFirstEquiv d (y,0))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply,
    radialProductChart_symm r hr u c y 0 (neg_lt_zero.mpr hr)]
  simp only [radialCollar,add_zero]

theorem radialEuclideanChart_zero_mem_target (r : ℝ) (hr : 0 < r) (u : sphere (0:E) 1)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) :
    heightZeroInclusion d y ∈ (radialEuclideanChart r hr u c).target ↔ y ∈ c.target := by
  change (heightFirstEquiv d (y,0) ∈ Set.univ ∧
    (heightFirstEquiv d).symm (heightFirstEquiv d (y,0)) ∈ (radialProductChart r hr u c).target) ↔ _
  simp only [mem_univ,true_and,ContinuousLinearEquiv.symm_apply_apply,radialProductChart_target,
    mem_prod,mem_Ioi]
  exact and_iff_left (neg_lt_zero.mpr hr)

theorem centeredRadialChart_zero_symm (e : OpenPartialHomeomorph M E)
    (center : E) (r : ℝ) (hr : 0 < r) (u : sphere (0:E) 1)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) :
    (centeredRadialChart e center r hr u c).symm (heightZeroInclusion d y) =
      sphereEmbedding e center r (c.symm y) := by
  change e.symm ((radialEuclideanChart r hr u c).symm (heightZeroInclusion d y) + center) = _
  rw [radialEuclideanChart_zero_symm]
  simp only [sphereEmbedding,add_comm]

variable [ProperSpace E] [T2Space M] {ι : Type*} [Fintype ι]

theorem puncturedBoundaryChart_zero_symm
    (e : ι → OpenPartialHomeomorph M E) (center : ι → E) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hcover : ∀ i, closedBall (center i) (r i) ⊆ (e i).target)
    (i : ι) (u : sphere (0:E) 1)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) :
    (puncturedBoundaryChart e center r hr hcover i u c).symm (heightZeroInclusion d y) =
      sphereEmbedding (e i) (center i) (r i) (c.symm y) :=
  centeredRadialChart_zero_symm (e i) (center i) (r i) (hr i) u c y

/-- The whole zero-height target is exactly the sphere-chart target.
Disjoint closed balls eliminate every extra restriction from the other holes. -/
theorem puncturedBoundaryChart_zero_mem_target
    (e : ι → OpenPartialHomeomorph M E) (center : ι → E) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hcover : ∀ i, closedBall (center i) (r i) ⊆ (e i).target)
    (hdis : Pairwise (fun i j ↦ Disjoint (coordinateClosedBall (e i) (center i) (r i))
      (coordinateClosedBall (e j) (center j) (r j))))
    (i : ι) (u : sphere (0:E) 1)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) :
    heightZeroInclusion d y ∈ (puncturedBoundaryChart e center r hr hcover i u c).target ↔
      y ∈ c.target := by
  constructor
  · intro hy
    exact (radialEuclideanChart_zero_mem_target (r i) (hr i) u c y).mp hy.1.1.1
  · intro hy
    have hRt := (radialEuclideanChart_zero_mem_target (r i) (hr i) u c y).mpr hy
    have ht := hcover i (centered_sphere_mem_closedBall (center i) (r i) (hr i) (c.symm y))
    have hCt : heightZeroInclusion d y ∈
        (centeredRadialChart (e i) (center i) (r i) (hr i) u c).target := by
      change (heightZeroInclusion d y ∈ (radialEuclideanChart (r i) (hr i) u c).target ∧
        (radialEuclideanChart (r i) (hr i) u c).symm (heightZeroInclusion d y) ∈ Set.univ) ∧
        (radialEuclideanChart (r i) (hr i) u c).symm (heightZeroInclusion d y) + center i ∈ (e i).target
      refine ⟨⟨hRt,Set.mem_univ _⟩,?_⟩
      rw [radialEuclideanChart_zero_symm,add_comm]
      exact ht
    refine ⟨hCt,?_⟩
    change (centeredRadialChart (e i) (center i) (r i) (hr i) u c).symm
      (heightZeroInclusion d y) ∈ otherBallExterior e center r i
    rw [centeredRadialChart_zero_symm]
    exact coordinateClosedBall_subset_otherBallExterior e center r hdis i
      (sphereEmbedding_mem_coordinateClosedBall (e i) (center i) (r i) (hr i) (hcover i) (c.symm y))

/-- Restricting a boundary-chart weight to its own coordinate sphere has
exactly the corresponding sphere-chart support domain. -/
theorem sphereEmbedding_mem_puncturedBoundaryChart_source_iff
    (e : ι → OpenPartialHomeomorph M E) (center : ι → E) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hcover : ∀ i, closedBall (center i) (r i) ⊆ (e i).target)
    (hdis : Pairwise (fun i j ↦ Disjoint (coordinateClosedBall (e i) (center i) (r i))
      (coordinateClosedBall (e j) (center j) (r j))))
    (i : ι) (u : sphere (0:E) 1)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (v : sphere (0:E) 1) :
    sphereEmbedding (e i) (center i) (r i) v ∈
      (puncturedBoundaryChart e center r hr hcover i u c).source ↔ v ∈ c.source := by
  let γ := puncturedBoundaryChart e center r hr hcover i u c
  let F := sphereEmbedding (e i) (center i) (r i)
  constructor
  · intro hx
    have hz0 : γ (F v) 0 = 0 := by
      rw [show γ (F v) 0 = ‖e i (F v) - center i‖ - r i from
        centeredRadialChart_height (e i) (center i) (r i) (hr i) u c (F v) hx.1]
      change ‖e i ((e i).symm (center i + r i • (v:E))) - center i‖ - r i = 0
      rw [(e i).right_inv (hcover i (centered_sphere_mem_closedBall (center i) (r i) (hr i) v))]
      simp [norm_smul,Real.norm_eq_abs,abs_of_pos (hr i),norm_eq_of_mem_sphere v]
    let y := ((heightFirstEquiv d).symm (γ (F v))).1
    have hz : heightZeroInclusion d y = γ (F v) := by
      rw [heightZeroInclusion_apply]
      apply (heightFirstEquiv d).symm.injective
      rw [ContinuousLinearEquiv.symm_apply_apply]
      apply Prod.ext
      · rfl
      · exact hz0.symm
    have hyt : y ∈ c.target :=
      (puncturedBoundaryChart_zero_mem_target e center r hr hcover hdis i u c y).mp
        (hz.symm ▸ γ.map_source hx)
    have heq : F (c.symm y) = F v := by
      calc
        F (c.symm y) = γ.symm (heightZeroInclusion d y) :=
          (puncturedBoundaryChart_zero_symm e center r hr hcover i u c y).symm
        _ = F v := by rw [hz, γ.left_inv hx]
    have hv : c.symm y = v := sphereEmbedding_injective (e i) (center i) (r i) (hr i) (hcover i) heq
    exact hv ▸ c.map_target hyt
  · intro hv
    have ht := (puncturedBoundaryChart_zero_mem_target e center r hr hcover hdis i u c
      (c v)).mpr (c.map_source hv)
    have hx := γ.map_target ht
    rw [puncturedBoundaryChart_zero_symm,c.left_inv hv] at hx
    exact hx

end RadialSlice

section SmoothEmbedding
variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (d+1))) M] [IsManifold (𝓡 (d+1)) ∞ M]

local instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d+1))) = d+1) := ⟨finrank_euclideanSpace_fin⟩

theorem contMDiff_sphereEmbedding
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 (d+1)) ∞ M)
    (center : EuclideanSpace ℝ (Fin (d+1))) (r : ℝ) (hr : 0 < r)
    (hcover : closedBall center r ⊆ e.target) :
    ContMDiff (𝓡 d) (𝓡 (d+1)) ∞ (sphereEmbedding e center r) := by
  intro u
  have hcenter : ContMDiffAt (𝓡 d) (𝓡 (d+1)) ∞
      (fun v : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1 ↦ center + r • (v : EuclideanSpace ℝ (Fin (d+1)))) u := by
    have hsmul : ContMDiffAt (𝓡 d) (𝓡 (d+1)) ∞
        (fun v : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1 ↦
          r • (v : EuclideanSpace ℝ (Fin (d+1)))) u := by
      change ContMDiffAt (𝓡 d) (𝓡 (d+1)) ∞
        ((fun _ : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1 ↦ r) • Subtype.val) u
      exact (contMDiffAt_const (I := 𝓡 d) (I' := 𝓘(ℝ)) (n := ∞) (x := u) (c := r)).smul
        (contMDiff_coe_sphere (n := d) (m := ∞) u)
    change ContMDiffAt (𝓡 d) (𝓡 (d+1)) ∞
      ((fun _ : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1 ↦ center) +
        fun v : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1 ↦
          r • (v : EuclideanSpace ℝ (Fin (d+1)))) u
    exact (contMDiffAt_const (I := 𝓡 d) (I' := 𝓡 (d+1))
      (n := ∞) (x := u) (c := center)).add hsmul
  exact (contMDiffAt_symm_of_mem_maximalAtlas he
    (hcover (centered_sphere_mem_closedBall center r hr u))).comp u hcenter

end SmoothEmbedding

section Trace
variable {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (d+1))) M] [IsManifold (𝓡 (d+1)) ∞ M]
  {ι : Type*} [Fintype ι]

local instance sphereDimensionTrace :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d+1))) = d+1) := ⟨finrank_euclideanSpace_fin⟩

/-- The derivative of the zero face of the inverse punctured chart is the
derivative of the actual sphere embedding composed with the inverse sphere chart. -/
theorem puncturedBoundaryChart_zero_derivative
    (e : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))))
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas (𝓡 (d+1)) ∞ M)
    (center : ι → EuclideanSpace ℝ (Fin (d+1))) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (e i).target)
    (hdis : Pairwise (fun i j ↦ Disjoint (coordinateClosedBall (e i) (center i) (r i))
      (coordinateClosedBall (e j) (center j) (r j))))
    (i : ι) (u : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
    (c : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
      (EuclideanSpace ℝ (Fin d)))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1))
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ c.target) :
    (mfderiv (𝓡 (d+1)) (𝓡 (d+1))
      (puncturedBoundaryChart e center r hr hcover i u c).symm (heightZeroInclusion d y)).comp
        (heightZeroInclusion d) =
      (mfderiv (𝓡 d) (𝓡 (d+1)) (sphereEmbedding (e i) (center i) (r i)) (c.symm y)).comp
        (mfderiv (𝓡 d) (𝓡 d) c.symm y) := by
  let γ := puncturedBoundaryChart e center r hr hcover i u c
  let F := sphereEmbedding (e i) (center i) (r i)
  have hγ := puncturedBoundaryChart_mem_maximalAtlas e he center r hr hcover i u c hc
  have hz := (puncturedBoundaryChart_zero_mem_target e center r hr hcover hdis i u c y).mpr hy
  have hDface : mfderiv (𝓡 d) (𝓡 (d+1)) (heightZeroInclusion d) y = heightZeroInclusion d := by
    rw [mfderiv_eq_fderiv]
    exact (heightZeroInclusion d).hasFDerivAt.fderiv
  have hface : ContMDiff (𝓡 d) (𝓡 (d+1)) ∞ (heightZeroInclusion d) :=
    (heightZeroInclusion d).contDiff.contMDiff
  have hl := mfderiv_comp y
    ((contMDiffAt_symm_of_mem_maximalAtlas hγ hz).mdifferentiableAt (by simp))
    ((hface y).mdifferentiableAt (by simp))
  have hr' := mfderiv_comp y
    ((contMDiff_sphereEmbedding (e i) (he i) (center i) (r i) (hr i) (hcover i)
      (c.symm y)).mdifferentiableAt (by simp))
    ((contMDiffAt_symm_of_mem_maximalAtlas hc hy).mdifferentiableAt (by simp))
  have heq : γ.symm ∘ heightZeroInclusion d = F ∘ c.symm := by
    funext z
    exact puncturedBoundaryChart_zero_symm e center r hr hcover i u c z
  rw [hDface] at hl
  change mfderiv (𝓡 d) (𝓡 (d+1)) (γ.symm ∘ heightZeroInclusion d) y = _ at hl
  rw [heq] at hl
  exact hl.symm.trans hr'

/-- Actual coordinate evaluation of the sphere pullback is the height-zero
tangential evaluation of the ambient form. No smoothness of the form itself
is needed for this algebraic trace identity. -/
theorem puncturedBoundaryChart_zero_coefficient
    (e : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (d+1))))
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas (𝓡 (d+1)) ∞ M)
    (center : ι → EuclideanSpace ℝ (Fin (d+1))) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (e i).target)
    (hdis : Pairwise (fun i j ↦ Disjoint (coordinateClosedBall (e i) (center i) (r i))
      (coordinateClosedBall (e j) (center j) (r j))))
    (i : ι) (u : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
    (c : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
      (EuclideanSpace ℝ (Fin d)))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1))
    (α : Form (𝓡 (d+1)) M d) (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ c.target) :
    chartRepresentation (puncturedBoundaryChart e center r hr hcover i u c) α
      (heightZeroInclusion d y) (fun j ↦ EuclideanSpace.basisFun (Fin (d+1)) ℝ j.succ) =
    GenericFormIntegration.coefficient c
      (pullback (I := 𝓡 d) (I' := 𝓡 (d+1)) (sphereEmbedding (e i) (center i) (r i)) α) y := by
  let γ := puncturedBoundaryChart e center r hr hcover i u c
  let F := sphereEmbedding (e i) (center i) (r i)
  have hD := puncturedBoundaryChart_zero_derivative e he center r hr hcover hdis i u c hc y hy
  have hvec (j : Fin d) :
      mfderiv (𝓡 (d+1)) (𝓡 (d+1)) γ.symm (heightZeroInclusion d y)
        (EuclideanSpace.basisFun (Fin (d+1)) ℝ j.succ) =
      mfderiv (𝓡 d) (𝓡 (d+1)) F (c.symm y)
        (mfderiv (𝓡 d) (𝓡 d) c.symm y (EuclideanSpace.basisFun (Fin d) ℝ j)) := by
    rw [← heightZeroInclusion_basis]
    exact congrArg (fun L ↦ L (EuclideanSpace.basisFun (Fin d) ℝ j)) hD
  change α (γ.symm (heightZeroInclusion d y)) (fun j ↦
    mfderiv (𝓡 (d+1)) (𝓡 (d+1)) γ.symm (heightZeroInclusion d y)
      (EuclideanSpace.basisFun (Fin (d+1)) ℝ j.succ)) =
    α (F (c.symm y)) (fun j ↦ mfderiv (𝓡 d) (𝓡 (d+1)) F (c.symm y)
      (mfderiv (𝓡 d) (𝓡 d) c.symm y (EuclideanSpace.basisFun (Fin d) ℝ j)))
  simp only [hvec]
  rw [show γ.symm (heightZeroInclusion d y) = F (c.symm y) from
    puncturedBoundaryChart_zero_symm e center r hr hcover i u c y]

end Trace

section LowerFace
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Model (n+1)) M] [IsManifold (model (n+1)) ∞ M]
  {ι : Type*} [Fintype ι]

local instance sphereDimensionLowerFace :
    Fact (Module.finrank ℝ (Model (n+1)) = (2*n+1)+1) :=
  ⟨by simp [Model,Nat.mul_add,Nat.add_assoc]⟩

/-- The lower-face flux of an actual punctured boundary chart is the
negative of the outward sphere-chart pullback integral. The sign is inherited
from the genuine height-nonnegative domain, and no Stokes identity is assumed. -/
theorem lowerFaceIntegral_puncturedBoundaryChart
    (e : ι → OpenPartialHomeomorph M (Model (n+1)))
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas (model (n+1)) ∞ M)
    (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (e i).target)
    (hdis : Pairwise (fun i j ↦ Disjoint (coordinateClosedBall (e i) (center i) (r i))
      (coordinateClosedBall (e j) (center j) (r j))))
    (i : ι) (u : sphere (0 : Model (n+1)) 1)
    (c : OpenPartialHomeomorph (sphere (0 : Model (n+1)) 1)
      (EuclideanSpace ℝ (Fin (2*n+1))))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 (2*n+1)) ∞ (sphere (0 : Model (n+1)) 1))
    (ρ : M → ℝ) (β : Form (model (n+1)) M (2*n+1)) :
    FiniteChartStokes.lowerFaceIntegral (puncturedBoundaryChart e center r hr hcover i u c)
      (StokesLocalization.weightForm ρ β) =
      -(∫ y in c.target,
        ρ (sphereEmbedding (e i) (center i) (r i) (c.symm y)) *
          GenericFormIntegration.coefficient c
            (pullback (I := 𝓡 (2*n+1)) (I' := model (n+1))
              (sphereEmbedding (e i) (center i) (r i)) β) y) := by
  let γ := puncturedBoundaryChart e center r hr hcover i u c
  let F := sphereEmbedding (e i) (center i) (r i)
  have hs : {y : Fin (2*n+1) → ℝ |
      toEuclidean (2*n+1+1) (Fin.cons 0 y) ∈ γ.target} =
      (toEuclidean (2*n+1)) ⁻¹' c.target := by
    ext y
    change toEuclidean (2*n+1+1) (Fin.cons 0 y) ∈ γ.target ↔
      toEuclidean (2*n+1) y ∈ c.target
    rw [← heightZeroInclusion_toEuclidean (2*n+1) y]
    exact puncturedBoundaryChart_zero_mem_target e center r hr hcover hdis i u c _
  unfold FiniteChartStokes.lowerFaceIntegral
  rw [hs]
  congr 1
  have hvol := (PiLp.volume_preserving_toLp (Fin (2*n+1))).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin (2*n+1) → ℝ)).measurableEmbedding
    (fun y ↦ ρ (F (c.symm y)) * GenericFormIntegration.coefficient c
      (pullback (I := 𝓡 (2*n+1)) (I' := model (n+1)) F β) y) c.target
  rw [← hvol]
  apply setIntegral_congr_fun (c.open_target.measurableSet.preimage (toEuclidean (2*n+1)).continuous.measurable)
  intro y hy
  change chartRepresentation (puncturedBoundaryChart e center r hr hcover i u c)
      (StokesLocalization.weightForm ρ β) (toEuclidean (2*n+1+1) (Fin.cons 0 y))
      (fun j ↦ EuclideanSpace.basisFun (Fin (2*n+1+1)) ℝ j.succ) =
    ρ (F (c.symm (toEuclidean (2*n+1) y))) * GenericFormIntegration.coefficient c
      (pullback (I := 𝓡 (2*n+1)) (I' := model (n+1)) F β) (toEuclidean (2*n+1) y)
  rw [← heightZeroInclusion_toEuclidean (2*n+1) y]
  rw [StokesLocalization.chartRepresentation_weightForm,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  rw [puncturedBoundaryChart_zero_symm]
  have hcoef := puncturedBoundaryChart_zero_coefficient e he center r hr hcover hdis
    i u c hc β (toEuclidean (2*n+1) y) hy
  exact congrArg (fun s : ℝ ↦ ρ (F (c.symm (toEuclidean (2*n+1) y))) * s) hcoef

end LowerFace
end GaussBonnetChern.BoundarySphereTrace
