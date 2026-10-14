import GaussBonnetChern.ExteriorSmoothLinear

/-! Actual scalar differentials and the degree-zero exterior derivative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℝ,E) ∞ P]

/-- The actual differential of a scalar function, as a one-form. -/
def scalarDifferential (f : P → ℝ) : Form 𝓘(ℝ,E) P 1 :=
  fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0:Fin 1) (mvfderiv 𝓘(ℝ,E) f x)

@[simp] theorem scalarDifferential_apply (f : P → ℝ) (x : P)
    (v : Fin 1 → TangentSpace 𝓘(ℝ,E) x) :
    scalarDifferential f x v = mvfderiv 𝓘(ℝ,E) f x (v 0) := rfl

/-- The genuine chartwise exterior derivative in degree zero equals the
genuine manifold differential; no differential operator law is postulated. -/
theorem exteriorDerivative_ofFunction_at {f : P → ℝ} (x : P)
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ) f x) :
    exteriorDerivative (ofFunction (I := 𝓘(ℝ,E)) f) x = scalarDifferential (E := E) f x := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ P := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  have hy : e x ∈ e.target := e.map_source hx
  have hgi := (contMDiffAt_symm_of_mem_maximalAtlas he hy).mdifferentiableAt (by simp)
  have hfe : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ) f (e.symm (e x)) := by
    simpa only [e.left_inv hx] using hf
  have hchain : fderiv ℝ (f ∘ e.symm) (e x) =
      (mvfderiv 𝓘(ℝ,E) f (e.symm (e x))).comp (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm (e x)) := by
    rw [← mvfderiv_eq_fderiv]
    ext w
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ) (f ∘ e.symm) (e x) w =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ) f (e.symm (e x)) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm (e x) w)
    rw [mfderiv_comp (e x) hfe hgi]
    rfl
  apply ContinuousAlternatingMap.ext
  intro v
  change extDeriv (chartRepresentation e (ofFunction f)) (e x) (chartTangentMap e x ∘ v) =
    mvfderiv 𝓘(ℝ,E) f x (v 0)
  rw [chartRepresentation_ofFunction, extDeriv_constOfIsEmpty]
  change fderiv ℝ (f ∘ e.symm) (e x) (chartTangentMap e x (v 0)) = _
  rw [hchain]
  have hvec := inverseChartTangentMap_chartTangentMap e he x hx (v 0)
  convert! congrArg (fun w ↦ mvfderiv 𝓘(ℝ,E) f x w) hvec using 1
  erw [e.left_inv hx]
  rfl

theorem exteriorDerivative_ofFunction {f : P → ℝ}
    (hf : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ) f) :
    exteriorDerivative (ofFunction (I := 𝓘(ℝ,E)) f) = scalarDifferential (E := E) f := by
  funext x
  exact exteriorDerivative_ofFunction_at x (hf x)

theorem IsSmooth.scalarDifferential {f : P → ℝ}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ f) : IsSmooth (scalarDifferential (E := E) f) := by
  rw [← exteriorDerivative_ofFunction (hf.mdifferentiable (by simp))]
  exact (IsSmooth.ofFunction hf).exteriorDerivative

/-- The actual scalar differential is closed. -/
theorem exteriorDerivative_scalarDifferential {f : P → ℝ}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ f) :
    exteriorDerivative (scalarDifferential (E := E) f) = 0 := by
  rw [← exteriorDerivative_ofFunction (hf.mdifferentiable (by simp))]
  exact exteriorDerivative_exteriorDerivative _ (IsSmooth.ofFunction hf)

@[simp] theorem scalarDifferential_const (c : ℝ) :
    scalarDifferential (E := E) (P := P) (fun _ ↦ c) = 0 := by
  funext x
  ext v
  simp [scalarDifferential_apply, mvfderiv_const]

@[simp] theorem exteriorDerivative_ofFunction_const (c : ℝ) :
    exteriorDerivative (ofFunction (I := 𝓘(ℝ,E)) (M := P) (fun _ ↦ c)) = 0 := by
  rw [exteriorDerivative_ofFunction mdifferentiable_const, scalarDifferential_const]

theorem scalarDifferential_mul_at {f g : P → ℝ} (x : P)
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ) f x)
    (hg : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ) g x) :
    scalarDifferential (E := E) (fun y ↦ f y * g y) x =
      f x • scalarDifferential (E := E) g x + g x • scalarDifferential (E := E) f x := by
  ext v
  simp only [scalarDifferential_apply, mvfderiv_fun_mul hf hg,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

theorem scalarDifferential_mul {f g : P → ℝ}
    (hf : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ) g) :
    scalarDifferential (E := E) (fun x ↦ f x * g x) =
      (fun x ↦ f x • scalarDifferential (E := E) g x + g x • scalarDifferential (E := E) f x) := by
  funext x
  exact scalarDifferential_mul_at x (hf x) (hg x)

/-- Local finite-sum rule, so local frame coefficients do not have to be
extended as globally differentiable functions. -/
theorem scalarDifferential_sum_at {ι : Type*} (s : Finset ι) (f : ι → P → ℝ) (x : P)
    (hf : ∀ i ∈ s, MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ) (f i) x) :
    scalarDifferential (E := E) (fun y ↦ ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, scalarDifferential (E := E) (f i) x := by
  classical
  have h := (HasMFDerivAt.sum (t := s) (fun i hi ↦ (hf i hi).hasMFDerivAt)).mfderiv
  have hfun : (fun y ↦ ∑ i ∈ s, f i y) = ∑ i ∈ s, f i := by
    funext y
    simp
  rw [hfun]
  ext v
  simp only [ContinuousAlternatingMap.sum_apply, scalarDifferential_apply]
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ) (∑ i ∈ s, f i) x (v 0) =
    ∑ i ∈ s, mfderiv 𝓘(ℝ,E) 𝓘(ℝ) (f i) x (v 0)
  rw [h]
  simp only [ContinuousLinearMap.sum_apply]
  rfl

section Pullback
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace F Q] [IsManifold 𝓘(ℝ,F) ∞ Q]

/-- Scalar differentials pull back by the actual manifold chain rule. -/
theorem pullback_scalarDifferential_at (φ : P → Q) (f : Q → ℝ) (x : P)
    (hφ : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) φ x)
    (hf : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ) f (φ x)) :
    pullback (I := 𝓘(ℝ,E)) φ (scalarDifferential (E := F) f) x =
      scalarDifferential (E := E) (f ∘ φ) x := by
  ext v
  simp only [pullback_apply, scalarDifferential_apply]
  unfold mvfderiv
  rw [mfderiv_comp x hf hφ]
  rfl

theorem pullback_scalarDifferential (φ : P → Q) (f : Q → ℝ)
    (hφ : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,F) φ)
    (hf : MDifferentiable 𝓘(ℝ,F) 𝓘(ℝ) f) :
    pullback (I := 𝓘(ℝ,E)) φ (scalarDifferential (E := F) f) =
      scalarDifferential (E := E) (f ∘ φ) := by
  funext x
  exact pullback_scalarDifferential_at φ f x (hφ x) (hf (φ x))

theorem pullback_const_succ (q : Q) (k : ℕ) (α : Form 𝓘(ℝ,F) Q (k+1)) :
    pullback (I := 𝓘(ℝ,E)) (fun _ : P ↦ q) α = 0 := by
  funext x
  ext v
  simp only [pullback_apply, mfderiv_const, zero_apply]
  exact (α q).map_coord_zero 0 rfl

end Pullback

end GaussBonnetChern.DifferentialForm
