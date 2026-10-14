import GaussBonnetChern.ExteriorAssociativity

/-! # Linear operations on genuine smooth differential forms

The additive group and real module operations on `Form` are the existing
pointwise operations on continuous alternating maps. Smoothness and linearity of
exterior differentiation are proved using actual coordinate representations.
Additivity of the totalized derivative is only asserted at differentiable forms.
-/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {k : ℕ}

@[simp] theorem chartRepresentation_zero (e : OpenPartialHomeomorph M E) :
    chartRepresentation e (0 : Form 𝓘(ℝ, E) M k) = 0 := by
  funext y
  ext v
  rfl

@[simp] theorem chartRepresentation_add (e : OpenPartialHomeomorph M E)
    (α β : Form 𝓘(ℝ, E) M k) :
    chartRepresentation e (α + β) = chartRepresentation e α + chartRepresentation e β := by
  funext y
  ext v
  rfl

@[simp] theorem chartRepresentation_neg (e : OpenPartialHomeomorph M E)
    (α : Form 𝓘(ℝ, E) M k) :
    chartRepresentation e (-α) = -chartRepresentation e α := by
  funext y
  ext v
  rfl

@[simp] theorem chartRepresentation_sub (e : OpenPartialHomeomorph M E)
    (α β : Form 𝓘(ℝ, E) M k) :
    chartRepresentation e (α - β) = chartRepresentation e α - chartRepresentation e β := by
  simp only [sub_eq_add_neg, chartRepresentation_add, chartRepresentation_neg]

@[simp] theorem chartRepresentation_smul (e : OpenPartialHomeomorph M E)
    (c : ℝ) (α : Form 𝓘(ℝ, E) M k) :
    chartRepresentation e (c • α) = c • chartRepresentation e α := by
  funext y
  ext v
  rfl

/-- Coordinates form a genuine real linear map, including outside the chart.
No differentiability is needed for this algebraic operation. -/
def chartRepresentationLinear (e : OpenPartialHomeomorph M E) :
    Form 𝓘(ℝ, E) M k →ₗ[ℝ]
      (E → ContinuousAlternatingMap ℝ E ℝ (Fin k)) where
  toFun := chartRepresentation e
  map_add' := chartRepresentation_add e
  map_smul' := chartRepresentation_smul e

@[simp] theorem chartRepresentation_sum {ι : Type*} (e : OpenPartialHomeomorph M E)
    (s : Finset ι) (α : ι → Form 𝓘(ℝ, E) M k) :
    chartRepresentation e (∑ i ∈ s, α i) = ∑ i ∈ s, chartRepresentation e (α i) :=
  map_sum (chartRepresentationLinear e) α s

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem IsSmooth.zero : IsSmooth (0 : Form 𝓘(ℝ, E) M k) := by
  intro e _
  rw [chartRepresentation_zero]
  exact contDiffOn_const

theorem IsSmooth.add {α β : Form 𝓘(ℝ, E) M k}
    (hα : IsSmooth α) (hβ : IsSmooth β) : IsSmooth (α + β) := by
  intro e he
  rw [chartRepresentation_add]
  exact (hα e he).add (hβ e he)

theorem IsSmooth.neg {α : Form 𝓘(ℝ, E) M k} (hα : IsSmooth α) : IsSmooth (-α) := by
  intro e he
  rw [chartRepresentation_neg]
  exact (hα e he).neg

theorem IsSmooth.sub {α β : Form 𝓘(ℝ, E) M k}
    (hα : IsSmooth α) (hβ : IsSmooth β) : IsSmooth (α - β) := by
  simpa only [sub_eq_add_neg] using hα.add hβ.neg

theorem IsSmooth.const_smul {α : Form 𝓘(ℝ, E) M k}
    (hα : IsSmooth α) (c : ℝ) : IsSmooth (c • α) := by
  intro e he
  rw [chartRepresentation_smul]
  exact (hα e he).const_smul c

theorem IsSmooth.sum {ι : Type*} (s : Finset ι) (α : ι → Form 𝓘(ℝ, E) M k)
    (hα : ∀ i ∈ s, IsSmooth (α i)) : IsSmooth (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (IsSmooth.zero (E := E) (M := M) (k := k))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hα i (Finset.mem_insert_self i s)).add
      (ih (fun j hj ↦ hα j (Finset.mem_insert_of_mem hj)))

theorem chartDerivative_add (e : OpenPartialHomeomorph M E)
    (α β : Form 𝓘(ℝ, E) M k) (x : M)
    (hα : DifferentiableAt ℝ (chartRepresentation e α) (e x))
    (hβ : DifferentiableAt ℝ (chartRepresentation e β) (e x)) :
    chartDerivative e (α + β) x = chartDerivative e α x + chartDerivative e β x := by
  unfold chartDerivative
  rw [chartRepresentation_add, extDeriv_add hα hβ]
  ext v
  rfl

/-- Local additivity only needs differentiability of the two coordinate forms
at the actual point. It does not need global smoothness of locally defined frames. -/
theorem exteriorDerivative_add_at (α β : Form 𝓘(ℝ, E) M k) (x : M)
    (hα : DifferentiableAt ℝ (chartRepresentation (chartAt E x) α) (chartAt E x x))
    (hβ : DifferentiableAt ℝ (chartRepresentation (chartAt E x) β) (chartAt E x x)) :
    exteriorDerivative (α + β) x = exteriorDerivative α x + exteriorDerivative β x :=
  chartDerivative_add (chartAt E x) α β x hα hβ

theorem exteriorDerivative_add (α β : Form 𝓘(ℝ, E) M k)
    (hα : IsSmooth α) (hβ : IsSmooth β) :
    exteriorDerivative (α + β) = exteriorDerivative α + exteriorDerivative β := by
  funext x
  apply exteriorDerivative_add_at
  · exact ((hα _ (IsManifold.chart_mem_maximalAtlas x)).contDiffAt
      ((chartAt E x).open_target.mem_nhds ((chartAt E x).map_source
        (mem_chart_source E x)))).differentiableAt (by simp)
  · exact ((hβ _ (IsManifold.chart_mem_maximalAtlas x)).contDiffAt
      ((chartAt E x).open_target.mem_nhds ((chartAt E x).map_source
        (mem_chart_source E x)))).differentiableAt (by simp)

@[simp] theorem exteriorDerivative_zero :
    exteriorDerivative (0 : Form 𝓘(ℝ, E) M k) = 0 := by
  funext x
  unfold exteriorDerivative chartDerivative
  rw [chartRepresentation_zero]
  simp only [extDeriv, fderiv_zero]
  change ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ) 0).compContinuousLinearMap _ = 0
  rw [map_zero]
  ext v
  rfl

/-- Constant scalar multiplication commutes even with the totalized derivative:
this special homogeneity law is valid without an additivity assertion. -/
theorem exteriorDerivative_smul (c : ℝ) (α : Form 𝓘(ℝ, E) M k) :
    exteriorDerivative (c • α) = c • exteriorDerivative α := by
  funext x
  unfold exteriorDerivative chartDerivative
  rw [chartRepresentation_smul, extDeriv_smul]
  ext v
  rfl

theorem exteriorDerivative_neg (α : Form 𝓘(ℝ, E) M k) :
    exteriorDerivative (-α) = -exteriorDerivative α := by
  have hneg {r : ℕ} (β : Form 𝓘(ℝ, E) M r) : (-1 : ℝ) • β = -β := by
    funext y
    ext v
    change (-1 : ℝ) * β y v = -(β y v)
    ring
  have h := exteriorDerivative_smul (-1) α
  rw [hneg, hneg] at h
  exact h

theorem exteriorDerivative_sub (α β : Form 𝓘(ℝ, E) M k)
    (hα : IsSmooth α) (hβ : IsSmooth β) :
    exteriorDerivative (α - β) = exteriorDerivative α - exteriorDerivative β := by
  rw [sub_eq_add_neg, exteriorDerivative_add α (-β) hα hβ.neg,
    exteriorDerivative_neg, sub_eq_add_neg]

theorem exteriorDerivative_sum {ι : Type*} (s : Finset ι)
    (α : ι → Form 𝓘(ℝ, E) M k) (hα : ∀ i ∈ s, IsSmooth (α i)) :
    exteriorDerivative (∑ i ∈ s, α i) = ∑ i ∈ s, exteriorDerivative (α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, exteriorDerivative_zero]
  | @insert i s hi ih =>
    have hiα := hα i (Finset.mem_insert_self i s)
    have hsα : ∀ j ∈ s, IsSmooth (α j) := fun j hj ↦ hα j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      exteriorDerivative_add _ _ hiα (IsSmooth.sum s α hsα), ih hsα]

end GaussBonnetChern.DifferentialForm

noncomputable section
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

theorem IsSmooth.degreeCast {r s : ℕ} (h : r = s)
    {α : Form 𝓘(ℝ, E) M r} (hα : IsSmooth α) : IsSmooth (degreeCastForm h α) := by
  subst s
  exact hα

theorem exteriorDerivative_degreeCast {r s : ℕ} (h : r = s)
    (α : Form 𝓘(ℝ, E) M r) :
    exteriorDerivative (degreeCastForm h α) =
      degreeCastForm (congrArg (fun j ↦ j + 1) h) (exteriorDerivative α) := by
  subst s
  rfl

@[simp] theorem chartRepresentation_ofFunction (e : OpenPartialHomeomorph M E)
    (f : M → ℝ) :
    chartRepresentation e (ofFunction f) =
      fun y ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f (e.symm y)) := by
  funext y
  ext v
  rfl

theorem IsSmooth.ofFunction {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) :
    IsSmooth (ofFunction (I := 𝓘(ℝ, E)) f) := by
  intro e he
  rw [chartRepresentation_ofFunction]
  intro y hy
  have hc : ContDiffAt ℝ ∞ (fun z ↦ f (e.symm z)) y :=
    (hf.contMDiffAt.comp y (contMDiffAt_symm_of_mem_maximalAtlas he hy)).contDiffAt
  let L := (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)).toContinuousLinearEquiv.toContinuousLinearMap
  exact (L.contDiff.contDiffAt.comp y hc).contDiffWithinAt

theorem isSmooth_ofFunction_const (c : ℝ) :
    IsSmooth (ofFunction (I := 𝓘(ℝ, E)) (M := M) (fun _ ↦ c)) :=
  IsSmooth.ofFunction contMDiff_const

/-- Exterior differentiation commutes with a finite sum of differentiable
model-space forms at the point. -/
theorem extDeriv_finset_sum {ι : Type*} (s : Finset ι)
    (α : ι → E → ContinuousAlternatingMap ℝ E ℝ (Fin k)) (x : E)
    (hα : ∀ i ∈ s, DifferentiableAt ℝ (α i) x) :
    extDeriv (∑ i ∈ s, α i) x = ∑ i ∈ s, extDeriv (α i) x := by
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ)
      (fderiv ℝ (∑ i ∈ s, α i) x) = _
  rw [fderiv_sum hα, map_sum]
  rfl

theorem extDeriv_fun_finset_sum {ι : Type*} (s : Finset ι)
    (α : ι → E → ContinuousAlternatingMap ℝ E ℝ (Fin k)) (x : E)
    (hα : ∀ i ∈ s, DifferentiableAt ℝ (α i) x) :
    extDeriv (fun y ↦ ∑ i ∈ s, α i y) x = ∑ i ∈ s, extDeriv (α i) x := by
  have heq : (fun y ↦ ∑ i ∈ s, α i y) = ∑ i ∈ s, α i := by
    funext y
    simp
  rw [heq]
  exact extDeriv_finset_sum s α x hα

theorem chartDerivative_sum {ι : Type*} (s : Finset ι)
    (e : OpenPartialHomeomorph M E) (α : ι → Form 𝓘(ℝ, E) M k) (x : M)
    (hα : ∀ i ∈ s, DifferentiableAt ℝ (chartRepresentation e (α i)) (e x)) :
    chartDerivative e (∑ i ∈ s, α i) x = ∑ i ∈ s, chartDerivative e (α i) x := by
  unfold chartDerivative
  rw [chartRepresentation_sum, extDeriv_finset_sum s _ _ hα]
  ext v
  simp

theorem exteriorDerivative_sum_at {ι : Type*} (s : Finset ι)
    (α : ι → Form 𝓘(ℝ, E) M k) (x : M)
    (hα : ∀ i ∈ s, DifferentiableAt ℝ (chartRepresentation (chartAt E x) (α i))
      (chartAt E x x)) :
    exteriorDerivative (∑ i ∈ s, α i) x = ∑ i ∈ s, exteriorDerivative (α i) x :=
  chartDerivative_sum s (chartAt E x) α x hα

/-- Smoothness of the coordinate exterior derivative follows from ordinary
Fréchet differentiation and its continuous linear alternatization. -/
theorem contDiffAt_extDeriv {α : E → ContinuousAlternatingMap ℝ E ℝ (Fin k)} {x : E}
    (hα : ContDiffAt ℝ ∞ α x) : ContDiffAt ℝ ∞ (extDeriv α) x :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).contDiff.contDiffAt.comp x
    (hα.fderiv_right (by simp))

section MatrixCurvature
variable {ι : Type*} [Fintype ι]

/-- Curvature of a finite matrix of genuine model-space connection one-forms.
It is defined by `dA + A ∧ A`, with the column-frame convention. -/
def connectionMatrixCurvature
    (A : ι → ι → E → ContinuousAlternatingMap ℝ E ℝ (Fin 1))
    (a b : ι) (x : E) : ContinuousAlternatingMap ℝ E ℝ (Fin 2) :=
  extDeriv (A a b) x + ∑ c, wedgeFiber (A a c x) (A c b x)

private theorem wedgeFiber_add_left_linear {r s : ℕ}
    (a b : ContinuousAlternatingMap ℝ E ℝ (Fin r))
    (c : ContinuousAlternatingMap ℝ E ℝ (Fin s)) :
    wedgeFiber (a + b) c = wedgeFiber a c + wedgeFiber b c := by
  change wedgeFiberBilinear r s (a + b) c = _
  rw [map_add, ContinuousLinearMap.add_apply]
  rfl

private theorem wedgeFiber_add_right_linear {r s : ℕ}
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin r))
    (b c : ContinuousAlternatingMap ℝ E ℝ (Fin s)) :
    wedgeFiber a (b + c) = wedgeFiber a b + wedgeFiber a c :=
  (wedgeFiberBilinear r s a).map_add b c

private theorem wedgeFiber_sum_left_linear {r s : ℕ}
    (a : ι → ContinuousAlternatingMap ℝ E ℝ (Fin r))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin s)) :
    wedgeFiber (∑ c, a c) b = ∑ c, wedgeFiber (a c) b := by
  change wedgeFiberBilinear r s (∑ c, a c) b = _
  rw [map_sum, ContinuousLinearMap.sum_apply]
  rfl

private theorem wedgeFiber_sum_right_linear {r s : ℕ}
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin r))
    (b : ι → ContinuousAlternatingMap ℝ E ℝ (Fin s)) :
    wedgeFiber a (∑ c, b c) = ∑ c, wedgeFiber a (b c) :=
  map_sum (wedgeFiberBilinear r s a) b Finset.univ

/-- The two cubic matrix wedge sums agree by associativity and exchange of
the two finite indices. No skew symmetry or dimension restriction is used. -/
theorem connectionMatrix_cubic_cancel
    (A : ι → ι → ContinuousAlternatingMap ℝ E ℝ (Fin 1)) (a b : ι) :
    (∑ c, ∑ d, wedgeFiber (wedgeFiber (A a d) (A d c)) (A c b)) =
      ∑ c, ∑ d, wedgeFiber (A a c) (wedgeFiber (A c d) (A d b)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ext v
  simpa using wedgeFiber_assoc_apply (A a c) (A c d) (A d b) v

/-- The differential Bianchi identity for a genuine smooth connection matrix,
at a point where its entries are smooth. This is a local coordinate theorem. -/
theorem extDeriv_connectionMatrixCurvature
    (A : ι → ι → E → ContinuousAlternatingMap ℝ E ℝ (Fin 1))
    (x : E) (hA : ∀ a b, ContDiffAt ℝ ∞ (A a b) x) (a b : ι) :
    extDeriv (connectionMatrixCurvature A a b) x =
      ∑ c, (wedgeFiber (connectionMatrixCurvature A a c x) (A c b x) -
        wedgeFiber (A a c x) (connectionMatrixCurvature A c b x)) := by
  have hdA := fun a b ↦ (hA a b).differentiableAt (by simp)
  have hw := fun c ↦ contDiffAt_wedgeFiber (hA a c) (hA c b)
  have hsum : DifferentiableAt ℝ
      (fun y ↦ ∑ c, wedgeFiber (A a c y) (A c b y)) x :=
    DifferentiableAt.fun_sum (fun c _ ↦ (hw c).differentiableAt (by simp))
  change extDeriv (fun y ↦ extDeriv (A a b) y +
    ∑ c, wedgeFiber (A a c y) (A c b y)) x = _
  rw [extDeriv_fun_add ((contDiffAt_extDeriv (hA a b)).differentiableAt (by simp)) hsum,
    extDeriv_extDeriv_apply (hA a b) (by simp), zero_add,
    extDeriv_fun_finset_sum Finset.univ _ x
      (fun c _ ↦ (hw c).differentiableAt (by simp))]
  have hleib (c : ι) :
      extDeriv (fun y ↦ wedgeFiber (A a c y) (A c b y)) x =
        wedgeFiber (extDeriv (A a c) x) (A c b x) -
          wedgeFiber (A a c x) (extDeriv (A c b) x) := by
    rw [extDeriv_wedgeFiber (hdA a c) (hdA c b), pow_one]
    change wedgeFiber (extDeriv (A a c) x) (A c b x) +
      (-1 : ℝ) • wedgeFiber (A a c x) (extDeriv (A c b) x) = _
    ext v
    change wedgeFiber (extDeriv (A a c) x) (A c b x) v +
      (-1 : ℝ) * wedgeFiber (A a c x) (extDeriv (A c b) x) v =
        wedgeFiber (extDeriv (A a c) x) (A c b x) v -
          wedgeFiber (A a c x) (extDeriv (A c b) x) v
    ring
  simp_rw [hleib, connectionMatrixCurvature, wedgeFiber_add_left_linear,
    wedgeFiber_add_right_linear, wedgeFiber_sum_left_linear, wedgeFiber_sum_right_linear]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, connectionMatrix_cubic_cancel (fun a b ↦ A a b x) a b]
  abel

end MatrixCurvature
end GaussBonnetChern.DifferentialForm
