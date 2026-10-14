import GaussBonnetChern.EulerIntegral

/-! # Smooth orthonormal frames in the chosen atlas orientation

Gram--Schmidt is applied to the actual positive coordinate basis. Its positive
triangular determinant ensures compatibility with the original atlas orientation
on the whole chart source, with no pointwise choice asserted to be smooth.
-/

noncomputable section
open Bundle Filter Module InnerProductSpace
open scoped Manifold Topology ContDiff

namespace GaussBonnetChern

universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

def chartTangentFrame (e : OpenPartialHomeomorph M (Model n)) (i : Fin (2 * n)) :
    (x : M) → TangentSpace (model n) x :=
  fun x ↦ mfderiv (model n) (model n) e.symm (e x)
    (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)

theorem chartTangentFrame_eq_basis (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) {x : M} (hx : x ∈ e.source) :
    (fun i ↦ chartTangentFrame n M e i x) = sourceCoordinateBasis n M e he x hx := by
  funext i
  rfl

theorem chartTangentFrame_linearIndependent (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) {x : M} (hx : x ∈ e.source) :
    LinearIndependent ℝ (fun i ↦ chartTangentFrame n M e i x) := by
  rw [chartTangentFrame_eq_basis n M e he hx]
  exact (sourceCoordinateBasis n M e he x hx).linearIndependent

theorem contMDiffAt_chartTangentFrame (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (i : Fin (2 * n))
    {x : M} (hx : x ∈ e.source) :
    ContMDiffAt (model n) (model n).tangent ∞ (T% (chartTangentFrame n M e i)) x := by
  have h := (contMDiffAt_coordinateVector n M e he (e x) (e.map_source hx) i).comp x
    (contMDiffAt_of_mem_maximalAtlas he hx)
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  dsimp only [chartTangentFrame, Function.comp_apply, coordinateVector]
  rw [e.left_inv hy]

def chartOrthonormalFrame (e : OpenPartialHomeomorph M (Model n)) (i : Fin (2 * n)) :
    (x : M) → TangentSpace (model n) x :=
  fun x ↦ gramSchmidtNormed ℝ (fun j ↦ chartTangentFrame n M e j x) i

def chartOrthonormalBasis (e : OpenPartialHomeomorph M (Model n)) (x : M) :
    OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x) :=
  gramSchmidtOrthonormalBasis
    (by change Module.finrank ℝ (Model n) = Fintype.card (Fin (2 * n)); simp [Model])
    (fun i ↦ chartTangentFrame n M e i x)

theorem chartOrthonormalBasis_apply (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) {x : M} (hx : x ∈ e.source)
    (i : Fin (2 * n)) :
    chartOrthonormalBasis n M e x i = chartOrthonormalFrame n M e i x := by
  apply gramSchmidtOrthonormalBasis_apply
  apply norm_ne_zero_iff.mp
  rw [gramSchmidtNormed_unit_length i (chartTangentFrame_linearIndependent n M e he hx)]
  norm_num

theorem contMDiffAt_chartOrthonormalFrame (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (i : Fin (2 * n))
    {x : M} (hx : x ∈ e.source) :
    ContMDiffAt (model n) (model n).tangent ∞ (T% (chartOrthonormalFrame n M e i)) x :=
  contMDiffAt_gramSchmidtNormed_tangent n M
    (fun j ↦ contMDiffAt_chartTangentFrame n M e he j hx)
    (chartTangentFrame_linearIndependent n M e he hx) i

theorem contMDiffAt_chartOrthonormalBasis (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (i : Fin (2 * n))
    {x : M} (hx : x ∈ e.source) :
    ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun y ↦ chartOrthonormalBasis n M e y i)) x := by
  apply (contMDiffAt_chartOrthonormalFrame n M e he i hx).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  rw [chartOrthonormalBasis_apply n M e he hy i]

theorem contMDiffOn_chartOrthonormalBasis (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) (i : Fin (2 * n)) :
    ContMDiffOn (model n) (model n).tangent ∞
      (T% (fun y ↦ chartOrthonormalBasis n M e y i)) e.source :=
  fun _ hx ↦ (contMDiffAt_chartOrthonormalBasis n M e he i hx).contMDiffWithinAt

theorem chartOrthonormalBasis_det_pos (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) {x : M} (hx : x ∈ e.source) :
    0 < (chartOrthonormalBasis n M e x).toBasis.det (sourceCoordinateBasis n M e he x hx) := by
  rw [← chartTangentFrame_eq_basis n M e he hx]
  exact gramSchmidtOrthonormalBasis_det_pos _ _ (chartTangentFrame_linearIndependent n M e he hx)

theorem chartOrthonormalBasis_det_coordinateVector_pos
    (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) {y : Model n} (hy : y ∈ e.target) :
    0 < (chartOrthonormalBasis n M e (e.symm y)).toBasis.det (coordinateVector n M e y) := by
  have h := chartOrthonormalBasis_det_pos n M e he (e.map_target hy)
  have hv : (sourceCoordinateBasis n M e he (e.symm y) (e.map_target hy) :
      Fin (2 * n) → TangentSpace (model n) (e.symm y)) = coordinateVector n M e y := by
    funext j
    simp only [sourceCoordinateBasis_apply, coordinateVector]
    rw [e.right_inv hy]
  rwa [hv] at h

theorem chartOrthonormalBasis_orientation (a : FiniteOrientedAtlas n M) (i : Fin a.card)
    {x : M} (hx : x ∈ (a.chart i).source) :
    (chartOrthonormalBasis n M (a.chart i) x).toBasis.orientation = atlasOrientation n M a x := by
  rw [atlasOrientation_eq_chart n M a i x hx, Basis.orientation_eq_iff_det_pos]
  exact chartOrthonormalBasis_det_pos n M (a.chart i) (a.smooth i) hx

/-- The actual chart-positive orthonormal bases change by determinant one
on every overlap, which is the orientation input for gluing angular forms. -/
theorem chartOrthonormalBasis_transition_det_eq_one (a : FiniteOrientedAtlas n M)
    (i j : Fin a.card) {x : M} (hi : x ∈ (a.chart i).source) (hj : x ∈ (a.chart j).source) :
    (chartOrthonormalBasis n M (a.chart i) x).toBasis.det
      (chartOrthonormalBasis n M (a.chart j) x) = 1 := by
  apply OrthonormalBasis.det_to_matrix_orthonormalBasis_of_same_orientation
  rw [chartOrthonormalBasis_orientation n M a i hi,
    chartOrthonormalBasis_orientation n M a j hj]

theorem atlasEulerForm_eq_chartFrame (a : FiniteOrientedAtlas n M) (hn : 0 < n)
    (i : Fin a.card) {x : M} (hx : x ∈ (a.chart i).source) :
    atlasEulerForm n M a hn x = frameEulerForm n M x (chartOrthonormalBasis n M (a.chart i) x) := by
  have ho : (chartOrthonormalBasis n M (a.chart i) x).toBasis.orientation =
      (atlasOrthonormalFrame n M a hn x).toBasis.orientation := by
    rw [chartOrthonormalBasis_orientation n M a i hx, atlasOrthonormalFrame_orientation]
  exact frameEulerForm_eq_of_positive n M x (chartOrthonormalBasis n M (a.chart i) x)
    (atlasOrthonormalFrame n M a hn x) ((Basis.orientation_eq_iff_det_pos _ _).mp ho)

/-- Every point admits an actual smooth orthonormal frame compatible with
the exact atlas orientation used by the frozen GBC statement. -/
theorem exists_localPositiveSmoothOrthonormalBasis (a : FiniteOrientedAtlas n M) (p : M) :
    ∃ (s : Set M) (b : (x : M) → OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace (model n) x)),
      IsOpen s ∧ p ∈ s ∧
      (∀ i, ContMDiffOn (model n) (model n).tangent ∞ (T% (fun x ↦ b x i)) s) ∧
      (∀ x ∈ s, (b x).toBasis.orientation = atlasOrientation n M a x) := by
  obtain ⟨i, hi⟩ := a.covers p
  exact ⟨(a.chart i).source, chartOrthonormalBasis n M (a.chart i),
    (a.chart i).open_source, hi, contMDiffOn_chartOrthonormalBasis n M (a.chart i) (a.smooth i),
    fun _ hx ↦ chartOrthonormalBasis_orientation n M a i hx⟩

end GaussBonnetChern
