import GaussBonnetChern.SphereFormIntegration
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Finite atlases positively oriented by the outward sphere form

The sign of an actual smooth nonzero chart density is fixed by shrinking its
domain. A coordinate reflection reverses the sign when necessary. Compactness
then produces a finite cover. Positive dimension is essential for the reflection.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module Metric
open scoped Manifold ContDiff Topology

namespace GaussBonnetChern

def sphereCoordinateReflection {d : ℕ} (i₀ : Fin d) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ({ toFun := fun x ↦ WithLp.toLp 2 (fun i ↦ if i = i₀ then -x i else x i)
     invFun := fun x ↦ WithLp.toLp 2 (fun i ↦ if i = i₀ then -x i else x i)
     left_inv := by intro x; ext i; by_cases hi : i = i₀ <;> simp [hi]
     right_inv := by intro x; ext i; by_cases hi : i = i₀ <;> simp [hi]
     map_add' := by intro x y; ext i; by_cases hi : i = i₀ <;> simp [hi, add_comm]
     map_smul' := by intro c x; ext i; by_cases hi : i = i₀ <;> simp [hi] } :
       EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d)).toContinuousLinearEquiv

@[simp] theorem sphereCoordinateReflection_apply {d : ℕ} (i₀ : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    sphereCoordinateReflection i₀ x i = if i = i₀ then -x i else x i := rfl

@[simp] theorem sphereCoordinateReflection_symm {d : ℕ} (i₀ : Fin d) :
    (sphereCoordinateReflection i₀).symm = sphereCoordinateReflection i₀ := rfl

theorem sphereCoordinateReflection_basis {d : ℕ} (i₀ : Fin d) :
    (fun i ↦ sphereCoordinateReflection i₀ (EuclideanSpace.basisFun (Fin d) ℝ i)) =
      Function.update (EuclideanSpace.basisFun (Fin d) ℝ) i₀
        (-EuclideanSpace.basisFun (Fin d) ℝ i₀) := by
  funext i
  ext j
  by_cases hi : i = i₀ <;> by_cases hj : j = i₀ <;>
    simp [hi, hj, EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]

theorem sphereCoordinateReflection_form {d : ℕ} (i₀ : Fin d)
    (α : (EuclideanSpace ℝ (Fin d)) [⋀^Fin d]→L[ℝ] ℝ) :
    α (fun i ↦ sphereCoordinateReflection i₀ (EuclideanSpace.basisFun (Fin d) ℝ i)) =
      -α (EuclideanSpace.basisFun (Fin d) ℝ) := by
  rw [sphereCoordinateReflection_basis]
  change α.toMultilinearMap (Function.update (EuclideanSpace.basisFun (Fin d) ℝ) i₀
    (-EuclideanSpace.basisFun (Fin d) ℝ i₀)) = -α.toMultilinearMap _
  rw [MultilinearMap.map_update_neg, Function.update_eq_self]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (finrank ℝ E = d+1)]

theorem sphereChart_transLinear_smooth
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (r : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    e.transHomeomorph r.toHomeomorph ∈
      IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1) := by
  apply (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).mpr
  constructor
  · exact r.contDiff.contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas he)
  · exact (contMDiffOn_symm_of_mem_maximalAtlas he).comp
      r.symm.contDiff.contMDiff.contMDiffOn (fun _ hy ↦ hy)

theorem sphereChartDensity_reflection (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (i₀ : Fin d) (y : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ (e.transHomeomorph (sphereCoordinateReflection i₀).toHomeomorph).target) :
    sphereChartDensity b (e.transHomeomorph (sphereCoordinateReflection i₀).toHomeomorph) y =
      -sphereChartDensity b e (sphereCoordinateReflection i₀ y) := by
  let r := sphereCoordinateReflection i₀
  have hyr : r.symm y ∈ e.target := hy
  have hD := mfderiv_comp y
    ((contMDiffAt_symm_of_mem_maximalAtlas he hyr).mdifferentiableAt (by simp))
    ((r.symm.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp) y)
  rw [mfderiv_eq_fderiv, r.symm.fderiv] at hD
  change sphereVolumeForm b (e.symm (r.symm y))
    (fun i ↦ mfderiv (𝓡 d) (𝓡 d) (e.symm ∘ r.symm) y
      (EuclideanSpace.basisFun (Fin d) ℝ i)) = _
  rw [hD]
  exact sphereCoordinateReflection_form i₀
    ((sphereVolumeForm b (e.symm (r.symm y))).compContinuousLinearMap
      (mfderiv (𝓡 d) (𝓡 d) e.symm (r.symm y)))

theorem sphereChart_exists_positive_restriction
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (u : sphere (0:E) 1) (hu : u ∈ e.source)
    (hpos : 0 < sphereChartDensity b e (e u)) :
    ∃ f : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)),
      f ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1) ∧ u ∈ f.source ∧
      ∀ y ∈ f.target, 0 < sphereChartDensity b f y := by
  let V := e.target ∩ sphereChartDensity b e ⁻¹' Set.Ioi 0
  have hV : IsOpen V :=
    (contDiffOn_sphereChartDensity b e he).continuousOn.isOpen_inter_preimage
      e.open_target isOpen_Ioi
  let U := e.source ∩ e ⁻¹' V
  have hU : IsOpen U := e.isOpen_inter_preimage hV
  let f := e.restr U
  refine ⟨f, restr_mem_maximalAtlas _ he hU, ?_, ?_⟩
  · change u ∈ (e.restr U).source
    rw [e.restr_source' U hU]
    exact ⟨hu, hu, e.map_source hu, hpos⟩
  · intro y hy
    have hs : f.symm y ∈ e.source ∩ U := by
      simpa only [f, e.restr_source' U hU] using f.map_target hy
    have hp := hs.2.2.2
    change 0 < sphereChartDensity b e y
    change 0 < sphereChartDensity b e (e (f.symm y)) at hp
    simpa only [show e (f.symm y) = y from f.right_inv hy] using hp

/-- Every point admits a genuine smooth chart on which the outward density is positive. -/
theorem exists_sphere_positive_chart (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (hd : 0 < d) (u : sphere (0:E) 1) :
    ∃ e : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)),
      e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1) ∧ u ∈ e.source ∧
      ∀ y ∈ e.target, 0 < sphereChartDensity b e y := by
  let e := chartAt (EuclideanSpace ℝ (Fin d)) u
  have he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1) :=
    IsManifold.chart_mem_maximalAtlas u
  have hu : u ∈ e.source := mem_chart_source _ _
  have hn := sphereChartDensity_ne_zero b e he (e u) (e.map_source hu)
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · let i₀ : Fin d := ⟨0, hd⟩
    let r := sphereCoordinateReflection i₀
    let f := e.transHomeomorph r.toHomeomorph
    have hf := sphereChart_transLinear_smooth e he r
    have hfu : u ∈ f.source := hu
    apply sphereChart_exists_positive_restriction b f hf u hfu
    rw [sphereChartDensity_reflection b e he i₀ (f u) (f.map_source hfu)]
    have hr : r (f u) = e u := r.symm_apply_apply (e u)
    change 0 < -sphereChartDensity b e (r (f u))
    rw [hr]
    exact neg_pos.mpr hneg
  · exact sphereChart_exists_positive_restriction b e he u hu hpos

/-- Finite charts, genuinely smooth and positively oriented by the outward form. -/
structure FiniteSphereOrientedAtlas (b : OrthonormalBasis (Fin (d+1)) ℝ E) where
  card : ℕ
  chart : Fin card → OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d))
  smooth : ∀ i, chart i ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1)
  covers : ∀ x, ∃ i, x ∈ (chart i).source
  positive_density : ∀ i y, y ∈ (chart i).target → 0 < sphereChartDensity b (chart i) y

/-- Compactness makes the positive atlas finite; no orientation-existence premise is used. -/
theorem nonempty_finiteSphereOrientedAtlas (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (hd : 0 < d) : Nonempty (FiniteSphereOrientedAtlas b) := by
  classical
  letI : FiniteDimensional ℝ E := b.toBasis.finiteDimensional_of_finite
  letI : CompactSpace (sphere (0:E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  choose e he hu hp using exists_sphere_positive_chart b hd
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (e x).source) (fun x ↦ (e x).open_source)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hu x⟩)
  let a := (Fintype.equivFin t).symm
  refine ⟨⟨Fintype.card t, fun i ↦ e (a i).val, fun i ↦ he _, ?_, fun i ↦ hp _⟩⟩
  intro x
  obtain ⟨u, hut, hux⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  refine ⟨(Fintype.equivFin t) ⟨u, hut⟩, ?_⟩
  simpa only [a, Equiv.symm_apply_apply] using hux

/-- A chosen finite atlas for the actual outward orientation. -/
def sphereOrientedAtlas (b : OrthonormalBasis (Fin (d+1)) ℝ E) (hd : 0 < d) :
    FiniteSphereOrientedAtlas b := (nonempty_finiteSphereOrientedAtlas b hd).some

theorem FiniteSphereOrientedAtlas.exists_partition
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (a : FiniteSphereOrientedAtlas b) :
    ∃ ρ : SmoothPartitionOfUnity (Fin a.card) (𝓡 d) (sphere (0:E) 1) Set.univ,
      ρ.IsSubordinate (fun i ↦ (a.chart i).source) := by
  letI : FiniteDimensional ℝ E := b.toBasis.finiteDimensional_of_finite
  letI : CompactSpace (sphere (0:E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  apply SmoothPartitionOfUnity.exists_isSubordinate (𝓡 d) isClosed_univ
    (fun i ↦ (a.chart i).source) (fun i ↦ (a.chart i).open_source)
  intro x _
  obtain ⟨i, hi⟩ := a.covers x
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- The actual outward density transforms by the signed transition determinant. -/
theorem sphereChartDensity_transition
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e e' : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (he' : e' ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ e.target) (hy' : e.symm y ∈ e'.source) :
    sphereChartDensity b e y = sphereChartDensity b e' (e' (e.symm y)) *
      LinearMap.det (fderiv ℝ (e' ∘ e.symm) y).toLinearMap := by
  let v := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let A := DifferentialForm.chartRepresentation e' (sphereVolumeForm b) (e' (e.symm y))
  let L := fderiv ℝ (e' ∘ e.symm) y
  have h := congrArg (fun W ↦ W v)
    (DifferentialForm.transition_pullback e e' he he' (sphereVolumeForm b) y hy hy')
  change sphereChartDensity b e y = A (fun i ↦ L (v i)) at h
  have hA := congrArg (fun W ↦ W (fun i ↦ L (v i)))
    (A.toAlternatingMap.eq_smul_basis_det v)
  change A (fun i ↦ L (v i)) = A v * v.det (fun i ↦ L (v i)) at hA
  have hdet : v.det (fun i ↦ L (v i)) = LinearMap.det L.toLinearMap := by
    change v.det (L.toLinearMap ∘ v) = _
    rw [Basis.det_comp, Basis.det_self, mul_one]
  rw [h, hA, hdet]
  rfl



/-- Positive outward densities force a positive Jacobian on every chart overlap. -/
theorem sphereChart_positive_transition
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e e' : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (he' : e' ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (hp : ∀ y ∈ e.target, 0 < sphereChartDensity b e y)
    (hp' : ∀ y ∈ e'.target, 0 < sphereChartDensity b e' y)
    (x : sphere (0:E) 1) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    0 < LinearMap.det (fderiv ℝ (e' ∘ e.symm) (e x)).toLinearMap := by
  have h := sphereChartDensity_transition b e e' he he' (e x) (e.map_source hx)
    (by simpa only [e.left_inv hx] using hx')
  rw [e.left_inv hx] at h
  exact (mul_pos_iff_of_pos_left (hp' (e' x) (e'.map_source hx'))).mp
    (h ▸ hp (e x) (e.map_source hx))

/-- Any two such finite atlases give positively oriented chart transitions. -/
theorem FiniteSphereOrientedAtlas.positive_cross_transition
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (a a' : FiniteSphereOrientedAtlas b) (i : Fin a.card) (j : Fin a'.card)
    (x : sphere (0:E) 1) (hx : x ∈ (a.chart i).source) (hx' : x ∈ (a'.chart j).source) :
    0 < LinearMap.det (fderiv ℝ (a'.chart j ∘ (a.chart i).symm) ((a.chart i) x)).toLinearMap :=
  sphereChart_positive_transition b _ _ (a.smooth i) (a'.smooth j)
    (a.positive_density i) (a'.positive_density j) x hx hx'

/-- The finite atlas is positively oriented in the ordinary Jacobian sense. -/
theorem FiniteSphereOrientedAtlas.positive_transition
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (a : FiniteSphereOrientedAtlas b) (i j : Fin a.card)
    (x : sphere (0:E) 1) (hx : x ∈ (a.chart i).source) (hx' : x ∈ (a.chart j).source) :
    0 < LinearMap.det (fderiv ℝ (a.chart j ∘ (a.chart i).symm) ((a.chart i) x)).toLinearMap :=
  a.positive_cross_transition b a i j x hx hx'

end GaussBonnetChern
