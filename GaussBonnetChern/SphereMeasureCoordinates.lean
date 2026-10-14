import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Polar measure in actual sphere coordinates

The measure used here is the canonical inner-product volume. The radial map is
formed from an actual unit-vector parametrization; its image is the cone used
in `Measure.toSphere`, and its differential is an ordinary Frechet derivative.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module MeasureTheory Metric Set Function
open scoped Manifold Pointwise ENNReal ContDiff

namespace GaussBonnetChern.SphereMeasureCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {d : ℕ}

/-- Orthonormal coordinates, with the ordinary finite product norm. -/
def ambientCoordinates (b : OrthonormalBasis (Fin (d+1)) ℝ E) :
    E ≃L[ℝ] (Fin (d+1) → ℝ) :=
  b.repr.toContinuousLinearEquiv.trans (PiLp.continuousLinearEquiv 2 ℝ _)

@[simp] theorem ambientCoordinates_apply (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (v : E) (i : Fin (d+1)) : ambientCoordinates b v i = b.repr v i := rfl

theorem ambientCoordinates_measurePreserving (b : OrthonormalBasis (Fin (d+1)) ℝ E) :
    MeasurePreserving (ambientCoordinates b) volume volume :=
  (PiLp.volume_preserving_ofLp (Fin (d+1))).comp b.measurePreserving_repr

/-- First coordinate is radius, the remaining coordinates parametrize directions. -/
def coneMap (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    (x : Fin (d+1) → ℝ) : E :=
  x 0 • (ψ (Fin.tail x) : E)

def coneDomain (s : Set (Fin d → ℝ)) : Set (Fin (d+1) → ℝ) :=
  {x | x 0 ∈ Ioo (0 : ℝ) 1 ∧ Fin.tail x ∈ s}

theorem measurableSet_coneDomain {s : Set (Fin d → ℝ)} (hs : MeasurableSet s) :
    MeasurableSet (coneDomain s) :=
  (measurable_pi_apply 0 measurableSet_Ioo).inter
    (hs.preimage (by fun_prop))

theorem coneMap_image (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    (s : Set (Fin d → ℝ)) :
    coneMap ψ '' coneDomain s = Ioo (0 : ℝ) 1 • ((↑) '' (ψ '' s)) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x 0, hx.1, (ψ (Fin.tail x) : E), ⟨ψ (Fin.tail x),
      ⟨Fin.tail x, hx.2, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨r, hr, _, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨Fin.cons r y, by simpa [coneDomain] using And.intro hr hy,
      by simp [coneMap]⟩

theorem norm_coneMap (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    {x : Fin (d+1) → ℝ} (hx : 0 ≤ x 0) : ‖coneMap ψ x‖ = x 0 := by
  simp [coneMap, norm_smul, norm_eq_of_mem_sphere, abs_of_nonneg hx]

theorem coneMap_injOn (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    {s : Set (Fin d → ℝ)} (hψ : InjOn ψ s) : InjOn (coneMap ψ) (coneDomain s) := by
  intro x hx y hy hxy
  have hr : x 0 = y 0 := by
    simpa [norm_coneMap ψ hx.1.1.le, norm_coneMap ψ hy.1.1.le] using congrArg norm hxy
  have hv : (ψ (Fin.tail x) : E) = (ψ (Fin.tail y) : E) := by
    apply (smul_right_injective E (ne_of_gt hx.1.1))
    simpa only [coneMap, hr] using hxy
  have ht := hψ hx.2 hy.2 (Subtype.ext hv)
  exact Fin.cons_self_tail x ▸ Fin.cons_self_tail y ▸ congrArg₂ Fin.cons hr ht

/-- The actual cone change-of-variables identity. No chart Jacobian is assumed. -/
theorem toSphere_image_eq_cone_jacobian
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    {s : Set (Fin d → ℝ)} (hs : MeasurableSet s)
    (himage : MeasurableSet (ψ '' s)) (hψ : InjOn ψ s)
    (D : (Fin (d+1) → ℝ) → (Fin (d+1) → ℝ) →L[ℝ] (Fin (d+1) → ℝ))
    (hD : ∀ x ∈ coneDomain s,
      HasFDerivWithinAt (ambientCoordinates b ∘ coneMap ψ) (D x) (coneDomain s) x) :
    (volume : Measure E).toSphere (ψ '' s) = (d+1) *
      ∫⁻ x in coneDomain s, ENNReal.ofReal |(D x).det| := by
  have hdim : finrank ℝ E = d+1 := by simpa using finrank_eq_card_basis b.toBasis
  rw [Measure.toSphere_apply' _ himage, hdim, ← coneMap_image]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1
  have hinj : InjOn (ambientCoordinates b ∘ coneMap ψ) (coneDomain s) :=
    (ambientCoordinates b).injective.injOn.comp (coneMap_injOn ψ hψ) (mapsTo_image _ _)
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_coneDomain hs) hD hinj (fun _ ↦ (1 : ℝ≥0∞))
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul, mul_one] at hcov
  rw [Set.image_comp] at hcov
  rw [← hcov]
  simpa only [(ambientCoordinates b).injective.preimage_image] using
    (ambientCoordinates_measurePreserving b).measure_preimage_emb
      (ambientCoordinates b).toHomeomorph.measurableEmbedding
      ((ambientCoordinates b) '' (coneMap ψ '' coneDomain s))

/-- The ordinary tail projection as a continuous linear map. -/
def tailLinear (d : ℕ) : (Fin (d+1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.succ

@[simp] theorem tailLinear_apply (x : Fin (d+1) → ℝ) :
    tailLinear d x = Fin.tail x := rfl

/-- The actual derivative of the radial parametrization in product coordinates. -/
def coneDerivative (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    (Dψ : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E)
    (x : Fin (d+1) → ℝ) : (Fin (d+1) → ℝ) →L[ℝ] E :=
  x 0 • (Dψ (Fin.tail x)).comp (tailLinear d) +
    (ContinuousLinearMap.proj 0).smulRight (ψ (Fin.tail x) : E)

theorem hasFDerivAt_coneMap (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    (Dψ : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E)
    (x : Fin (d+1) → ℝ)
    (hψ : HasFDerivAt (fun y ↦ (ψ y : E)) (Dψ (Fin.tail x)) (Fin.tail x)) :
    HasFDerivAt (coneMap ψ) (coneDerivative ψ Dψ x) x :=
  (hasFDerivAt_apply 0 x).smul (hψ.comp x (tailLinear d).hasFDerivAt)

theorem det_ambientCoordinates_comp
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (D : (Fin (d+1) → ℝ) →L[ℝ] E) :
    ((ambientCoordinates b).toContinuousLinearMap.comp D).det =
      b.toBasis.det (fun i ↦ D (Pi.basisFun ℝ (Fin (d+1)) i)) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin (d+1))),
    Basis.det_apply]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply, b.coe_toBasis_repr_apply]

theorem coneDerivative_basis_zero (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    (Dψ : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E) (x : Fin (d+1) → ℝ) :
    coneDerivative ψ Dψ x (Pi.basisFun ℝ (Fin (d+1)) 0) = (ψ (Fin.tail x) : E) := by
  have ht : tailLinear d (Pi.basisFun ℝ (Fin (d+1)) 0) = 0 := by
    ext i
    simp [tailLinear, Pi.basisFun_apply]
  simp only [coneDerivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ht]
  simp [Pi.basisFun_apply]

theorem coneDerivative_basis_succ (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    (Dψ : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E) (x : Fin (d+1) → ℝ) (i : Fin d) :
    coneDerivative ψ Dψ x (Pi.basisFun ℝ (Fin (d+1)) i.succ) =
      x 0 • Dψ (Fin.tail x) (Pi.basisFun ℝ (Fin d) i) := by
  have ht : tailLinear d (Pi.basisFun ℝ (Fin (d+1)) i.succ) =
      Pi.basisFun ℝ (Fin d) i := by
    ext j
    simp [tailLinear, Pi.basisFun_apply, Pi.single_apply]
  simp only [coneDerivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ht]
  simp [Pi.basisFun_apply]

theorem determinant_cons_smul (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (u : E) (v : Fin d → E) (r : ℝ) :
    b.toBasis.det (Fin.cons u (fun i ↦ r • v i)) =
      r^d * b.toBasis.det (Fin.cons u v) := by
  have h := b.toBasis.det.map_smul_univ (Fin.cons 1 (fun _ : Fin d ↦ r)) (Fin.cons u v)
  have hv : (fun i : Fin (d+1) ↦
      (Fin.cons 1 (fun _ : Fin d ↦ r) : Fin (d+1) → ℝ) i •
        (Fin.cons u v : Fin (d+1) → E) i) =
      Fin.cons u (fun i ↦ r • v i) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  simpa only [hv, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul, smul_eq_mul] using h

theorem det_coneDerivative (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    (Dψ : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E) (x : Fin (d+1) → ℝ) :
    ((ambientCoordinates b).toContinuousLinearMap.comp (coneDerivative ψ Dψ x)).det =
      (x 0)^d * b.toBasis.det (Fin.cons (ψ (Fin.tail x) : E)
        (fun i ↦ Dψ (Fin.tail x) (Pi.basisFun ℝ (Fin d) i))) := by
  rw [det_ambientCoordinates_comp]
  have h : (fun i ↦ coneDerivative ψ Dψ x (Pi.basisFun ℝ (Fin (d+1)) i)) =
      Fin.cons (ψ (Fin.tail x) : E)
        (fun i ↦ x 0 • Dψ (Fin.tail x) (Pi.basisFun ℝ (Fin d) i)) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using coneDerivative_basis_zero ψ Dψ x
    · simpa using coneDerivative_basis_succ ψ Dψ x j
  rw [h, determinant_cons_smul]

theorem radialMoment (d : ℕ) :
    ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r^d) =
      ENNReal.ofReal (1 / ((d : ℝ)+1)) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal (intervalIntegral.intervalIntegrable_pow d).1]
  · rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp [integral_pow]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact pow_nonneg hr.1.le _

theorem lintegral_coneDomain {s : Set (Fin d → ℝ)}
    (J : (Fin d → ℝ) → ℝ≥0∞) (hJ : AEMeasurable J (volume.restrict s)) :
    (∫⁻ x in coneDomain s, ENNReal.ofReal ((x 0)^d) * J (Fin.tail x)) =
      ENNReal.ofReal (1 / ((d : ℝ)+1)) * ∫⁻ y in s, J y := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) ↦ ℝ) 0
  have hp := volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) ↦ ℝ) 0
  have h := hp.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun p : ℝ × (Fin d → ℝ) ↦ ENNReal.ofReal (p.1^d) * J p.2) (Ioo 0 1 ×ˢ s)
  change (∫⁻ x in coneDomain s, ENNReal.ofReal ((x 0)^d) * J (Fin.tail x)) = _ at h
  rw [h]
  change (∫⁻ p in Ioo (0 : ℝ) 1 ×ˢ s, ENNReal.ofReal (p.1^d) * J p.2
    ∂(volume.prod volume)) = _
  rw [← Measure.prod_restrict]
  have hf : AEMeasurable (fun r : ℝ ↦ ENNReal.ofReal (r^d))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by fun_prop
  simpa only [radialMoment] using lintegral_prod_mul hf hJ

/-- Signed outward-normal-first Jacobian of a unit-vector parametrization. -/
def normalJacobian (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (ψ : (Fin d → ℝ) → sphere (0 : E) 1) (y : Fin d → ℝ) : ℝ :=
  b.toBasis.det (Fin.cons (ψ y : E)
    (fun i ↦ fderiv ℝ (fun z ↦ (ψ z : E)) y (Pi.basisFun ℝ (Fin d) i)))

theorem normalJacobian_aemeasurable (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    {s : Set (Fin d → ℝ)} (hs : MeasurableSet s) (hψ : ContinuousOn ψ s) :
    AEMeasurable (fun y ↦ ENNReal.ofReal |normalJacobian b ψ y|) (volume.restrict s) := by
  have hdet : Continuous fun v : Fin (d+1) → E ↦ b.toBasis.det v :=
    b.toBasis.continuous_toMatrix.matrix_det
  have hv : AEMeasurable (fun y ↦ (Fin.cons (ψ y : E)
      (fun i ↦ fderiv ℝ (fun z ↦ (ψ z : E)) y (Pi.basisFun ℝ (Fin d) i)) :
        Fin (d+1) → E))
      (volume.restrict s) := by
    apply aemeasurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact (continuous_subtype_val.comp_continuousOn hψ).aemeasurable hs
    · exact (measurable_fderiv_apply_const ℝ (fun z ↦ (ψ z : E)) _).aemeasurable
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (hdet.abs.measurable.comp_aemeasurable hv)

/-- Actual polar sphere measure equals the integral of the absolute normal
Jacobian in any differentiable injective unit-vector parametrization. -/
theorem toSphere_image_eq_lintegral_normalJacobian
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (ψ : (Fin d → ℝ) → sphere (0 : E) 1)
    {s : Set (Fin d → ℝ)} (hs : MeasurableSet s)
    (hψcont : ContinuousOn ψ s) (hψinj : InjOn ψ s)
    (hψdiff : ∀ y ∈ s, DifferentiableAt ℝ (fun z ↦ (ψ z : E)) y) :
    (volume : Measure E).toSphere (ψ '' s) =
      ∫⁻ y in s, ENNReal.ofReal |normalJacobian b ψ y| := by
  let Dψ := fderiv ℝ (fun z ↦ (ψ z : E))
  let D := fun x ↦ (ambientCoordinates b).toContinuousLinearMap.comp
    (coneDerivative ψ Dψ x)
  have hD : ∀ x ∈ coneDomain s,
      HasFDerivWithinAt (ambientCoordinates b ∘ coneMap ψ) (D x) (coneDomain s) x := by
    intro x hx
    exact ((ambientCoordinates b).hasFDerivAt.comp x
      (hasFDerivAt_coneMap ψ Dψ x (hψdiff _ hx.2).hasFDerivAt)).hasFDerivWithinAt
  rw [toSphere_image_eq_cone_jacobian b ψ hs
    (hs.image_of_continuousOn_injOn hψcont hψinj) hψinj D hD]
  have h : (∫⁻ x in coneDomain s, ENNReal.ofReal |(D x).det|) =
      ∫⁻ x in coneDomain s, ENNReal.ofReal ((x 0)^d) *
        ENNReal.ofReal |normalJacobian b ψ (Fin.tail x)| := by
    apply setLIntegral_congr_fun (measurableSet_coneDomain hs)
    intro x hx
    dsimp [D]
    rw [det_coneDerivative, abs_mul, abs_of_nonneg (pow_nonneg hx.1.1.le _),
      ENNReal.ofReal_mul (pow_nonneg hx.1.1.le _)]
    rfl
  rw [h, lintegral_coneDomain _ (normalJacobian_aemeasurable b ψ hs hψcont), ← mul_assoc]
  have hc : ((d : ℝ≥0∞)+1) * ENNReal.ofReal (1 / ((d : ℝ)+1)) = 1 := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    rw [ENNReal.ofReal_add (Nat.cast_nonneg d) zero_le_one]
    simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one, one_div, one_mul]
    exact ENNReal.mul_inv_cancel (by positivity) (by simp)
  rw [hc, one_mul]

section Charts
variable [Fact (finrank ℝ E = d+1)]

theorem differentiableAt_coe_symm_chart
    (e : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : E) 1))
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ e.target) :
    DifferentiableAt ℝ (fun z ↦ (e.symm z : E)) y := by
  have h : ContDiffAt ℝ ∞ (fun z ↦ (e.symm z : E)) y :=
    ((contMDiff_coe_sphere (e.symm y)).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas he hy)).contDiffAt
  exact h.differentiableAt (by simp)

theorem normalJacobian_chart
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : E) 1))
    (y : Fin d → ℝ) (hy : WithLp.toLp 2 y ∈ e.target) :
    normalJacobian b (fun z ↦ e.symm (WithLp.toLp 2 z)) y =
      b.toBasis.det (Fin.cons (e.symm (WithLp.toLp 2 y) : E)
        (fun i ↦ fderiv ℝ (fun z ↦ (e.symm z : E)) (WithLp.toLp 2 y)
          (EuclideanSpace.basisFun (Fin d) ℝ i))) := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).symm
  have hd := (differentiableAt_coe_symm_chart e he hy).hasFDerivAt.comp y L.hasFDerivAt
  simp only [Function.comp_def] at hd
  unfold normalJacobian
  rw [hd.fderiv]
  congr 1

/-- Polar sphere measure in every genuine smooth sphere chart, with the
outward normal in the first determinant slot and the standard Euclidean basis
in the remaining slots. The equality includes dimension zero. -/
theorem toSphere_image_symm_chart
    (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (e : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : E) 1))
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : MeasurableSet s) (hst : s ⊆ e.target) :
    (volume : Measure E).toSphere (e.symm '' s) =
      ∫⁻ y in s, ENNReal.ofReal |b.toBasis.det (Fin.cons (e.symm y : E)
        (fun i ↦ fderiv ℝ (fun z ↦ (e.symm z : E)) y
          (EuclideanSpace.basisFun (Fin d) ℝ i)))| := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).symm
  let ψ : (Fin d → ℝ) → sphere (0 : E) 1 := fun y ↦ e.symm (L y)
  let t := L ⁻¹' s
  have ht : MeasurableSet t := hs.preimage L.continuous.measurable
  have htgt : MapsTo L t e.target := fun _ hx ↦ hst hx
  have hc : ContinuousOn ψ t := e.continuousOn_symm.comp L.continuous.continuousOn htgt
  have hi : InjOn ψ t := (e.symm.injOn).comp L.injective.injOn htgt
  have hd : ∀ y ∈ t, DifferentiableAt ℝ (fun z ↦ (ψ z : E)) y := by
    intro y hy
    exact (differentiableAt_coe_symm_chart e he (hst hy)).comp y L.differentiableAt
  have h := toSphere_image_eq_lintegral_normalJacobian b ψ ht hc hi hd
  have him : ψ '' t = e.symm '' s := by
    change (e.symm ∘ L) '' (L ⁻¹' s) = _
    rw [Set.image_comp, L.surjective.image_preimage]
  rw [him] at h
  rw [h]
  have hcj : (∫⁻ y in t, ENNReal.ofReal |normalJacobian b ψ y|) =
      ∫⁻ y in t, ENNReal.ofReal |b.toBasis.det (Fin.cons (e.symm (L y) : E)
        (fun i ↦ fderiv ℝ (fun z ↦ (e.symm z : E)) (L y)
          (EuclideanSpace.basisFun (Fin d) ℝ i)))| := by
    apply setLIntegral_congr_fun ht
    intro y hy
    exact congrArg (fun r : ℝ ↦ ENNReal.ofReal |r|)
      (normalJacobian_chart b e he y (hst hy))
  rw [hcj]
  simpa only [t, L, PiLp.coe_symm_continuousLinearEquiv] using
    (PiLp.volume_preserving_toLp (Fin d)).setLIntegral_comp_preimage_emb
      L.toHomeomorph.measurableEmbedding
      (fun y : EuclideanSpace ℝ (Fin d) ↦ ENNReal.ofReal |b.toBasis.det
        (Fin.cons (e.symm y : E) (fun i ↦ fderiv ℝ (fun z ↦ (e.symm z : E)) y
          (EuclideanSpace.basisFun (Fin d) ℝ i)))|) s

end Charts

end GaussBonnetChern.SphereMeasureCoordinates
