import GaussBonnetChern.PositiveOrthonormalFrames
import GaussBonnetChern.OrthonormalFrames
import GaussBonnetChern.GradientLinearization
import GaussBonnetChern.NormalizedSphereLimit
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! # Actual vector fields in orthonormal frame coordinates

The coordinate norm is exactly the user's Riemannian norm. At a zero, metric
compatibility removes the derivative of the moving orthonormal frame. Thus the
rescaling lemmas apply to the actual geometric section, without replacing a
varying metric by a fixed coordinate norm.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle FiberBundle Filter Function
open scoped Manifold ContDiff Topology

namespace GaussBonnetChern

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

def orthonormalFieldCoordinates
    (b : ∀ y : M, OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y))
    (X : (y : M) → TangentSpace (model n) y) (y : M) : Model n :=
  (b y).repr (X y)

@[simp] theorem norm_orthonormalFieldCoordinates
    (b : ∀ y : M, OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y))
    (X : (y : M) → TangentSpace (model n) y) (y : M) :
    ‖orthonormalFieldCoordinates n M b X y‖ = ‖X y‖ :=
  (b y).repr.norm_map _

theorem contMDiffAt_orthonormalFieldCoordinates
    {b : ∀ y : M, OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y)}
    {X : (y : M) → TangentSpace (model n) y} {p : M}
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y => b y i)) p)
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) p) :
    ContMDiffAt (model n) (model n) ∞ (orthonormalFieldCoordinates n M b X) p := by
  have hpi := contMDiffAt_pi_space.mpr (fun i => (hb i).inner_bundle hX)
  have h := (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (n := ∞)).contMDiff.contMDiffAt.comp p hpi
  convert h using 1
  funext y
  ext i
  exact (b y).repr_apply_apply (X y) i

theorem mvfderiv_frameCoefficient_at_zero
    {b : ∀ y : M, OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y)}
    {X : (y : M) → TangentSpace (model n) y} {p : M}
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y => b y i)) p)
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) p)
    (hzero : X p = 0) (i : Fin (2*n)) (v : TangentSpace (model n) p) :
    mvfderiv (model n) (fun y => inner ℝ (b y i) (X y)) p v =
      inner ℝ (b p i) (connection n M X p v) := by
  letI : IsContMDiffRiemannianBundle (model n) 1 (Model n)
      (TangentSpace (model n) : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have h := (connection_isMetricCompatible n M).mvfderiv_inner_eq
    (extend (Model n) (x := p) v)
    ((hb i).mdifferentiableAt (by simp)) (hX.mdifferentiableAt (by simp))
  simpa only [extend_apply_self, hzero, inner_zero_right, zero_add] using h

/-- Frame coordinates after an actual local parametrization. In applications
`g` is a centered inverse chart, not an abstract replacement for the manifold. -/
def chartFieldCoordinates
    (b : ∀ y : M, OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y))
    (X : (y : M) → TangentSpace (model n) y) (g : Model n → M) : Model n → Model n :=
  orthonormalFieldCoordinates n M b X ∘ g

/-- The derivative of a model-space parametrization with its source tangent
space explicitly identified with the model vector space. -/
def parametrizationDerivative (g : Model n → M) (z : Model n) :
    Model n →L[ℝ] TangentSpace (model n) (g z) :=
  (mfderiv (model n) (model n) g z).comp
    (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap

theorem contDiffAt_chartFieldCoordinates
    {b : ∀ y : M, OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y)}
    {X : (y : M) → TangentSpace (model n) y} {g : Model n → M} {z : Model n}
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y => b y i)) (g z))
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g z))
    (hg : ContMDiffAt (model n) (model n) ∞ g z) :
    ContDiffAt ℝ ∞ (chartFieldCoordinates n M b X g) z :=
  ((contMDiffAt_orthonormalFieldCoordinates n M hb hX).comp z hg).contDiffAt

theorem chartFieldCoordinates_zero
    (b : ∀ y : M, OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y))
    {X : (y : M) → TangentSpace (model n) y} (g : Model n → M) {z : Model n}
    (hzero : X (g z) = 0) : chartFieldCoordinates n M b X g z = 0 := by
  simp [chartFieldCoordinates, orthonormalFieldCoordinates, hzero]

theorem hasFDerivAt_chartFieldCoordinates_at_zero
    {b : ∀ y : M, OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y)}
    {X : (y : M) → TangentSpace (model n) y} {g : Model n → M} {z : Model n}
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y => b y i)) (g z))
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g z))
    (hg : ContMDiffAt (model n) (model n) ∞ g z) (hzero : X (g z) = 0) :
    HasFDerivAt (chartFieldCoordinates n M b X g)
      ((b (g z)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((connection n M X (g z)).comp (parametrizationDerivative n M g z))) z := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  let a : M → ℝ := fun y => inner ℝ (b y i) (X y)
  have ha : ContMDiffAt (model n) 𝓘(ℝ) ∞ a (g z) := (hb i).inner_bundle hX
  have hs : DifferentiableAt ℝ (a ∘ g) z :=
    ((ha.comp z hg).contDiffAt).differentiableAt (by simp)
  convert hs.hasFDerivAt.hasFDerivWithinAt using 1
  · funext y
    exact (b (g y)).repr_apply_apply (X (g y)) i
  · ext v
    have hd := mvfderiv_comp z (ha.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))
    rw [mvfderiv_eq_fderiv] at hd
    rw [hd]
    change (b (g z)).repr (connection n M X (g z) (parametrizationDerivative n M g z v)) i =
      mvfderiv (model n) a (g z) (parametrizationDerivative n M g z v)
    rw [OrthonormalBasis.repr_apply_apply]
    exact (mvfderiv_frameCoefficient_at_zero n M hb hX hzero i _).symm

theorem fderiv_chartFieldCoordinates_at_zero
    {b : ∀ y : M, OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y)}
    {X : (y : M) → TangentSpace (model n) y} {g : Model n → M} {z : Model n}
    (hb : ∀ i, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y => b y i)) (g z))
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g z))
    (hg : ContMDiffAt (model n) (model n) ∞ g z) (hzero : X (g z) = 0) :
    fderiv ℝ (chartFieldCoordinates n M b X g) z =
      (b (g z)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((connection n M X (g z)).comp (parametrizationDerivative n M g z)) :=
  (hasFDerivAt_chartFieldCoordinates_at_zero n M hb hX hg hzero).fderiv

theorem det_frame_comp {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (R : V ≃L[ℝ] W) (A : V →L[ℝ] V) (D : W →L[ℝ] V) :
    ((R : V →L[ℝ] W).comp (A.comp D)).det =
      A.det * ((R : V →L[ℝ] W).comp D).det := by
  have heq : (R : V →L[ℝ] W).comp (A.comp D) =
      ((R : V →L[ℝ] W).comp (A.comp (R.symm : W →L[ℝ] V))).comp
        ((R : V →L[ℝ] W).comp D) := by
    ext w
    simp
  rw [heq]
  change LinearMap.det (_ ∘ₗ _) = _
  rw [LinearMap.det_comp]
  congr 1
  simpa only [ContinuousLinearMap.det] using!
    (LinearMap.det_conj A.toLinearMap R.toLinearEquiv)

theorem sign_det_frame_comp {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (R : V ≃L[ℝ] W) (A : V →L[ℝ] V) (D : W →L[ℝ] V)
    (hpos : 0 < ((R : V →L[ℝ] W).comp D).det) :
    Real.sign (((R : V →L[ℝ] W).comp (A.comp D)).det) = Real.sign A.det := by
  rw [det_frame_comp, real_sign_mul, Real.sign_of_pos hpos, mul_one]

def centeredInverseChart (e : OpenPartialHomeomorph M (Model n)) (p : M) (z : Model n) : M :=
 e.symm (e p + z)

theorem centeredInverseChart_zero (e : OpenPartialHomeomorph M (Model n)) {p:M}
 (hp : p∈e.source) : centeredInverseChart n M e p 0 = p := by
 simp only [centeredInverseChart, add_zero, e.left_inv hp]

theorem contMDiffAt_centeredInverseChart (e : OpenPartialHomeomorph M (Model n))
 (he : e∈IsManifold.maximalAtlas (model n) ∞ M) {p:M} (hp:p∈e.source) :
 ContMDiffAt (model n) (model n) ∞ (centeredInverseChart n M e p) 0 := by
 have hg := contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hp)
 have ht : ContMDiffAt (model n) (model n) ∞ (fun z : Model n => e p + z) 0 :=
   contMDiffAt_const.add contMDiffAt_id
 have hg' : ContMDiffAt (model n) (model n) ∞ e.symm ((fun z : Model n => e p + z) 0) := by
   simpa only [add_zero] using hg
 exact hg'.comp 0 ht

theorem normalized_field_coordinates
 (b:∀y:M,OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y))
 (X:(y:M)→TangentSpace (model n) y) (y:M) :
 orthonormalFieldCoordinates n M b (fun x => ‖X x‖⁻¹ • X x) y =
 LocalIndex.normalize (orthonormalFieldCoordinates n M b X y) := by
 simp [orthonormalFieldCoordinates, LocalIndex.normalize]

theorem sign_fderiv_chartFieldCoordinates_at_zero
 {b:∀y:M,OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y)}
 {X:(y:M)→TangentSpace (model n) y} {g:Model n→M} {z:Model n}
 (hb:∀i,ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y => b y i)) (g z))
 (hX:ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g z))
 (hg:ContMDiffAt (model n) (model n) ∞ g z) (hzero:X (g z)=0)
 (hpos:0<((b (g z)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (parametrizationDerivative n M g z)).det) :
 Real.sign (fderiv ℝ (chartFieldCoordinates n M b X g) z).det =
 Real.sign (fieldLinearization n M (g z) X).det := by
 rw [fderiv_chartFieldCoordinates_at_zero n M hb hX hg hzero,
   fieldLinearization_eq_connection n M hX hzero]
 exact sign_det_frame_comp (b (g z)).repr.toContinuousLinearEquiv _ _ hpos

theorem det_orthonormal_repr_comp {d : ℕ} {V : Type*}
 [NormedAddCommGroup V] [InnerProductSpace ℝ V]
 (b:OrthonormalBasis (Fin d) ℝ V) (D:EuclideanSpace ℝ (Fin d) →L[ℝ] V) :
 (b.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp D).det =
 b.toBasis.det (fun i => D (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
 classical
 change LinearMap.det (b.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp D).toLinearMap = _
 rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
   Module.Basis.det_apply]
 congr 1
 ext i j
 simp only [LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply,
   OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
   OrthonormalBasis.coe_toBasis]
 rfl
theorem injective_fderiv_chartFieldCoordinates_at_zero
 {b:∀y:M,OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y)}
 {X:(y:M)→TangentSpace (model n) y} {g:Model n→M} {z:Model n}
 (hb:∀i,ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y => b y i)) (g z))
 (hX:ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g z))
 (hg:ContMDiffAt (model n) (model n) ∞ g z) (hzero:X (g z)=0)
 (hi : Injective (fieldLinearization n M (g z) X))
 (hg' : Injective (parametrizationDerivative n M g z)) :
 Injective (fderiv ℝ (chartFieldCoordinates n M b X g) z) := by
 rw [fieldLinearization_eq_connection n M hX hzero] at hi
 rw [fderiv_chartFieldCoordinates_at_zero n M hb hX hg hzero]
 exact (b (g z)).repr.injective.comp (hi.comp hg')

def normalizedChartField
 (b:∀y:M,OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y))
 (X:(y:M)→TangentSpace (model n) y) (g:Model n→M) (z:Model n) : Model n :=
 (b (g z)).repr (‖X (g z)‖⁻¹ • X (g z))

theorem normalizedChartField_eq
 (b:∀y:M,OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y))
 (X:(y:M)→TangentSpace (model n) y) (g:Model n→M) :
 normalizedChartField n M b X g = LocalIndex.normalize ∘ chartFieldCoordinates n M b X g := by
 funext z
 exact normalized_field_coordinates n M b X (g z)

theorem exists_normalizedChartField_limit
 {b:∀y:M,OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) y)}
 {X:(y:M)→TangentSpace (model n) y} {g:Model n→M}
 (hb:∀i,ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y => b y i)) (g 0))
 (hX:ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g 0))
 (hg:ContMDiffAt (model n) (model n) ∞ g 0) (hzero:X (g 0)=0)
 (hi : Injective (fieldLinearization n M (g 0) X))
 (hg' : Injective (parametrizationDerivative n M g 0)) :
 ∃ L : Model n ≃L[ℝ] Model n,
   fderiv ℝ (chartFieldCoordinates n M b X g) 0 = (L : Model n →L[ℝ] Model n) ∧
   TendstoUniformlyOn (fun r : ℝ => fun u => normalizedChartField n M b X g (r • u))
     (fun u => LocalIndex.normalize (L u)) (𝓝[>] (0 : ℝ)) (Metric.sphere (0 : Model n) 1) ∧
   TendstoUniformlyOn (fun r : ℝ => fderiv ℝ (fun u => normalizedChartField n M b X g (r • u)))
     (fderiv ℝ (fun u => LocalIndex.normalize (L u))) (𝓝[>] (0 : ℝ)) (Metric.sphere (0 : Model n) 1) := by
 let F := chartFieldCoordinates n M b X g
 have hinj : Injective (fderiv ℝ F 0) := injective_fderiv_chartFieldCoordinates_at_zero n M hb hX hg hzero hi hg'
 let L : Model n ≃L[ℝ] Model n :=
   (LinearEquiv.ofBijective (fderiv ℝ F 0).toLinearMap
     ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
 have hL : fderiv ℝ F 0 = (L : Model n →L[ℝ] Model n) := rfl
 have hF : ContDiffAt ℝ 1 F 0 :=
   (contDiffAt_chartFieldCoordinates n M hb hX hg).of_le (by simp)
 have hz : F 0 = 0 := chartFieldCoordinates_zero n M b g hzero
 refine ⟨L,hL,?_,?_⟩
 · simpa only [normalizedChartField_eq,Function.comp_def] using
     LocalIndex.tendstoUniformlyOn_normalize_rescale L (hL ▸ (hF.differentiableAt (by norm_num)).hasFDerivAt) hz
 · simpa only [normalizedChartField_eq,Function.comp_def] using
     LocalIndex.tendstoUniformlyOn_fderiv_normalized_linear L hF hL hz

theorem injective_parametrizationDerivative_centeredInverseChart
 (e : OpenPartialHomeomorph M (Model n))
 (he : e∈IsManifold.maximalAtlas (model n) ∞ M) {p:M} (hp:p∈e.source) :
 Injective (parametrizationDerivative n M (centeredInverseChart n M e p) 0) := by
 have hd : e.MDifferentiable (model n) (model n) :=
   ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
 have ht : MDifferentiableAt (model n) (model n) (fun z : Model n => e p + z) 0 :=
   mdifferentiableAt_const.add mdifferentiableAt_id
 have hg : MDifferentiableAt (model n) (model n) e.symm ((fun z : Model n => e p+z) 0) := by
   simpa only [add_zero] using hd.mdifferentiableAt_symm (e.map_source hp)
 change Injective (((mfderiv (model n) (model n) (e.symm ∘ (fun z : Model n => e p+z)) 0)).comp
   (NormedSpace.fromTangentSpace (0 : Model n)).symm.toContinuousLinearMap)
 rw [mfderiv_comp 0 hg ht]
 have h₁ : Injective (mfderiv (model n) (model n) e.symm (e p + 0)) := by
   apply hd.symm.mfderiv_injective
   change e p + 0 ∈ e.target
   simpa only [add_zero] using e.map_source hp
 have h₂ : Injective (mfderiv (model n) (model n) (fun z : Model n => e p + z) 0) := by
   rw [mfderiv_eq_fderiv, fderiv_const_add]
   intro x y h
   simpa only [fderiv_fun_id, ContinuousLinearMap.id_apply] using! h
 exact h₁.comp (h₂.comp (NormedSpace.fromTangentSpace (0 : Model n)).symm.injective)
theorem centered_chart_frame_det_pos (e : OpenPartialHomeomorph M (Model n))
    (he : e ∈ IsManifold.maximalAtlas (model n) ∞ M) {p : M} (hp : p ∈ e.source) :
    0 < ((chartOrthonormalBasis n M e (centeredInverseChart n M e p 0)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (parametrizationDerivative n M (centeredInverseChart n M e p) 0)).det := by
  have hs := contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hp)
  have ht : MDifferentiableAt (model n) (model n) (fun z : Model n => e p + z) 0 :=
    mdifferentiableAt_const.add mdifferentiableAt_id
  have hg : MDifferentiableAt (model n) (model n) e.symm ((fun z : Model n => e p + z) 0) := by
    simpa only [add_zero] using hs.mdifferentiableAt (by simp)
  have hder := mfderiv_comp 0 hg ht
  change mfderiv (model n) (model n) (centeredInverseChart n M e p) 0 = _ at hder
  have hshift : mfderiv (model n) (model n) (fun z : Model n => e p + z) 0 =
      ContinuousLinearMap.id ℝ (Model n) := by
    rw [mfderiv_eq_fderiv, fderiv_const_add, fderiv_fun_id]
  unfold parametrizationDerivative
  rw [hder, hshift]
  rw [det_orthonormal_repr_comp]
  have hy : e p + 0 ∈ e.target := by simpa only [add_zero] using e.map_source hp
  convert chartOrthonormalBasis_det_coordinateVector_pos n M e he hy using 1 <;> rfl


def positiveChartField (a : FiniteOrientedAtlas n M) (i : Fin a.card)
    (X : (y : M) → TangentSpace (model n) y) (p : M) : Model n → Model n :=
  chartFieldCoordinates n M (chartOrthonormalBasis n M (a.chart i)) X
    (centeredInverseChart n M (a.chart i) p)

def positiveNormalizedChartField (a : FiniteOrientedAtlas n M) (i : Fin a.card)
    (X : (y : M) → TangentSpace (model n) y) (p : M) : Model n → Model n :=
  normalizedChartField n M (chartOrthonormalBasis n M (a.chart i)) X
    (centeredInverseChart n M (a.chart i) p)

theorem exists_positive_normalized_field_limit (a : FiniteOrientedAtlas n M) {p : M}
    {X : (y : M) → TangentSpace (model n) y}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) p)
    (hzero : X p = 0) (hi : Injective (fieldLinearization n M p X)) :
    ∃ (i : Fin a.card) (L : Model n ≃L[ℝ] Model n),
      p ∈ (a.chart i).source ∧
      fderiv ℝ (positiveChartField n M a i X p) 0 = (L : Model n →L[ℝ] Model n) ∧
      Real.sign (L : Model n →L[ℝ] Model n).det = Real.sign (fieldLinearization n M p X).det ∧
      TendstoUniformlyOn (fun r : ℝ => fun u => positiveNormalizedChartField n M a i X p (r • u))
        (fun u => LocalIndex.normalize (L u)) (𝓝[>] (0 : ℝ)) (Metric.sphere (0 : Model n) 1) ∧
      TendstoUniformlyOn (fun r : ℝ => fderiv ℝ (fun u => positiveNormalizedChartField n M a i X p (r • u)))
        (fderiv ℝ (fun u => LocalIndex.normalize (L u))) (𝓝[>] (0 : ℝ)) (Metric.sphere (0 : Model n) 1) := by
  obtain ⟨i, hp⟩ := a.covers p
  let e := a.chart i
  let b := chartOrthonormalBasis n M e
  let g := centeredInverseChart n M e p
  have hgp : g 0 = p := centeredInverseChart_zero n M e hp
  have hXp : ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g 0) := by rwa [hgp]
  have hz : X (g 0) = 0 := by rwa [hgp]
  have hii : Injective (fieldLinearization n M (g 0) X) := by rwa [hgp]
  have hb : ∀ j, ContMDiffAt (model n) (model n).tangent ∞ (T% (fun y => b y j)) (g 0) := by
    intro j
    rw [hgp]
    exact contMDiffAt_chartOrthonormalBasis n M e (a.smooth i) j hp
  have hg := contMDiffAt_centeredInverseChart n M e (a.smooth i) hp
  have hgi := injective_parametrizationDerivative_centeredInverseChart n M e (a.smooth i) hp
  obtain ⟨L, hL, hC, hD⟩ := exists_normalizedChartField_limit n M hb hXp hg hz hii hgi
  have hsign := sign_fderiv_chartFieldCoordinates_at_zero n M hb hXp hg hz
    (centered_chart_frame_det_pos n M e (a.smooth i) hp)
  rw [hL, hgp] at hsign
  exact ⟨i, L, hp, hL, hsign, hC, hD⟩
end GaussBonnetChern




