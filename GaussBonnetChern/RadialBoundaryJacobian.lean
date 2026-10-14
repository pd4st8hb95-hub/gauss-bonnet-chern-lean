import GaussBonnetChern.RadialBoundaryCharts
import GaussBonnetChern.SphereFormIntegration
import GaussBonnetChern.SphereMeasureCoordinates

noncomputable section
open Set Metric Module
open scoped ContDiff Manifold
namespace GaussBonnetChern.RadialBoundaryCharts
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {d : ℕ} [Fact (Module.finrank ℝ E = d+1)]

def heightLinear (d : ℕ) : EuclideanSpace ℝ (Fin (d+1)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) ℝ).comp
    (heightFirstEquiv d).symm.toContinuousLinearMap

def sphereCoordinateLinear (d : ℕ) :
    EuclideanSpace ℝ (Fin (d+1)) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin d)) ℝ).comp
    (heightFirstEquiv d).symm.toContinuousLinearMap

@[simp] theorem heightLinear_apply (z : EuclideanSpace ℝ (Fin (d+1))) :
    heightLinear d z = z 0 := rfl

@[simp] theorem sphereCoordinateLinear_apply (z : EuclideanSpace ℝ (Fin (d+1))) (i : Fin d) :
    sphereCoordinateLinear d z i = z i.succ := rfl

def collarCoordinateMap (r : ℝ)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (z : EuclideanSpace ℝ (Fin (d+1))) : E :=
  (r + z 0) • (c.symm (sphereCoordinateLinear d z) : E)

def collarCoordinateDerivative (r : ℝ)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (z : EuclideanSpace ℝ (Fin (d+1))) : EuclideanSpace ℝ (Fin (d+1)) →L[ℝ] E :=
  (r + z 0) • (fderiv ℝ (fun y ↦ (c.symm y:E)) (sphereCoordinateLinear d z)).comp
    (sphereCoordinateLinear d) +
      (heightLinear d).smulRight (c.symm (sphereCoordinateLinear d z) : E)

theorem hasFDerivAt_collarCoordinateMap (r : ℝ)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0:E) 1))
    (z : EuclideanSpace ℝ (Fin (d+1))) (hz : sphereCoordinateLinear d z ∈ c.target) :
    HasFDerivAt (collarCoordinateMap r c) (collarCoordinateDerivative r c z) z := by
  have hψ : ContDiffAt ℝ ∞ (fun y ↦ (c.symm y:E)) (sphereCoordinateLinear d z) :=
    ((contMDiff_coe_sphere (n := d) (m := ∞) (c.symm (sphereCoordinateLinear d z))).comp _
      (contMDiffAt_symm_of_mem_maximalAtlas hc hz)).contDiffAt
  exact ((heightLinear d).hasFDerivAt.const_add r).smul
    ((hψ.differentiableAt (by simp)).hasFDerivAt.comp z (sphereCoordinateLinear d).hasFDerivAt)

theorem collarCoordinateDerivative_basis_zero (r : ℝ)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (z : EuclideanSpace ℝ (Fin (d+1))) :
    collarCoordinateDerivative r c z (EuclideanSpace.basisFun (Fin (d+1)) ℝ 0) =
      (c.symm (sphereCoordinateLinear d z) : E) := by
  have ht : sphereCoordinateLinear d (EuclideanSpace.basisFun (Fin (d+1)) ℝ 0) = 0 := by
    ext j
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have hh : heightLinear d (EuclideanSpace.basisFun (Fin (d+1)) ℝ 0) = 1 := by
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  change (r + z 0) •
    fderiv ℝ (fun y ↦ (c.symm y:E)) (sphereCoordinateLinear d z)
      (sphereCoordinateLinear d (EuclideanSpace.basisFun (Fin (d+1)) ℝ 0)) +
    heightLinear d (EuclideanSpace.basisFun (Fin (d+1)) ℝ 0) •
      (c.symm (sphereCoordinateLinear d z) : E) = _
  rw [ht, map_zero, smul_zero, zero_add, hh, one_smul]

theorem collarCoordinateDerivative_basis_succ (r : ℝ)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (z : EuclideanSpace ℝ (Fin (d+1))) (i : Fin d) :
    collarCoordinateDerivative r c z (EuclideanSpace.basisFun (Fin (d+1)) ℝ i.succ) =
      (r + z 0) • fderiv ℝ (fun y ↦ (c.symm y:E)) (sphereCoordinateLinear d z)
        (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  have ht : sphereCoordinateLinear d (EuclideanSpace.basisFun (Fin (d+1)) ℝ i.succ) =
      EuclideanSpace.basisFun (Fin d) ℝ i := by
    ext j
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have hh : heightLinear d (EuclideanSpace.basisFun (Fin (d+1)) ℝ i.succ) = 0 := by
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  change (r + z 0) •
    fderiv ℝ (fun y ↦ (c.symm y:E)) (sphereCoordinateLinear d z)
      (sphereCoordinateLinear d (EuclideanSpace.basisFun (Fin (d+1)) ℝ i.succ)) +
    heightLinear d (EuclideanSpace.basisFun (Fin (d+1)) ℝ i.succ) •
      (c.symm (sphereCoordinateLinear d z) : E) = _
  rw [ht, hh, zero_smul, add_zero]

section EuclideanDeterminant
variable (r : ℝ)
variable (c : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
    (EuclideanSpace ℝ (Fin d)))
variable (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞
  (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1))
variable (z : EuclideanSpace ℝ (Fin (d+1))) (hz : sphereCoordinateLinear d z ∈ c.target)

local instance euclideanDimensionFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d+1))) = d+1) := ⟨finrank_euclideanSpace_fin⟩

include hc hz

theorem det_collarCoordinateDerivative :
    (collarCoordinateDerivative r c z).det = (r + z 0)^d *
      sphereChartDensity (EuclideanSpace.basisFun (Fin (d+1)) ℝ) c (sphereCoordinateLinear d z) := by
  let b := EuclideanSpace.basisFun (Fin (d+1)) ℝ
  have hdet : (collarCoordinateDerivative r c z).det = b.toBasis.det
      (fun i ↦ collarCoordinateDerivative r c z (b i)) := by
    have hbself : b.toBasis.det (fun i ↦ b i) = 1 := by
      simpa only [OrthonormalBasis.coe_toBasis] using b.toBasis.det_self
    have h := (b.toBasis.det_comp (collarCoordinateDerivative r c z).toLinearMap b.toBasis).symm
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_coe,
      OrthonormalBasis.coe_toBasis, Function.comp_def] at h
    rw [hbself, mul_one] at h
    exact h
  rw [hdet]
  have hb : (fun i ↦ collarCoordinateDerivative r c z (b i)) =
      Fin.cons (c.symm (sphereCoordinateLinear d z) : EuclideanSpace ℝ (Fin (d+1)))
        (fun i ↦ (r+z 0) • fderiv ℝ (fun y ↦ (c.symm y : EuclideanSpace ℝ (Fin (d+1))))
          (sphereCoordinateLinear d z) (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact collarCoordinateDerivative_basis_zero r c z
    · exact collarCoordinateDerivative_basis_succ r c z j
  rw [hb, SphereMeasureCoordinates.determinant_cons_smul]
  congr 1
  exact (sphereChartDensity_eq_det b c hc (sphereCoordinateLinear d z) hz).symm

theorem det_collarCoordinateDerivative_pos
    (hrz : 0 < r+z 0)
    (hp : 0 < sphereChartDensity (EuclideanSpace.basisFun (Fin (d+1)) ℝ)
      c (sphereCoordinateLinear d z)) :
    0 < (collarCoordinateDerivative r c z).det := by
  rw [det_collarCoordinateDerivative r c hc z hz]
  exact mul_pos (pow_pos hrz _) hp

end EuclideanDeterminant
end GaussBonnetChern.RadialBoundaryCharts
