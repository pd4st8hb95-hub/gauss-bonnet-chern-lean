import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-! # Uniform first-order blow-up of a differentiable zero

All derivatives below are actual Fréchet derivatives. The estimates are uniform
on the unit sphere and are derived from differentiability and continuity of the
derivative at zero; no uniform remainder estimate is an additional premise.
-/

noncomputable section
open Filter Set Metric Asymptotics
open scoped Topology ContDiff

namespace GaussBonnetChern.LocalIndex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def rescale (f : E → F) (r : ℝ) (u : E) : F := r⁻¹ • f (r • u)

theorem norm_rescale_sub {f : E → F} (L : E →L[ℝ] F) {r : ℝ} (hr : 0 < r) (u : E) :
    ‖rescale f r u - L u‖ = r⁻¹ * ‖f (r • u) - L (r • u)‖ := by
  have h : rescale f r u - L u = r⁻¹ • (f (r • u) - L (r • u)) := by
    simp [rescale, smul_sub, map_smul, smul_smul, hr.ne']
  rw [h, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]

theorem uniform_rescale_estimate {f : E → F} {L : E →L[ℝ] F}
    (hf : HasFDerivAt f L 0) (hzero : f 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → ∀ u : E, ‖u‖ = 1 →
      ‖rescale f r u - L u‖ < ε := by
  have hrem := (isLittleO_iff.mp (hasFDerivAt_iff_isLittleO_nhds_zero.mp hf)) (half_pos hε)
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hrem
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ u hu
  have hru : ‖r • u‖ = r := by simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu]
  have hb := hbound (show dist (r • u) (0 : E) < δ by simpa [dist_zero_right, hru] using hrδ)
  simp only [zero_add, hzero, sub_zero, hru] at hb
  rw [norm_rescale_sub L hr]
  calc
    r⁻¹ * ‖f (r • u) - L (r • u)‖ ≤ r⁻¹ * (ε / 2 * r) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hr.le)
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

theorem tendstoUniformlyOn_rescale {f : E → F} {L : E →L[ℝ] F}
    (hf : HasFDerivAt f L 0) (hzero : f 0 = 0) :
    TendstoUniformlyOn (rescale f) L (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := uniform_rescale_estimate hf hzero hε
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  intro u hu
  rw [dist_eq_norm, norm_sub_rev]
  exact hb r hr.1 hr.2 u (by simpa [mem_sphere, dist_zero_right] using hu)

theorem tendstoUniformlyOn_smul_of_continuousAt {G : Type*} [PseudoMetricSpace G]
    {g : E → G} (hg : ContinuousAt g 0) :
    TendstoUniformlyOn (fun r : ℝ => fun u : E => g (r • u)) (fun _ => g 0)
      (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp hg ε hε
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  intro u hu
  rw [dist_comm]
  apply hb
  simpa [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1,
    (show ‖u‖ = 1 by simpa [mem_sphere, dist_zero_right] using hu)] using hr.2

theorem hasFDerivAt_rescale {f : E → F} {r : ℝ} (hr : r ≠ 0) {u : E}
    (hf : DifferentiableAt ℝ f (r • u)) :
    HasFDerivAt (rescale f r) (fderiv ℝ f (r • u)) u := by
  have h := (hf.hasFDerivAt.comp u ((hasFDerivAt_id u).const_smul r)).const_smul r⁻¹
  convert h using 1
  · rfl
  · ext v
    simp [ContinuousLinearMap.comp_apply, smul_smul, hr]

theorem fderiv_rescale {f : E → F} {r : ℝ} (hr : r ≠ 0) {u : E}
    (hf : DifferentiableAt ℝ f (r • u)) :
    fderiv ℝ (rescale f r) u = fderiv ℝ f (r • u) :=
  (hasFDerivAt_rescale hr hf).fderiv

theorem uniform_fderiv_rescale_estimate {f : E → F}
    (hf : ContDiffAt ℝ 1 f 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → ∀ u : E, ‖u‖ = 1 →
      ‖fderiv ℝ (rescale f r) u - fderiv ℝ f 0‖ < ε := by
  have hd : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℝ f x :=
    (hf.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num)
  have hc := (hf.continuousAt_fderiv (by norm_num)).eventually (ball_mem_nhds _ hε)
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp (hd.and hc)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ u hu
  have hru : dist (r • u) (0 : E) < δ := by
    simpa [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu] using hrδ
  have hh := hb hru
  rw [fderiv_rescale hr.ne' hh.1]
  simpa only [mem_ball, dist_eq_norm] using hh.2

theorem tendstoUniformlyOn_fderiv_rescale {f : E → F} (hf : ContDiffAt ℝ 1 f 0) :
    TendstoUniformlyOn (fun r : ℝ => fderiv ℝ (rescale f r)) (fun _ => fderiv ℝ f 0)
      (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := uniform_fderiv_rescale_estimate hf hε
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  intro u hu
  rw [dist_eq_norm, norm_sub_rev]
  exact hb r hr.1 hr.2 u (by simpa [mem_sphere, dist_zero_right] using hu)

/-- A positive lower bound that is also meaningful when the unit sphere is
empty. No positive-dimensional hypothesis is needed. -/
def inverseBound (L : E ≃L[ℝ] F) : ℝ := (‖(L.symm : F →L[ℝ] E)‖ + 1)⁻¹

theorem inverseBound_pos (L : E ≃L[ℝ] F) : 0 < inverseBound L := by
  unfold inverseBound
  positivity

theorem inverseBound_le_norm (L : E ≃L[ℝ] F) {u : E} (hu : ‖u‖ = 1) :
    inverseBound L ≤ ‖L u‖ := by
  have h := (L.symm : F →L[ℝ] E).le_opNorm (L u)
  change ‖L.symm (L u)‖ ≤ ‖(L.symm : F →L[ℝ] E)‖ * ‖L u‖ at h
  rw [L.symm_apply_apply, hu] at h
  unfold inverseBound
  apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < ‖(L.symm : F →L[ℝ] E)‖ + 1)).mpr
  nlinarith [norm_nonneg (L u)]

/-- All sufficiently small positive rescalings stay uniformly separated from
zero and in a fixed bounded ball. -/
theorem rescale_uniform_bounds {f : E → F} (L : E ≃L[ℝ] F)
    (hf : HasFDerivAt f (L : E →L[ℝ] F) 0) (hzero : f 0 = 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u ∈ sphere (0 : E) 1,
      inverseBound L / 2 ≤ ‖rescale f r u‖ ∧
        ‖rescale f r u‖ ≤ ‖(L : E →L[ℝ] F)‖ + 1 := by
  have hc : 0 < min (inverseBound L / 2) 1 := lt_min (half_pos (inverseBound_pos L)) zero_lt_one
  obtain ⟨δ, hδ, hb⟩ := uniform_rescale_estimate hf hzero hc
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  intro u hu
  have hnorm : ‖u‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hu
  have herror := hb r hr.1 hr.2 u hnorm
  change ‖rescale f r u - L u‖ < min (inverseBound L / 2) 1 at herror
  have hlo := inverseBound_le_norm L hnorm
  have hup := (L : E →L[ℝ] F).le_opNorm u
  rw [hnorm, mul_one] at hup
  change ‖L u‖ ≤ ‖(L : E →L[ℝ] F)‖ at hup
  have ha := norm_sub_norm_le (L u) (rescale f r u)
  rw [norm_sub_rev] at ha
  have hb' := norm_sub_norm_le (rescale f r u) (L u)
  constructor <;> have hm := min_le_left (inverseBound L / 2) (1 : ℝ)
  · linarith
  · have hm' := min_le_right (inverseBound L / 2) (1 : ℝ)
    linarith

theorem eventually_rescale_ne_zero {f : E → F} (L : E ≃L[ℝ] F)
    (hf : HasFDerivAt f (L : E →L[ℝ] F) 0) (hzero : f 0 = 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u ∈ sphere (0 : E) 1, f (r • u) ≠ 0 := by
  filter_upwards [rescale_uniform_bounds L hf hzero] with r hr
  intro u hu hzero'
  have h := (hr u hu).1
  have hp := inverseBound_pos L
  simp only [rescale, hzero', smul_zero, norm_zero] at h
  linarith

end GaussBonnetChern.LocalIndex
