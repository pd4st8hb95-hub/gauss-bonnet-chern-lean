import GaussBonnetChern.NondegenerateScaling
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform convergence of normalized small spheres

The normalization and its derivatives are actual maps and Fréchet derivatives.
Compact annuli supply uniform continuity; their inner radius comes from the
proved inverse bound and Taylor estimate.
-/

noncomputable section
open Filter Set Metric
open scoped Topology ContDiff

namespace GaussBonnetChern.LocalIndex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalize (x : E) : E := ‖x‖⁻¹ • x

theorem normalize_pos_smul (x : E) {r : ℝ} (hr : 0 < r) :
    normalize (r • x) = normalize x := by
  simp [normalize, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv, smul_smul,
    mul_assoc, mul_comm, mul_left_comm, hr.ne']

theorem normalize_rescale (f : E → E) {r : ℝ} (hr : 0 < r) :
    (normalize ∘ rescale f r) = (fun u => normalize (f (r • u))) := by
  funext u
  exact normalize_pos_smul _ (inv_pos.mpr hr)

theorem norm_normalize {x : E} (hx : x ≠ 0) : ‖normalize x‖ = 1 := by
  simp [normalize, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x),
    norm_ne_zero_iff.mpr hx]

theorem eventually_normalized_sphere_mapsTo {f : E → E} (L : E ≃L[ℝ] E)
    (hf : HasFDerivAt f (L : E →L[ℝ] E) 0) (hzero : f 0 = 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), MapsTo (fun u => normalize (f (r • u)))
      (sphere (0 : E) 1) (sphere (0 : E) 1) := by
  filter_upwards [eventually_rescale_ne_zero L hf hzero] with r hr
  intro u hu
  simpa [mem_sphere, dist_zero_right] using norm_normalize (hr u hu)

theorem contDiffAt_normalize {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ normalize x := by
  exact ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

theorem compact_annulus [FiniteDimensional ℝ E] (c B : ℝ) :
    IsCompact {x : E | c ≤ ‖x‖ ∧ ‖x‖ ≤ B} := by
  have heq : {x : E | c ≤ ‖x‖ ∧ ‖x‖ ≤ B} = closedBall (0 : E) B ∩ {x | c ≤ ‖x‖} := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, mem_closedBall, dist_zero_right]
    tauto
  rw [heq]
  exact (isCompact_closedBall 0 B).inter_right (isClosed_le continuous_const continuous_norm)

theorem tendstoUniformlyOn_normalize_rescale [FiniteDimensional ℝ E]
    {f : E → E} (L : E ≃L[ℝ] E) (hf : HasFDerivAt f (L : E →L[ℝ] E) 0)
    (hzero : f 0 = 0) :
    TendstoUniformlyOn (fun r : ℝ => fun u => normalize (f (r • u)))
      (fun u => normalize (L u)) (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
  let K : Set E := {x | inverseBound L / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ ‖(L : E →L[ℝ] E)‖ + 1}
  have hc : IsCompact K := compact_annulus _ _
  have hn : ContinuousOn normalize K := by
    intro x hx
    apply (contDiffAt_normalize (show x ≠ 0 from ?_)).continuousAt.continuousWithinAt
    have hp := inverseBound_pos L
    intro h
    simp only [K, mem_setOf_eq, h, norm_zero] at hx
    linarith [hx.1]
  have hL : ∀ u ∈ sphere (0 : E) 1, L u ∈ K := by
    intro u hu
    have hn : ‖u‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hu
    have lo := inverseBound_le_norm L hn
    have up := (L : E →L[ℝ] E).le_opNorm u
    rw [hn, mul_one] at up
    change ‖L u‖ ≤ ‖(L : E →L[ℝ] E)‖ at up
    exact ⟨by linarith [inverseBound_pos L], by linarith⟩
  have ht := (hc.uniformContinuousOn_of_continuous hn).comp_tendstoUniformlyOn_eventually
    (rescale_uniform_bounds L hf hzero) hL (tendstoUniformlyOn_rescale hf hzero)
  apply ht.congr
  filter_upwards [self_mem_nhdsWithin] with r hr
  intro u _
  exact congrFun (normalize_rescale f hr) u

theorem eventually_sphere_smul {p : E → Prop} (hp : ∀ᶠ x in 𝓝 (0 : E), p x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u ∈ sphere (0 : E) 1, p (r • u) := by
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hp
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  intro u hu
  apply hb
  simpa [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1,
    (show ‖u‖ = 1 by simpa [mem_sphere, dist_zero_right] using hu)] using hr.2

theorem uniform_product_same_parameter {X Y Z T : Type*} [PseudoMetricSpace Y]
    [PseudoMetricSpace Z] {l : Filter T} {s : Set X}
    {f : T → X → Y} {g : T → X → Z} {f₀ : X → Y} {g₀ : X → Z}
    (hf : TendstoUniformlyOn f f₀ l s) (hg : TendstoUniformlyOn g g₀ l s) :
    TendstoUniformlyOn (fun t x => (f t x, g t x)) (fun x => (f₀ x, g₀ x)) l s := by
  rw [Metric.tendstoUniformlyOn_iff] at hf hg ⊢
  intro ε hε
  filter_upwards [hf ε hε, hg ε hε] with t ht ht'
  intro x hx
  exact max_lt (ht x hx) (ht' x hx)

theorem eventually_contDiffAt_normalized_sphere {f : E → E} (L : E ≃L[ℝ] E)
    (hf : ContDiffAt ℝ 1 f 0) (hL : fderiv ℝ f 0 = (L : E →L[ℝ] E))
    (hzero : f 0 = 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u ∈ sphere (0 : E) 1,
      ContDiffAt ℝ 1 (fun v => normalize (f (r • v))) u := by
  have hd : HasFDerivAt f (L : E →L[ℝ] E) 0 := hL ▸ (hf.differentiableAt (by norm_num)).hasFDerivAt
  filter_upwards [eventually_sphere_smul (hf.eventually (by norm_num)),
    eventually_rescale_ne_zero L hd hzero] with r hr hne
  intro u hu
  exact ((contDiffAt_normalize (hne u hu)).of_le (by simp)).comp u
    ((hr u hu).comp u (contDiffAt_id.const_smul r))

theorem tendstoUniformlyOn_fderiv_normalized_rescale [FiniteDimensional ℝ E]
    {f : E → E} (L : E ≃L[ℝ] E) (hf : ContDiffAt ℝ 1 f 0)
    (hL : fderiv ℝ f 0 = (L : E →L[ℝ] E)) (hzero : f 0 = 0) :
    TendstoUniformlyOn (fun r : ℝ => fderiv ℝ (fun u => normalize (f (r • u))))
      (fun u => (fderiv ℝ normalize (L u)).comp (L : E →L[ℝ] E))
      (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
  have hd : HasFDerivAt f (L : E →L[ℝ] E) 0 := hL ▸ (hf.differentiableAt (by norm_num)).hasFDerivAt
  let K : Set E := {x | inverseBound L / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ ‖(L : E →L[ℝ] E)‖ + 1}
  let C : Set (E →L[ℝ] E) := closedBall 0 (‖(L : E →L[ℝ] E)‖ + 1)
  have hK : IsCompact K := compact_annulus _ _
  have hC : IsCompact C := isCompact_closedBall _ _
  have hnorm : ∀ x ∈ K, x ≠ 0 := by
    intro x hx hzero'
    have hp := inverseBound_pos L
    simp only [K, mem_setOf_eq, hzero', norm_zero] at hx
    linarith [hx.1]
  let G : E × (E →L[ℝ] E) → (E →L[ℝ] E) :=
    fun z => (fderiv ℝ normalize z.1).comp z.2
  have hG : ContinuousOn G (K ×ˢ C) := by
    intro z hz
    have hc := (contDiffAt_normalize (hnorm z.1 hz.1)).continuousAt_fderiv (by simp)
    exact ((hc.comp continuousAt_fst).clm_comp continuousAt_snd).continuousWithinAt
  have hDv : TendstoUniformlyOn (fun r : ℝ => fderiv ℝ (rescale f r))
      (fun _ => (L : E →L[ℝ] E)) (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
    simpa only [hL] using tendstoUniformlyOn_fderiv_rescale hf
  have hDb : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u ∈ sphere (0 : E) 1,
      fderiv ℝ (rescale f r) u ∈ C := by
    have he := (Metric.tendstoUniformlyOn_iff.mp hDv) 1 zero_lt_one
    filter_upwards [he] with r hr
    intro u hu
    have hx := hr u hu
    have hn := norm_sub_norm_le (fderiv ℝ (rescale f r) u) (L : E →L[ℝ] E)
    rw [dist_eq_norm, norm_sub_rev] at hx
    simp only [C, mem_closedBall, dist_zero_right]
    linarith
  have hFb : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u ∈ sphere (0 : E) 1,
      (rescale f r u, fderiv ℝ (rescale f r) u) ∈ K ×ˢ C := by
    filter_upwards [rescale_uniform_bounds L hd hzero, hDb] with r hr hd'
    intro u hu
    exact ⟨hr u hu, hd' u hu⟩
  have hlim : ∀ u ∈ sphere (0 : E) 1, (L u, (L : E →L[ℝ] E)) ∈ K ×ˢ C := by
    intro u hu
    have hn : ‖u‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hu
    have lo := inverseBound_le_norm L hn
    have up := (L : E →L[ℝ] E).le_opNorm u
    rw [hn, mul_one] at up
    change ‖L u‖ ≤ ‖(L : E →L[ℝ] E)‖ at up
    refine ⟨⟨by linarith [inverseBound_pos L], by linarith⟩, ?_⟩
    simp only [C, mem_closedBall, dist_zero_right]
    linarith
  have hpair := uniform_product_same_parameter (tendstoUniformlyOn_rescale hd hzero) hDv
  have hconv := ((hK.prod hC).uniformContinuousOn_of_continuous hG).comp_tendstoUniformlyOn_eventually
    hFb hlim hpair
  apply hconv.congr
  have hdnear : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℝ f x :=
    (hf.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num)
  filter_upwards [eventually_sphere_smul hdnear, rescale_uniform_bounds L hd hzero,
    self_mem_nhdsWithin] with r hdr hbr hr
  intro u hu
  have hne : rescale f r u ≠ 0 := hnorm _ (hbr u hu)
  have hcomp := fderiv_comp u ((contDiffAt_normalize hne).differentiableAt (by simp))
    (hasFDerivAt_rescale (ne_of_gt hr) (hdr u hu)).differentiableAt
  change (fderiv ℝ normalize (rescale f r u)).comp (fderiv ℝ (rescale f r) u) = _
  rw [← hcomp, normalize_rescale f hr]

/-- The limit is the actual derivative of the normalized linear map, on the
unit sphere. The zero-dimensional case is included via its empty sphere. -/
theorem tendstoUniformlyOn_fderiv_normalized_linear [FiniteDimensional ℝ E]
    {f : E → E} (L : E ≃L[ℝ] E) (hf : ContDiffAt ℝ 1 f 0)
    (hL : fderiv ℝ f 0 = (L : E →L[ℝ] E)) (hzero : f 0 = 0) :
    TendstoUniformlyOn (fun r : ℝ => fderiv ℝ (fun u => normalize (f (r • u))))
      (fderiv ℝ (fun u => normalize (L u)))
      (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
  apply (tendstoUniformlyOn_fderiv_normalized_rescale L hf hL hzero).congr_right
  intro u hu
  have hn : ‖u‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hu
  have hne : L u ≠ 0 := by
    intro h
    have h' : u = 0 := L.injective (by simpa using h)
    simp [h'] at hn
  simpa only [ContinuousLinearEquiv.fderiv, Function.comp_def] using!
    (fderiv_comp u ((contDiffAt_normalize hne).differentiableAt (by simp)) L.differentiableAt).symm

/-- Uniform directional-derivative convergence includes, in particular, all
unit tangent directions to the sphere (`inner u v = 0`). -/
theorem tendstoUniformlyOn_normalized_directional [FiniteDimensional ℝ E]
    {f : E → E} (L : E ≃L[ℝ] E) (hf : ContDiffAt ℝ 1 f 0)
    (hL : fderiv ℝ f 0 = (L : E →L[ℝ] E)) (hzero : f 0 = 0) :
    TendstoUniformlyOn
      (fun r : ℝ => fun z : E × E => (fderiv ℝ (fun u => normalize (f (r • u))) z.1) z.2)
      (fun z : E × E => (fderiv ℝ (fun u => normalize (L u)) z.1) z.2)
      (𝓝[>] (0 : ℝ)) {z : E × E | ‖z.1‖ = 1 ∧ ‖z.2‖ ≤ 1} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht := (Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_fderiv_normalized_linear L hf hL hzero)) ε hε
  filter_upwards [ht] with r hr
  intro z hz
  have hu : z.1 ∈ sphere (0 : E) 1 := by simpa [mem_sphere, dist_zero_right] using hz.1
  have hh := hr z.1 hu
  rw [dist_eq_norm] at hh ⊢
  change ‖((fderiv ℝ (fun u => normalize (L u)) z.1) -
    fderiv ℝ (fun u => normalize (f (r • u))) z.1) z.2‖ < ε
  refine lt_of_le_of_lt (le_trans (ContinuousLinearMap.le_opNorm _ _) ?_) hh
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2
    (norm_nonneg ((fderiv ℝ (fun u => normalize (L u)) z.1) -
      fderiv ℝ (fun u => normalize (f (r • u))) z.1))

end GaussBonnetChern.LocalIndex
