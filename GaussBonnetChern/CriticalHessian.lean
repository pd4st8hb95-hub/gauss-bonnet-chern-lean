import GaussBonnetChern.MorseHessian

/-! # The Hessian at a critical point

Metric compatibility identifies the covariant Hessian with the derivative of
the actual scalar differential along a smooth field. The connection correction
vanishes at a critical point, which is the key coordinate-invariance identity.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff Topology

namespace GaussBonnetChern

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

theorem hessian_eq_directionalDerivative {f : M → ℝ} {p : M}
    {Y : (y : M) → TangentSpace (model n) y}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f p)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) p)
    (u : TangentSpace (model n) p) :
    hessian n M f p u (Y p) =
      mvfderiv (model n) (fun y ↦ mvfderiv (model n) f y (Y y)) p u -
        mvfderiv (model n) f p (connection n M Y p u) := by
  let : IsContMDiffRiemannianBundle (model n) 1 (Model n)
      (TangentSpace (model n) : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have h := (connection_isMetricCompatible n M).mvfderiv_inner_eq
    (extend (Model n) (x := p) u)
    ((contMDiffAt_gradient n M hf).mdifferentiableAt (by simp))
    (hY.mdifferentiableAt (by simp))
  simp only [inner_gradient, extend_apply_self] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

theorem hessian_eq_directionalDerivative_of_critical {f : M → ℝ} {p : M}
    {Y : (y : M) → TangentSpace (model n) y}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f p)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) p)
    (hcritical : mvfderiv (model n) f p = 0) (u : TangentSpace (model n) p) :
    hessian n M f p u (Y p) =
      mvfderiv (model n) (fun y ↦ mvfderiv (model n) f y (Y y)) p u := by
  rw [hessian_eq_directionalDerivative n M hf hY, hcritical]
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem hessian_pullback_at_critical
    {f : M → ℝ} {g : E → M} {s : Set E} {y : E}
    (hs : IsOpen s) (hy : y ∈ s)
    (hg : ContMDiffOn 𝓘(ℝ, E) (model n) ∞ g s)
    (hgi : ∀ z ∈ s, (mfderiv 𝓘(ℝ, E) (model n) g z).IsInvertible)
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f (g y))
    (hcritical : mvfderiv (model n) f (g y) = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) y u v =
      hessian n M f (g y) (mfderiv 𝓘(ℝ, E) (model n) g y u)
        (mfderiv 𝓘(ℝ, E) (model n) g y v) := by
  let V := extend (Model n) (x := g y) (mfderiv 𝓘(ℝ, E) (model n) g y v)
  let Z := VectorField.mpullback 𝓘(ℝ, E) (model n) g V
  have hV : ContMDiffAt (model n) (model n).tangent ∞ (T% V) (g y) := contMDiffAt_extend ..
  have hgy := hg.contMDiffAt (hs.mem_nhds hy)
  have hZ := hV.mpullback_vectorField_preimage hgy (hgi y hy) (by simp)
  have hZd : DifferentiableAt ℝ Z y :=
    (contMDiffAt_vectorSpace_iff_contDiffAt.mp hZ).differentiableAt (by simp)
  have hZy : Z y = v := by
    change (mfderiv 𝓘(ℝ, E) (model n) g y).inverse (V (g y)) = v
    simp only [V, extend_apply_self]
    exact (hgi y hy).inverse_apply_self v
  have hF : ContDiffAt ℝ ∞ (f ∘ g) y := (hf.comp y hgy).contDiffAt
  have hDF := (hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hscalar := contMDiffAt_directionalDerivative n M hf hV
  have heq : (fun z ↦ fderiv ℝ (f ∘ g) z (Z z)) =ᶠ[𝓝 y]
      (fun z ↦ mvfderiv (model n) f (g z) (V (g z))) := by
    have hf1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
      (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
    filter_upwards [hs.mem_nhds hy, hgy.continuousAt.tendsto.eventually hf1] with z hz hfz
    have hgz := hg.contMDiffAt (hs.mem_nhds hz)
    have hc := mvfderiv_comp_apply z (hfz.mdifferentiableAt (by simp))
      (hgz.mdifferentiableAt (by simp)) (Z z)
    rw [mvfderiv_eq_fderiv] at hc
    exact hc.trans (congrArg (mvfderiv (model n) f (g z)) ((hgi z hz).self_apply_inverse _))
  have hzero : fderiv ℝ (f ∘ g) y = 0 := by
    have hc := mvfderiv_comp y (hf.mdifferentiableAt (by simp)) (hgy.mdifferentiableAt (by simp))
    rw [mvfderiv_eq_fderiv, hcritical] at hc
    simpa using! hc
  have hd := fderiv_clm_apply hDF hZd
  have hdeq := heq.fderiv_eq (𝕜 := ℝ)
  have hc := mvfderiv_comp_apply y (hscalar.mdifferentiableAt (by simp))
    (hgy.mdifferentiableAt (by simp)) u
  rw [mvfderiv_eq_fderiv] at hc
  have hH := hessian_eq_directionalDerivative_of_critical n M hf hV hcritical
    (mfderiv 𝓘(ℝ, E) (model n) g y u)
  simp only [V, extend_apply_self] at hH
  rw [← hH] at hc
  have hc' : fderiv ℝ (fun z ↦ mvfderiv (model n) f (g z) (V (g z))) y u =
      hessian n M f (g y) (mfderiv 𝓘(ℝ, E) (model n) g y u)
        (mfderiv 𝓘(ℝ, E) (model n) g y v) := by
    simpa only [Function.comp_def] using! hc
  rw [← hdeq, hd, hzero, hZy] at hc'
  simpa using hc'

theorem connection_gradient_injective_of_coordinate_hessian
    {f : M → ℝ} {g : E → M} {s : Set E} {y : E}
    (hs : IsOpen s) (hy : y ∈ s)
    (hg : ContMDiffOn 𝓘(ℝ, E) (model n) ∞ g s)
    (hgi : ∀ z ∈ s, (mfderiv 𝓘(ℝ, E) (model n) g z).IsInvertible)
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f (g y))
    (hcritical : mvfderiv (model n) f (g y) = 0)
    (hH : Function.Injective (fderiv ℝ (fderiv ℝ (f ∘ g)) y)) :
    Function.Injective (connection n M (gradient n M f) (g y)) := by
  intro u v huv
  obtain ⟨a, ha⟩ : ∃ a : E, mfderiv 𝓘(ℝ, E) (model n) g y a = u := (hgi y hy).surjective u
  obtain ⟨b, hb⟩ : ∃ b : E, mfderiv 𝓘(ℝ, E) (model n) g y b = v := (hgi y hy).surjective v
  have hab : a = b := by
    apply hH
    ext w
    rw [hessian_pullback_at_critical n M hs hy hg hgi hf hcritical,
      hessian_pullback_at_critical n M hs hy hg hgi hf hcritical, ha, hb]
    simp only [hessian, huv]
  exact ha.symm.trans ((congrArg (mfderiv 𝓘(ℝ, E) (model n) g y) hab).trans hb)
end GaussBonnetChern

