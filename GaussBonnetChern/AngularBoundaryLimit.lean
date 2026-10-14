import GaussBonnetChern.SphereFormIntegration
import GaussBonnetChern.NormalizedSphereLimit

/-! # Operator-norm control of actual sphere-form coefficients

The norm below is on ambient alternating forms. It does not use the chart
norm of a sphere tangent space. A pointwise orthonormal tangent tuple is
lifted through the genuine differential of the sphere inclusion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module Filter Set Metric MeasureTheory
open scoped Topology Manifold BigOperators RealInnerProductSpace

namespace GaussBonnetChern.AngularBoundary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (finrank ℝ E = d + 1)]

def ambientSphereRestriction
    (β : sphere (0 : E) 1 → E [⋀^Fin d]→L[ℝ] ℝ) :
    DifferentialForm.Form (𝓡 d) (sphere (0 : E) 1) d :=
  fun u => (β u).compContinuousLinearMap
    (mvfderiv (𝓡 d) ((↑) : sphere (0 : E) 1 → E) u)

theorem abs_sphereFormCoefficient_ambient_le
    (b : OrthonormalBasis (Fin (d + 1)) ℝ E)
    (β : sphere (0 : E) 1 → E [⋀^Fin d]→L[ℝ] ℝ) (u : sphere (0 : E) 1) :
    |sphereFormCoefficient b (ambientSphereRestriction β) u| ≤ ‖β u‖ := by
  let e := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) d
    (ne_zero_of_mem_unit_sphere u)
  let D := mvfderiv (𝓡 d) ((↑) : sphere (0 : E) 1 → E) u
  have heRange (i : Fin d) : (e i : E) ∈ D.range := by
    rw [range_mvfderiv_subtypeVal (n := d) u]
    exact (e i).property
  choose w hw using heRange
  have hlift : (fun i => D (w i)) = (fun i => (e i : E)) := by
    funext i
    exact hw i
  have hnorm (i : Fin d) : ‖(e i : E)‖ = 1 := e.orthonormal.1 i
  have heON : Orthonormal ℝ (fun i => (e i : E)) :=
    e.orthonormal.comp_linearIsometry (ℝ ∙ (u : E))ᗮ.subtypeₗᵢ
  have hON : Orthonormal ℝ (Fin.cons (u : E) (fun i => (e i : E))) := by
    apply orthonormal_vecCons_iff.mpr
    exact ⟨norm_eq_of_mem_sphere u,
      fun i => Submodule.mem_orthogonal_singleton_iff_inner_right.mp (e i).property, heON⟩
  have hdet : |b.toBasis.det (Fin.cons (u : E) (fun i => (e i : E)))| = 1 := by
    have h := b.toBasis.orientation.abs_volumeForm_apply_of_pairwise_orthogonal hON.2
    rw [b.toBasis.orientation.volumeForm_robust b rfl] at h
    simpa only [hON.1, Finset.prod_const_one] using h
  have hvol : |sphereVolumeForm b u w| = 1 := by
    calc
      |sphereVolumeForm b u w| =
          |b.toBasis.det (Fin.cons (u : E) (fun i => (e i : E)))| := by
        change |b.toBasis.det (Fin.cons (u : E) (fun i => D (w i)))| = _
        exact congrArg (fun v => |b.toBasis.det (Fin.cons (u : E) v)|) hlift
      _ = 1 := hdet
  have hv : sphereVolumeForm b u w ≠ 0 := by intro hz; simpa [hz] using hvol
  rw [sphereFormCoefficient_eq_ratio b (ambientSphereRestriction β) u w hv, abs_div, hvol, div_one]
  change |β u (fun i => D (w i))| ≤ ‖β u‖
  have hh := (β u).le_opNorm (fun i => (e i : E))
  have hb : |β u (fun i => (e i : E))| ≤ ‖β u‖ := by
    simpa only [Real.norm_eq_abs, hnorm, Finset.prod_const_one, mul_one] using hh
  exact (congrArg (fun v => |β u v|) hlift).trans_le hb

theorem sphereFormCoefficient_ambient_sub
    (b : OrthonormalBasis (Fin (d + 1)) ℝ E)
    (β γ : sphere (0 : E) 1 → E [⋀^Fin d]→L[ℝ] ℝ) (u : sphere (0 : E) 1) :
    sphereFormCoefficient b (ambientSphereRestriction (fun x => β x - γ x)) u =
      sphereFormCoefficient b (ambientSphereRestriction β) u -
        sphereFormCoefficient b (ambientSphereRestriction γ) u := by
  simp [sphereFormCoefficient, ambientSphereRestriction, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.sub_apply, sub_div]

/-- Uniform ambient operator-norm convergence controls the actual unique
coefficient of the sphere top form, with constant one. -/
theorem uniform_sphereFormCoefficient_of_ambient {T : Type*} {l : Filter T}
    (b : OrthonormalBasis (Fin (d + 1)) ℝ E)
    {β : T → sphere (0 : E) 1 → E [⋀^Fin d]→L[ℝ] ℝ}
    {γ : sphere (0 : E) 1 → E [⋀^Fin d]→L[ℝ] ℝ}
    (h : TendstoUniformlyOn β γ l univ) :
    TendstoUniformlyOn (fun t => sphereFormCoefficient b (ambientSphereRestriction (β t)))
      (sphereFormCoefficient b (ambientSphereRestriction γ)) l univ := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with t ht
  intro u hu
  have hb := abs_sphereFormCoefficient_ambient_le b (fun x => γ x - β t x) u
  rw [sphereFormCoefficient_ambient_sub] at hb
  rw [dist_eq_norm, Real.norm_eq_abs]
  apply lt_of_le_of_lt hb
  simpa only [dist_eq_norm] using ht u hu

section Integrals

/-- Uniform convergence on a finite measure space passes through actual
Bochner integrals once integrability is established. -/
theorem tendsto_integral_of_uniform {X T : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {l : Filter T} {f : T → X → ℝ} {g : X → ℝ}
    (hf : ∀ᶠ t in l, Integrable (f t) μ) (hg : Integrable g μ)
    (hconv : TendstoUniformlyOn f g l univ) :
    Tendsto (fun t => ∫ x, f t x ∂μ) l (𝓝 (∫ x, g x ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hm : 0 ≤ μ.real univ := measureReal_nonneg
  have hden : 0 < μ.real univ + 1 := by positivity
  have hδ : 0 < ε / (μ.real univ + 1) := div_pos hε hden
  filter_upwards [hf, (Metric.tendstoUniformlyOn_iff.mp hconv) _ hδ] with t ht hc
  rw [dist_eq_norm, ← integral_sub ht hg]
  have hbound : ∀ᵐ x ∂μ, ‖f t x - g x‖ ≤ ε / (μ.real univ + 1) := by
    filter_upwards with x
    have h := hc x (mem_univ x)
    rw [dist_eq_norm, norm_sub_rev] at h
    exact h.le
  apply lt_of_le_of_lt (norm_integral_le_of_norm_le_const hbound)
  have hfrac : μ.real univ / (μ.real univ + 1) < 1 := by
    rw [div_lt_one hden]
    linarith
  calc
    ε / (μ.real univ + 1) * μ.real univ = ε * (μ.real univ / (μ.real univ + 1)) := by ring
    _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
    _ = ε := mul_one _

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem sphereFormIntegral_smul (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (c : ℝ) (α : DifferentialForm.Form (𝓡 d) (sphere (0:E) 1) d) :
    sphereFormIntegral b (c • α) = c * sphereFormIntegral b α := by
  unfold sphereFormIntegral
  have hc (u : sphere (0:E) 1) : sphereFormCoefficient b (c • α) u =
      c * sphereFormCoefficient b α u :=
    sphereFormCoefficient_fsmul b (fun _ => c) α u
  simp_rw [hc]
  exact integral_const_mul c _

/-- The polar integral of actual restricted ambient top forms is continuous
under uniform ambient operator-norm convergence. Smoothness supplies the
required integrability internally via the existing sphere-form theorem. -/
theorem tendsto_sphereFormIntegral_of_uniform_ambient {T : Type*} {l : Filter T}
    (b : OrthonormalBasis (Fin (d + 1)) ℝ E)
    {β : T → sphere (0 : E) 1 → E [⋀^Fin d]→L[ℝ] ℝ}
    {γ : sphere (0 : E) 1 → E [⋀^Fin d]→L[ℝ] ℝ}
    (hβ : ∀ᶠ t in l, DifferentialForm.IsSmooth (ambientSphereRestriction (β t)))
    (hγ : DifferentialForm.IsSmooth (ambientSphereRestriction γ))
    (hconv : TendstoUniformlyOn β γ l univ) :
    Tendsto (fun t => sphereFormIntegral b (ambientSphereRestriction (β t)))
      l (𝓝 (sphereFormIntegral b (ambientSphereRestriction γ))) := by
  apply tendsto_integral_of_uniform (volume : Measure E).toSphere
  · exact hβ.mono (fun t ht => integrable_sphereFormCoefficient b _ ht)
  · exact integrable_sphereFormCoefficient b _ hγ
  · exact uniform_sphereFormCoefficient_of_ambient b hconv

end Integrals

end GaussBonnetChern.AngularBoundary
