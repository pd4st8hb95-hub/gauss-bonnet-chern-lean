import GaussBonnetChern.CriticalMorseCharts
import GaussBonnetChern.MorseLocalizedDeformation
import GaussBonnetChern.MorseVectorField

/-! # Actual geometric modification of a critical level

The charts are constructed for the entire fiber of the actual critical set.
Finiteness isolates that value from every other critical value. Shrinking the
common scale then supplies the chart domains and the regular complement needed
by the explicit smooth lowering construction.

The resulting function and deformation are actual functions on the manifold.
No handle attachment, relative-homology comparison, or Morse chart is assumed.
-/

noncomputable section

open Set Function Filter Bundle
open scoped Topology Manifold ContDiff GaussBonnetChern.MorseCharts

namespace GaussBonnetChern.Morse

open MorseCharts

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]

/-- All critical points at one value, with no distinct-value hypothesis. -/
abbrev CriticalValueFiber (f : M → ℝ) (c : ℝ) :=
  {p : M // mvfderiv (model n) f p = 0 ∧ f p = c}

theorem finite_criticalValueFiber {f : M → ℝ}
    (hfin : {p : M | mvfderiv (model n) f p = 0}.Finite) (c : ℝ) :
    Finite (CriticalValueFiber n M f c) := by
  apply Set.Finite.to_subtype
  exact hfin.subset (fun _ hx => hx.1)

/-- The finite actual critical set gives an isolating closed interval. -/
theorem exists_criticalFiber_band {f : M → ℝ}
    (hfin : {p : M | mvfderiv (model n) f p = 0}.Finite) (c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : M,
      mvfderiv (model n) f p = 0 → f p ∈ Icc (c - ε) (c + ε) → f p = c := by
  let S := (f '' {p : M | mvfderiv (model n) f p = 0}) \ {c}
  have hS : IsClosed S := ((hfin.image f).sdiff (t := {c})).isClosed
  have hc : c ∈ Sᶜ := by simp [S]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hS.isOpen_compl.mem_nhds hc)
  refine ⟨r / 2, by positivity, ?_⟩
  intro p hp hpc
  by_contra hne
  have hdist : dist (f p) c < r := by
    rw [Real.dist_eq]
    have ha : |f p - c| ≤ r / 2 := abs_le.mpr ⟨by linarith [hpc.1], by linarith [hpc.2]⟩
    linarith
  exact hball hdist ⟨⟨p, hp, rfl⟩, hne⟩

/-- Every member of a complete critical-value fiber receives an actual
disjoint smooth Morse chart. Both the common block scale and regularity of
the remaining closed band are constructed, including an empty fiber. -/
theorem exists_criticalValueFiber_morse_charts [T2Space M]
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hfin : {p : M | mvfderiv (model n) f p = 0}.Finite)
    (hH : ∀ p, mvfderiv (model n) f p = 0 →
      Function.Injective (connection n M (gradient n M f) p)) (c : ℝ) :
    ∃ (w : CriticalValueFiber n M f c → Fin (Module.finrank ℝ (Model n)) → ℝ)
      (e : ∀ i : CriticalValueFiber n M f c, OpenPartialHomeomorph M
        (LiftedNegativeSpace.{u} (w i) × LiftedPositiveSpace.{u} (w i)))
      (ε : ℝ),
      0 < ε ∧ (∀ i, (i : M) ∈ (e i).source) ∧ (∀ i, e i (i : M) = 0) ∧
      (∀ i, ContMDiffOn (model n)
        𝓘(ℝ, LiftedNegativeSpace.{u} (w i) × LiftedPositiveSpace.{u} (w i)) ∞
        (e i) (e i).source) ∧
      (∀ i, ContMDiffOn
        𝓘(ℝ, LiftedNegativeSpace.{u} (w i) × LiftedPositiveSpace.{u} (w i)) (model n) ∞
        (e i).symm (e i).target) ∧
      (∀ i x, x ∈ (e i).source → f x = handleQuadratic c (e i x)) ∧
      (∀ i, Module.finrank ℝ (LiftedNegativeSpace.{u} (w i)) = morseIndex n M (hf (i : M))) ∧
      Pairwise (fun i j => Disjoint (e i).source (e j).source) ∧
      (∀ i, coordinateBlock ε ⊆ (e i).target) ∧
      (∀ x, f x ∈ Icc (c - ε) (c + ε) →
        (∀ i, x ∉ (e i).source) → mvfderiv (model n) f x ≠ 0) := by
  classical
  letI := finite_criticalValueFiber n M hfin c
  letI : Fintype (CriticalValueFiber n M f c) := Fintype.ofFinite _
  obtain ⟨w, e, δ, hδ, hpe, he0, hes, hei, hform, hindex, hdis, hblock⟩ :=
    exists_lifted_finite_disjoint_morse_charts n M hf
      (Subtype.val : CriticalValueFiber n M f c → M) Subtype.val_injective
      (fun i => i.property.1) (fun i => hH i i.property.1)
  obtain ⟨r, hr, hband⟩ := exists_criticalFiber_band n M hfin c
  let ε := min δ r
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεr : ε ≤ r := min_le_right _ _
  refine ⟨w, e, ε, lt_min hδ hr, hpe, he0, hes, hei, ?_, hindex, hdis, ?_, ?_⟩
  · intro i x hx
    simpa only [i.property.2, handleQuadratic] using hform i x hx
  · intro i
    exact (productBlock_mono hεδ).trans (hblock i)
  · intro x hx hout hcrit
    have hvalue : f x = c := hband x hcrit
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    let i : CriticalValueFiber n M f c := ⟨x, hcrit, hvalue⟩
    exact hout i (hpe i)

/-- A critical layer can be lowered by a globally smooth function, with its
upper sublevel unchanged and its entire new closed band regular. The actual
flow retracts the old upper sublevel to the new lower one and fixes the old
lower sublevel pointwise throughout the deformation. -/
theorem exists_criticalLevel_lowering_and_deformation [T2Space M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hfin : {p : M | mvfderiv (model n) f p = 0}.Finite)
    (hH : ∀ p, mvfderiv (model n) f p = 0 →
      Function.Injective (connection n M (gradient n M f) p)) (c : ℝ) :
    ∃ (ε : ℝ) (g : M → ℝ), 0 < ε ∧
      ContMDiff (model n) 𝓘(ℝ) ∞ g ∧
      (∀ x, g x ≤ f x) ∧
      {x | g x ≤ c + ε} = {x | f x ≤ c + ε} ∧
      (∀ x, g x ∈ Icc (c - ε) (c + ε) → mvfderiv (model n) g x ≠ 0) ∧
      ∃ H : M × ℝ → M, Continuous H ∧
        (∀ x, H (x, 0) = x) ∧
        (∀ x, f x ≤ c + ε → ∀ s ∈ Icc (0 : ℝ) 1, f (H (x, s)) ≤ c + ε) ∧
        (∀ x, f x ≤ c + ε → g (H (x, 1)) ≤ c - ε) ∧
        ∀ x, f x ≤ c - ε → ∀ s, H (x, s) = x := by
  classical
  letI := finite_criticalValueFiber n M hfin c
  letI : Fintype (CriticalValueFiber n M f c) := Fintype.ofFinite _
  obtain ⟨w, e, ε, hε, hpe, he0, he, hei, hform, hindex, hdis, hblock, hreg⟩ :=
    exists_criticalValueFiber_morse_charts n M hf hfin hH c
  have hsub i : handleEllipsoid ε ⊆ (e i).target :=
    (handleEllipsoid_subset_coordinateBlock hε).trans (hblock i)
  refine ⟨ε, finiteChartLowering e ε f, hε,
    contMDiff_finiteChartLowering e hε hsub he hf,
    finiteChartLowering_le e hε f,
    finiteChartLowering_upper_sublevel e hε f hdis hform,
    finiteChartLowering_regular_band e hε hsub he hei hf hdis hform hreg, ?_⟩
  exact exists_criticalLevel_deformation e hε hsub he hei hf hdis hform hreg

/-- The determinant certificate already obtained for the actual gradient
implies nondegeneracy of the actual covariant derivative used by the charts. -/
theorem connection_gradient_injective_of_linearization_det_ne_zero
    {f : M → ℝ} {p : M} (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f p)
    (hp : mvfderiv (model n) f p = 0)
    (hdet : LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap ≠ 0) :
    Function.Injective (connection n M (gradient n M f) p) := by
  have hker : LinearMap.ker (fieldLinearization n M p (gradient n M f)).toLinearMap = ⊥ := by
    by_contra hne
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
  have hinj := LinearMap.ker_eq_bot.mp hker
  intro v w hvw
  apply hinj
  change fieldLinearization n M p (gradient n M f) v =
    fieldLinearization n M p (gradient n M f) w
  rw [gradientLinearization_eq_connection n M hf hp]
  exact hvw

/-- One actual Morse function simultaneously has the original metric index
sign and the constructed geometric modification at every critical value. -/
theorem exists_morse_function_with_criticalLevel_geometry [T2Space M] [CompactSpace M] :
    ∃ (f : M → ℝ) (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f),
      {p : M | mvfderiv (model n) f p = 0}.Finite ∧
      (∀ p, mvfderiv (model n) f p = 0 →
        LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap ≠ 0 ∧
          Real.sign (LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap) =
            (-1 : ℝ) ^ morseIndex n M (hf p)) ∧
      ∀ c : ℝ, ∃ (ε : ℝ) (g : M → ℝ), 0 < ε ∧
        ContMDiff (model n) 𝓘(ℝ) ∞ g ∧ (∀ x, g x ≤ f x) ∧
        {x | g x ≤ c + ε} = {x | f x ≤ c + ε} ∧
        (∀ x, g x ∈ Icc (c - ε) (c + ε) → mvfderiv (model n) g x ≠ 0) ∧
        ∃ H : M × ℝ → M, Continuous H ∧
          (∀ x, H (x, 0) = x) ∧
          (∀ x, f x ≤ c + ε → ∀ s ∈ Icc (0 : ℝ) 1, f (H (x, s)) ≤ c + ε) ∧
          (∀ x, f x ≤ c + ε → g (H (x, 1)) ≤ c - ε) ∧
          ∀ x, f x ≤ c - ε → ∀ s, H (x, s) = x := by
  obtain ⟨f, hf, hfin, hsign⟩ := exists_morse_function_with_index_sign n M
  have hH (p : M) (hp : mvfderiv (model n) f p = 0) :
      Function.Injective (connection n M (gradient n M f) p) :=
    connection_gradient_injective_of_linearization_det_ne_zero n M (hf p) hp (hsign p hp).1
  exact ⟨f, hf, hfin, hsign, fun c =>
    exists_criticalLevel_lowering_and_deformation n M hf hfin hH c⟩

end GaussBonnetChern.Morse
