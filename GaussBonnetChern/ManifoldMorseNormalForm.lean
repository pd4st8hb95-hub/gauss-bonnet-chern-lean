import GaussBonnetChern.CriticalHessianIndex
import GaussBonnetChern.MorseNormalForm

/-! # The coordinate Hessian is nondegenerate for the original metric

These bridges apply the Euclidean Morse lemma to the same metric Hessian and
Morse index already used by the gradient construction.
-/

noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff
namespace GaussBonnetChern
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (TangentSpace (model n) : M → Type _)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem coordinate_hessian_injective_of_connection_gradient
    {f : M → ℝ} {g : E → M} {s : Set E} {y : E}
    (hs : IsOpen s) (hy : y ∈ s)
    (hg : ContMDiffOn 𝓘(ℝ, E) (model n) ∞ g s)
    (hgi : ∀ z ∈ s, (mfderiv 𝓘(ℝ, E) (model n) g z).IsInvertible)
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f (g y))
    (hcritical : mvfderiv (model n) f (g y) = 0)
    (hH : Function.Injective (connection n M (gradient n M f) (g y))) :
    Function.Injective (fderiv ℝ (fderiv ℝ (f ∘ g)) y) := by
  intro a b hab
  apply (hgi y hy).injective
  apply hH
  apply ext_inner_right ℝ
  intro z
  obtain ⟨w, hw⟩ : ∃ w : E, mfderiv 𝓘(ℝ, E) (model n) g y w = z := (hgi y hy).surjective z
  have h := congrArg (fun L : E →L[ℝ] ℝ ↦ L w) hab
  rw [hessian_pullback_at_critical n M hs hy hg hgi hf hcritical,
    hessian_pullback_at_critical n M hs hy hg hgi hf hcritical] at h
  simpa only [hessian, hw] using h

theorem coordinate_hessian_isInvertible_of_connection_gradient
    {f : M → ℝ} {g : E → M} {s : Set E} {y : E}
    (hs : IsOpen s) (hy : y ∈ s)
    (hg : ContMDiffOn 𝓘(ℝ, E) (model n) ∞ g s)
    (hgi : ∀ z ∈ s, (mfderiv 𝓘(ℝ, E) (model n) g z).IsInvertible)
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f (g y))
    (hcritical : mvfderiv (model n) f (g y) = 0)
    (hH : Function.Injective (connection n M (gradient n M f) (g y))) :
    (fderiv ℝ (fderiv ℝ (f ∘ g)) y).IsInvertible := by
  let H := fderiv ℝ (fderiv ℝ (f ∘ g)) y
  have hinj : Function.Injective H :=
    coordinate_hessian_injective_of_connection_gradient n M hs hy hg hgi hf hcritical hH
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ E).toLinearEquiv.finrank_eq
  have hsurj : Function.Surjective H :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let e := (LinearEquiv.ofBijective H.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

/-- A genuine Morse normal form in any actual inverse chart, with its
negative coordinate count identified with the original metric index. -/
theorem morse_normal_form_in_parametrization
    {f : M → ℝ} {g : E → M} {s : Set E} {y : E}
    (hs : IsOpen s) (hy : y ∈ s)
    (hg : ContMDiffOn 𝓘(ℝ, E) (model n) ∞ g s)
    (hgi : ∀ z ∈ s, (mfderiv 𝓘(ℝ, E) (model n) g z).IsInvertible)
    (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hcritical : mvfderiv (model n) f (g y) = 0)
    (hH : Function.Injective (connection n M (gradient n M f) (g y))) :
    ∃ (w : Fin (Module.finrank ℝ E) → ℝ)
      (e : OpenPartialHomeomorph E (Fin (Module.finrank ℝ E) → ℝ)),
      (∀ i, w i = -1 ∨ w i = 1) ∧
      (0 : E) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ v ∈ e.source, y + v ∈ s ∧
        f (g (y + v)) = f (g y) + ∑ i, w i * (e v i) ^ 2) ∧
      morseIndex n M (hf (g y)) = {i | w i < 0}.ncard := by
  have hF : ContDiffOn ℝ ∞ (f ∘ g) s := (hf.comp_contMDiffOn hg).contDiffOn
  have h0 := mvfderiv_comp y ((hf _).mdifferentiableAt (by simp))
    ((hg.contMDiffAt (hs.mem_nhds hy)).mdifferentiableAt (by simp))
  rw [hcritical, ContinuousLinearMap.zero_comp, mvfderiv_eq_fderiv] at h0
  have h0' : fderiv ℝ (f ∘ g) y = 0 := by simpa using! h0
  have hInv := coordinate_hessian_isInvertible_of_connection_gradient n M hs hy hg hgi
    (hf _) hcritical hH
  obtain ⟨w, e, hw, hsrc, he0, he, hei, hform, hi⟩ :=
    MorseLocal.morse_normal_form hs hy hF h0' hInv
  refine ⟨w, e, hw, hsrc, he0, he, hei, hform, ?_⟩
  rw [morseIndex_eq_sigNeg_coordinate_half_hessian n M hs hy hg hgi (hf _) hcritical]
  have heq : ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (f ∘ g)) y).toBilinForm.toQuadraticMap =
      (1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ (f ∘ g)) y).toBilinForm.toQuadraticMap := by
    ext v
    rfl
  rw [heq] at hi
  exact hi

end GaussBonnetChern
