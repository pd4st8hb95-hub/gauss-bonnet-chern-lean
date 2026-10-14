import GaussBonnetChern.EmptyManifold
import GaussBonnetChern.SurfaceNormalization
import GaussBonnetChern.HessianInertia
import GaussBonnetChern.GradientLinearization
import GaussBonnetChern.MorseTopologicalIndex
import GaussBonnetChern.SphereHomology
import GaussBonnetChern.ChernFiberNormalization

/-! # Acceptance regressions against the actual geometric and topological interfaces

These regressions do not import the candidate main theorem. Endpoint Hessian
tests use the actual covariant Hessian and the actual gradient linearization.
Critical-value tests retain every point in a fiber and the actual singular
homology Euler characteristic. Sphere tests compute actual singular homology;
the angular normalization is on a tangent-sphere fiber, not the Euler form of
a closed even-dimensional sphere with its induced metric.
-/

noncomputable section
open Bundle Module MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace GaussBonnetChern.AcceptanceRegression

universe u

section MetricEndpoints

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

/-- A nondegenerate actual gradient at either extreme Morse index has positive
determinant sign in every even dimension. No coordinate normal form is assumed. -/
theorem actual_gradient_endpoint_sign {f : M → ℝ} {p : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f p)
    (hp : mvfderiv (model n) f p = 0)
    (hdet : LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap ≠ 0)
    (hindex : morseIndex n M hf = 0 ∨ morseIndex n M hf = 2 * n) :
    Real.sign (LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap) = 1 := by
  rw [sign_gradientLinearization_det n M hf hp hdet]
  rcases hindex with hindex | hindex
  · simp [hindex]
  · simp [hindex, pow_mul]

/-- This is a model condition on the actual metric Hessian of an actual smooth
function, rather than an unrelated test matrix. It does not assert existence
of a function having this Hessian on an arbitrary manifold. -/
theorem actual_positive_hessian_endpoint {f : M → ℝ} {p : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f p)
    (hp : mvfderiv (model n) f p = 0)
    (hH : hessianMatrix n M f p = Matrix.diagonal (fun _ ↦ (1 : ℝ))) :
    morseIndex n M hf = 0 ∧
      Real.sign (LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap) = 1 := by
  have hindex : morseIndex n M hf = 0 := by
    simpa only [morseIndex, hH] using
      (negativeEigenvalueCount_positive_identity (ι := Fin (2 * n)))
  have hdet : LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap ≠ 0 := by
    rw [gradientLinearization_eq_connection n M hf hp, ← hessianMatrix_det n M f p, hH]
    simp [Matrix.det_diagonal]
  exact ⟨hindex, actual_gradient_endpoint_sign n M hf hp hdet (Or.inl hindex)⟩

/-- The maximal index is `2*n`, and therefore its determinant sign agrees
with index zero. The statement is uniform in `n`, including the auxiliary
zero-dimensional endpoint. -/
theorem actual_negative_hessian_endpoint {f : M → ℝ} {p : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f p)
    (hp : mvfderiv (model n) f p = 0)
    (hH : hessianMatrix n M f p = Matrix.diagonal (fun _ ↦ (-1 : ℝ))) :
    morseIndex n M hf = 2 * n ∧
      Real.sign (LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap) = 1 := by
  have hindex : morseIndex n M hf = 2 * n := by
    simpa only [morseIndex, hH, Fintype.card_fin] using
      (negativeEigenvalueCount_negative_identity (ι := Fin (2 * n)))
  have hdet : LinearMap.det (fieldLinearization n M p (gradient n M f)).toLinearMap ≠ 0 := by
    rw [gradientLinearization_eq_connection n M hf hp, ← hessianMatrix_det n M f p, hH]
    simp [Matrix.det_diagonal]
  exact ⟨hindex, actual_gradient_endpoint_sign n M hf hp hdet (Or.inr hindex)⟩

end MetricEndpoints

section SameValue

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

/-- Every point in a common critical-value fiber contributes. If its indices
agree, its Euler jump is the fiber cardinality times the common sign. The
geometric step is obtained from the actual Morse charts and relative homology. -/
theorem actual_sameValue_euler_jump {f : M → ℝ}
    (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hfin : {p : M | mvfderiv (model n) f p = 0}.Finite)
    (hH : ∀ p, mvfderiv (model n) f p = 0 →
      Function.Injective (connection n M (gradient n M f) p))
    (c : ℝ) (q : ℕ)
    (hq : ∀ p ∈ hfin.toFinset, f p = c → morseIndex n M (hf p) = q) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
      FiniteSingularHomologyBound {x : M // f x ≤ c - ε} (2 * n) →
      FiniteSingularHomologyBound {x : M // f x ≤ c + ε} (2 * n) ∧
        topologicalEulerCharacteristic {x : M // f x ≤ c + ε} =
          topologicalEulerCharacteristic {x : M // f x ≤ c - ε} +
            ((hfin.toFinset.filter (fun p ↦ f p = c)).card : ℤ) * (-1 : ℤ) ^ q := by
  classical
  obtain ⟨ρ, hρ, hstep⟩ := actual_criticalValue_euler_step n M hf hfin hH c
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ hA
  obtain ⟨hB, he⟩ := hstep ε hε hερ hA
  refine ⟨hB, ?_⟩
  rw [he]
  congr 1
  calc
    (∑ p ∈ hfin.toFinset with f p = c, (-1 : ℤ) ^ morseIndex n M (hf p)) =
        ∑ p ∈ hfin.toFinset with f p = c, (-1 : ℤ) ^ q := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hq p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2]
    _ = _ := by simp [nsmul_eq_mul]

/-- Two same-value extrema give a jump of two, not a single-point jump of one.
The cardinality assumption retains the full actual critical fiber. -/
theorem actual_two_sameValue_minima_jump {f : M → ℝ}
    (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hfin : {p : M | mvfderiv (model n) f p = 0}.Finite)
    (hH : ∀ p, mvfderiv (model n) f p = 0 →
      Function.Injective (connection n M (gradient n M f) p))
    (c : ℝ)
    (hq : ∀ p ∈ hfin.toFinset, f p = c → morseIndex n M (hf p) = 0)
    (hcard : (hfin.toFinset.filter (fun p ↦ f p = c)).card = 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
      FiniteSingularHomologyBound {x : M // f x ≤ c - ε} (2 * n) →
      FiniteSingularHomologyBound {x : M // f x ≤ c + ε} (2 * n) ∧
        topologicalEulerCharacteristic {x : M // f x ≤ c + ε} =
          topologicalEulerCharacteristic {x : M // f x ≤ c - ε} + 2 := by
  simpa only [hcard, pow_zero, mul_one, Nat.cast_ofNat] using
    actual_sameValue_euler_jump n M hf hfin hH c 0 hq

/-- The actual finite sublevel induction and the fiberwise finite-sum identity
combine without requiring distinct critical values or connectedness. -/
theorem actual_morse_euler_grouped_by_value {f : M → ℝ}
    (hf : ContMDiff (model n) 𝓘(ℝ) ∞ f)
    (hfin : {p : M | mvfderiv (model n) f p = 0}.Finite)
    (hH : ∀ p, mvfderiv (model n) f p = 0 →
      Function.Injective (connection n M (gradient n M f) p)) :
    FiniteSingularHomologyBound M (2 * n) ∧
      topologicalEulerCharacteristic M =
        ∑ c ∈ finiteCriticalValues f hfin,
          ∑ p ∈ hfin.toFinset with f p = c, (-1 : ℤ) ^ morseIndex n M (hf p) := by
  obtain ⟨hbound, he⟩ := actual_morse_homology_and_euler n M hf hfin hH
  exact ⟨hbound, he.trans
    (criticalValue_fiber_sum f hfin (fun p ↦ (-1 : ℤ) ^ morseIndex n M (hf p))).symm⟩

end SameValue

section Orientation

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M] [CompactSpace M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

/-- Opposite orientation changes the actual Euler top form by a sign, while
the scalar density and its positive Riemannian integral retain their value. -/
theorem opposite_orientation_euler_compatibility (hn : 0 < n)
    (a b : FiniteOrientedAtlas n M) (hab : a.Opposite b)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (τ : SmoothPartitionOfUnity (Fin b.card) (model n) M Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (hτ : τ.IsSubordinate (fun i ↦ (b.chart i).source)) :
    atlasEulerForm n M a hn = -atlasEulerForm n M b hn ∧
      (∀ x : M, frameEulerAlternating n M x (atlasOrthonormalFrame n M a hn x)
          (atlasOrthonormalFrame n M a hn x) =
        frameEulerAlternating n M x (atlasOrthonormalFrame n M b hn x)
          (atlasOrthonormalFrame n M b hn x)) ∧
      integralTopForm a ρ (atlasEulerForm n M a hn) =
        integralTopForm b τ (atlasEulerForm n M b hn) := by
  refine ⟨atlasEulerForm_neg_of_opposite n M a b hab hn, ?_, ?_⟩
  · intro x
    exact frameEulerAlternating_orthonormal_independent n M x
      (atlasOrthonormalFrame n M b hn x) (atlasOrthonormalFrame n M a hn x)
  · rw [integralTopForm_atlasEulerForm n M a hn ρ,
      integralTopForm_atlasEulerForm n M b hn τ]
    exact curvatureIntegral_independent n M hn a b ρ τ hρ hτ

/-- Holding the form fixed while reversing orientation negates the integral.
Together with the previous regression, this checks both sign changes. -/
theorem opposite_orientation_fixed_form (a b : FiniteOrientedAtlas n M)
    (hab : a.Opposite b)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M Set.univ)
    (τ : SmoothPartitionOfUnity (Fin b.card) (model n) M Set.univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (hτ : τ.IsSubordinate (fun i ↦ (b.chart i).source))
    (α : DifferentialForm.Form (model n) M (2 * n))
    (hα : DifferentialForm.IsSmooth α) :
    integralTopForm a ρ α = -integralTopForm b τ α :=
  integralTopForm_neg_of_opposite n M a b hab ρ τ hρ hτ α hα

end Orientation

section Spheres

/-- Actual real singular homology computes every even sphere's Euler value.
This theorem does not refer to a curvature integral or the candidate GBC proof. -/
theorem even_unitSphere_euler (n : ℕ) (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : finrank ℝ E = 2 * n + 1) :
    topologicalEulerCharacteristic (Metric.sphere (0 : E) 1) = 2 := by
  rw [unitSphere_topologicalEulerCharacteristic (2 * n) hE]
  simp [pow_mul]

theorem standard_twoSphere_euler :
    topologicalEulerCharacteristic
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) = 2 := by
  exact even_unitSphere_euler 1 _ (by simp)

theorem standard_fourSphere_euler :
    topologicalEulerCharacteristic
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) = 2 := by
  exact even_unitSphere_euler 2 _ (by simp)

/-- The actual two-dimensional density has the unit-curvature normalization.
The premise is an actual curvature component, and is not proved here for the
induced metric on `S²`. Thus this is not a sphere Gauss--Bonnet theorem. -/
theorem actual_unit_curvature_surface_density (M : Type u)
    [TopologicalSpace M] [ChartedSpace (Model 1) M] [IsManifold (model 1) ∞ M]
    [RiemannianBundle (TangentSpace (model 1) : M → Type _)]
    [IsContMDiffRiemannianBundle (model 1) ∞ (Model 1)
      (TangentSpace (model 1) : M → Type _)]
    (x : M) (hK : curvatureComponents 1 M x 0 1 0 1 = 1) :
    eulerDensity 1 M x = 1 / (2 * Real.pi) := by
  rw [eulerDensity_surface M x, hK]

/-- A genuinely normalized angular form integrates to one on each actual
metric tangent-sphere fiber in every positive `n`. Its sphere dimension is
`2*n-1`; this does not replace the closed `S^(2*n)` metric regression. -/
theorem actual_angular_fiber_normalization (n : ℕ) (M : Type u)
    [TopologicalSpace M] [ChartedSpace (Model n) M] [IsManifold (model n) ∞ M]
    [RiemannianBundle (TangentSpace (model n) : M → Type _)]
    [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
      (TangentSpace (model n) : M → Type _)] [Fact (0 < n)]
    (a : FiniteOrientedAtlas n M) (i : Fin a.card) (x : M)
    (hx : x ∈ (a.chart i).source) :
    sphereFormIntegral (chernFiberModelBasis n)
      (DifferentialForm.pullback (I := 𝓡 (2 * n - 1))
        (sphereFiberInclusion n M x (chartOrthonormalBasis n M (a.chart i) x))
        (atlasSphereAngularForm n M a)) = 1 :=
  atlasSphereAngularForm_fiber_integral n M a i x hx

end Spheres

end GaussBonnetChern.AcceptanceRegression
