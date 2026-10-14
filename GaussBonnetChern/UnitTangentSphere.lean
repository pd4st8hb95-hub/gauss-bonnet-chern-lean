import GaussBonnetChern.OrthonormalFrames
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # The actual unit tangent sphere and radial normalization

The sphere is the norm-one subset of the actual tangent bundle of the given
metric. It is not an auxiliary vector bundle supplied by the caller. This file
also computes the mass of the standard polar sphere measure in every positive
even dimension. The identification of that measure with the integral of the
oriented sphere volume form is a separate integration obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern
universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

/-- The unit tangent sphere of the metric used in the main statement. -/
abbrev UnitTangentSphere :=
  {v : TangentBundle (model n) M // ‖v.2‖ = 1}

namespace UnitTangentSphere

/-- Actual bundle projection restricted to norm-one vectors. -/
def proj (v : UnitTangentSphere n M) : M := v.1.1

/-- The tautological unit vector at its actual base point. -/
def vector (v : UnitTangentSphere n M) : TangentSpace (model n) (proj n M v) := v.1.2

@[simp] theorem norm_vector (v : UnitTangentSphere n M) : ‖vector n M v‖ = 1 := v.2

theorem vector_ne_zero (v : UnitTangentSphere n M) : vector n M v ≠ 0 := by
  intro h
  have := norm_vector n M v
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem continuous_proj : Continuous (proj n M) :=
  (FiberBundle.continuous_proj (Model n) (TangentSpace (model n) : M → Type _)).comp
    continuous_subtype_val

/-- Radial normalization of an actual nonzero tangent vector. -/
def ofNonzero (x : M) (v : TangentSpace (model n) x) (hv : v ≠ 0) :
    UnitTangentSphere n M :=
  ⟨⟨x, ‖v‖⁻¹ • v⟩, by simp [norm_smul, hv]⟩

@[simp] theorem proj_ofNonzero (x : M) (v : TangentSpace (model n) x) (hv : v ≠ 0) :
    proj n M (ofNonzero n M x v hv) = x := rfl

@[simp] theorem vector_ofNonzero (x : M) (v : TangentSpace (model n) x) (hv : v ≠ 0) :
    vector n M (ofNonzero n M x v hv) = ‖v‖⁻¹ • v := rfl

theorem ofNonzero_vector (v : UnitTangentSphere n M) :
    ofNonzero n M (proj n M v) (vector n M v) (vector_ne_zero n M v) = v := by
  apply Subtype.ext
  simp only [ofNonzero, norm_vector, inv_one, one_smul]
  rfl

end UnitTangentSphere

/-- Normalization as a section of the actual tangent bundle, defined also
at zeros (where it is zero). The smoothness statement below excludes zeros. -/
def normalizedVectorField (X : (x : M) → TangentSpace (model n) x)
    (x : M) : TangentSpace (model n) x := ‖X x‖⁻¹ • X x

theorem norm_normalizedVectorField {X : (x : M) → TangentSpace (model n) x}
    {x : M} (hx : X x ≠ 0) : ‖normalizedVectorField n M X x‖ = 1 := by
  simp [normalizedVectorField, norm_smul, hx]

/-- The norm of a smooth tangent field is smooth wherever the field does
not vanish. This uses the genuine smooth metric's inner product. -/
theorem contMDiffAt_norm_vectorField {X : (x : M) → TangentSpace (model n) x}
    {x : M} (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hx : X x ≠ 0) : ContMDiffAt (model n) 𝓘(ℝ) ∞ (fun y ↦ ‖X y‖) x := by
  have hi := hX.inner_bundle hX
  have hs := (Real.contDiffAt_sqrt (n := ∞)
    ((real_inner_self_pos.mpr hx).ne')).contMDiffAt.comp x hi
  simpa only [Function.comp_def, ← norm_eq_sqrt_real_inner] using hs

theorem contMDiffAt_normalizedVectorField
    {X : (x : M) → TangentSpace (model n) x} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hx : X x ≠ 0) :
    ContMDiffAt (model n) (model n).tangent ∞ (T% (normalizedVectorField n M X)) x := by
  exact ((contMDiffAt_norm_vectorField n M hX hx).inv₀ (norm_ne_zero_iff.mpr hx)).smul_section hX

/-- The fiber norm is continuous on the actual total tangent bundle. -/
theorem continuous_tangentNorm :
    Continuous (fun v : TangentBundle (model n) M ↦ ‖v.2‖) := by
  have hi : Continuous (fun v : TangentBundle (model n) M ↦ inner ℝ v.2 v.2) :=
    ((contMDiff_id : ContMDiff (model n).tangent (model n).tangent ∞
      (id : TangentBundle (model n) M → _)).inner_bundle contMDiff_id).continuous
  simpa only [← norm_eq_sqrt_real_inner] using hi.sqrt

/-- The unit sphere is the genuine closed norm level set. -/
theorem isClosed_unitTangentSphere :
    IsClosed {v : TangentBundle (model n) M | ‖v.2‖ = 1} :=
  isClosed_eq (continuous_tangentNorm n M) continuous_const

theorem isOpen_nonzeroTangentBundle :
    IsOpen {v : TangentBundle (model n) M | v.2 ≠ 0} := by
  simpa only [norm_ne_zero_iff] using
    (isOpen_ne_fun (continuous_tangentNorm n M) (continuous_const (y := (0:ℝ))))

/-- Smoothness of the actual fiber norm away from the zero section. -/
theorem contMDiffAt_tangentNorm (v : TangentBundle (model n) M) (hv : v.2 ≠ 0) :
    ContMDiffAt (model n).tangent 𝓘(ℝ) ∞
      (fun w : TangentBundle (model n) M ↦ ‖w.2‖) v := by
  have hi : ContMDiffAt (model n).tangent 𝓘(ℝ) ∞
      (fun w : TangentBundle (model n) M ↦ inner ℝ w.2 w.2) v :=
    (contMDiffAt_id : ContMDiffAt (model n).tangent (model n).tangent ∞
      (id : TangentBundle (model n) M → _) v).inner_bundle contMDiffAt_id
  have hs := (Real.contDiffAt_sqrt (n := ∞)
    ((real_inner_self_pos.mpr hv).ne')).contMDiffAt.comp v hi
  simpa only [Function.comp_def, ← norm_eq_sqrt_real_inner] using hs

/-- Actual coefficients of the tautological vector in the constructed local
orthonormal frame. They are defined on the total tangent bundle. -/
def localDirectionCoordinate (p : M) (i : Fin (2*n))
    (v : TangentBundle (model n) M) : ℝ :=
  inner ℝ (localOrthonormalFrame n M p i v.1) v.2

theorem contMDiffAt_localDirectionCoordinate (p : M) (i : Fin (2*n))
    (v : TangentBundle (model n) M)
    (hv : v.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ContMDiffAt (model n).tangent 𝓘(ℝ) ∞ (localDirectionCoordinate n M p i) v := by
  have hframe := (contMDiffAt_localOrthonormalFrame n M p i hv).comp v
    (contMDiffAt_proj (TangentSpace (model n) : M → Type _))
  exact hframe.inner_bundle contMDiffAt_id

theorem sum_sq_localDirectionCoordinate (p : M) (v : TangentBundle (model n) M)
    (hv : v.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet) :
    ∑ i, localDirectionCoordinate n M p i v ^ 2 = ‖v.2‖^2 := by
  simpa only [localOrthonormalBasis_apply n M p hv, Real.norm_eq_abs, sq_abs,
    localDirectionCoordinate] using
      (localOrthonormalBasis n M p v.1).sum_sq_norm_inner_right v.2

/-- Unit direction coordinates, extended by zero over the zero section.
All smoothness and unit-sphere assertions are made only away from zero. -/
def normalizedDirectionCoordinate (p : M) (i : Fin (2*n))
    (v : TangentBundle (model n) M) : ℝ :=
  ‖v.2‖⁻¹ * localDirectionCoordinate n M p i v

theorem contMDiffAt_normalizedDirectionCoordinate (p : M) (i : Fin (2*n))
    (v : TangentBundle (model n) M)
    (hv : v.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (hv0 : v.2 ≠ 0) :
    ContMDiffAt (model n).tangent 𝓘(ℝ) ∞ (normalizedDirectionCoordinate n M p i) v :=
  ((contMDiffAt_tangentNorm n M v hv0).inv₀ (norm_ne_zero_iff.mpr hv0)).mul
    (contMDiffAt_localDirectionCoordinate n M p i v hv)

/-- Chern's unit-vector relation holds for the actual metric coordinates. -/
theorem sum_sq_normalizedDirectionCoordinate (p : M) (v : TangentBundle (model n) M)
    (hv : v.1 ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) p).baseSet)
    (hv0 : v.2 ≠ 0) :
    ∑ i, normalizedDirectionCoordinate n M p i v ^ 2 = 1 := by
  simp only [normalizedDirectionCoordinate, mul_pow, ← Finset.mul_sum]
  rw [sum_sq_localDirectionCoordinate n M p v hv]
  field_simp

end GaussBonnetChern

namespace GaussBonnetChern.Chern

/-- Exact polar sphere mass in dimension `2*n`. This is a theorem about
Mathlib's actual polar measure, not a stipulated sphere-area constant. -/
theorem sphereMeasure_mass (n : ℕ) (hn : 0 < n) :
    (volume : Measure (Model n)).toSphere.real Set.univ =
      2 * Real.pi ^ n / ((n-1).factorial : ℝ) := by
  letI : Nontrivial (Model n) := Module.nontrivial_of_finrank_pos
    (R := ℝ) (by simpa [Model] using (show 0 < 2*n by omega))
  rw [Measure.toSphere_real_apply_univ]
  have hdim : Module.finrank ℝ (Model n) = 2*n := by simp [Model]
  rw [hdim]
  have hball := InnerProductSpace.volume_ball_of_dim_even hdim (0 : Model n) (1 : ℝ)
  have hreal : (volume : Measure (Model n)).real (Metric.ball 0 1) =
      Real.pi ^ n / (n.factorial : ℝ) := by
    simp only [measureReal_def, hball, ENNReal.ofReal_one, one_pow, one_mul]
    exact ENNReal.toReal_ofReal (by positivity)
  rw [hreal]
  have hfac : (n.factorial : ℝ) = (n:ℝ) * ((n-1).factorial:ℝ) := by
    rw [← Nat.succ_pred_eq_of_pos hn, Nat.factorial_succ]
    push_cast
    rfl
  rw [hfac]
  have hnz : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp
  <;> ring

end GaussBonnetChern.Chern
