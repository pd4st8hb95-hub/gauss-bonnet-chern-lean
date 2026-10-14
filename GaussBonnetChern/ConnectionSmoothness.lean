import GaussBonnetChern.Geometry
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Local smoothness of the Levi-Civita connection

The lemmas in this file concern the actual connection used by the statement.
They introduce no replacement connection or additional geometric hypothesis.
-/

noncomputable section

open Bundle Filter
open scoped Manifold Topology ContDiff

namespace GaussBonnetChern

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

/-- The derivative of a smooth scalar function evaluated on a smooth vector
field is smooth at the same point. -/
theorem contMDiffAt_directionalDerivative {f : M → ℝ}
    {X : (x : M) → TangentSpace (model n) x} {x : M}
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x)
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x) :
    ContMDiffAt (model n) 𝓘(ℝ) ∞ (fun y ↦ mvfderiv (model n) f y (X y)) x := by
  have hd := hf.mfderiv_const (m := ∞) (by simp)
  have ht : ContMDiffAt (model n) 𝓘(ℝ).tangent ∞
      (fun y ↦ (⟨f y, mfderiv (model n) 𝓘(ℝ) f y (X y)⟩ : TangentBundle 𝓘(ℝ) ℝ)) x :=
    hd.clm_apply_of_inCoordinates hX hf
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ) (n := ∞)).contMDiffAt.comp x ht

omit [IsManifold (model n) ∞ M] in
/-- Smoothness of all constant-vector evaluations detects smoothness of a
finite-dimensional continuous-linear-map-valued function. -/
theorem contMDiffAt_clm_of_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → Model n →L[ℝ] F} {x : M}
    (h : ∀ v, ContMDiffAt (model n) 𝓘(ℝ, F) ∞ (fun y ↦ f y v) x) :
    ContMDiffAt (model n) 𝓘(ℝ, Model n →L[ℝ] F) ∞ f x := by
  let d := Module.finrank ℝ (Model n)
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[ℝ] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.comp_contMDiffAt (contMDiffAt_pi_space.mpr fun i ↦ h _)

variable [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

/-- The scalar Koszul expression of locally smooth vector fields is smooth.
The formula refers to the actual Levi-Civita connection of the given metric. -/
theorem contMDiffAt_inner_connection
    {X Y Z : (x : M) → TangentSpace (model n) x} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x) :
    ContMDiffAt (model n) 𝓘(ℝ) ∞
      (fun y ↦ inner ℝ (connection n M Y y (X y)) (Z y)) x := by
  let : IsManifold (model n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (model n) 2 M)
  let : IsManifold (model n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (model n) ∞ M)
  let : IsContMDiffRiemannianBundle (model n) 1 (Model n)
      (TangentSpace (model n) : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have h1 := contMDiffAt_directionalDerivative n M (hY.inner_bundle hZ) hX
  have h2 := contMDiffAt_directionalDerivative n M (hZ.inner_bundle hX) hY
  have h3 := contMDiffAt_directionalDerivative n M (hX.inner_bundle hY) hZ
  have hXZ := hX.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hZ (by simp)
  have hYX := hY.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hX (by simp)
  have hZY := hZ.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hY (by simp)
  have h4 := hY.inner_bundle hXZ
  have h5 := hZ.inner_bundle hYX
  have h6 := hX.inner_bundle hZY
  have hr := (((((h1.add h2).sub h3).sub h4).sub h5).add h6).div_const (2 : ℝ)
  apply hr.congr_of_eventuallyEq
  have hx1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
    (hX.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hy1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
    (hY.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hz1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
    (hZ.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  filter_upwards [hx1, hy1, hz1] with y hxy hyy hzy
  exact CovariantDerivative.leviCivitaConnection_apply_inner (model n)
    (hxy.mdifferentiableAt (by simp)) (hyy.mdifferentiableAt (by simp))
    (hzy.mdifferentiableAt (by simp))

/-- A constant vector in a fixed bundle trivialization, transported back to
the tangent fibers. Only its germ in the trivialization domain is used. -/
def localFrameVector (x : M) (v : Model n) (y : M) : TangentSpace (model n) y :=
  (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) x).symmL ℝ y v

omit [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] in
theorem contMDiffAt_localFrameVector (x : M) (v : Model n) :
    ContMDiffAt (model n) (model n).tangent ∞ (T% (localFrameVector n M x v)) x := by
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) x
  have he := e.contMDiffAt_symmL (IB := model n) (n := ∞)
    (FiberBundle.mem_baseSet_trivializationAt' x)
  have hv : ContMDiffAt (model n) ((model n).prod 𝓘(ℝ, Model n)) ∞
      (fun y ↦ (⟨y, v⟩ : TotalSpace (Model n) (Bundle.Trivial M (Model n)))) x := by
    exact contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, contMDiffAt_const⟩
  exact he.clm_bundle_apply hv

/-- The actual metric expressed in a fixed local trivialization. -/
def localMetric (x y : M) : Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) x
  (innerSL ℝ).bilinearComp (e.symmL ℝ y) (e.symmL ℝ y)

theorem contMDiffAt_localMetric (x : M) :
    ContMDiffAt (model n) 𝓘(ℝ, Model n →L[ℝ] Model n →L[ℝ] ℝ) ∞
      (localMetric n M x) x := by
  apply contMDiffAt_clm_of_apply n M
  intro v
  apply contMDiffAt_clm_of_apply n M
  intro w
  exact (contMDiffAt_localFrameVector n M x v).inner_bundle
    (contMDiffAt_localFrameVector n M x w)

omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
  (TangentSpace (model n) : M → Type _)] in
/-- The local metric identifies the model space with its dual on the whole
domain of the chosen trivialization. -/
theorem localMetric_isInvertible (x y : M)
    (hy : y ∈ (trivializationAt (Model n) (TangentSpace (model n) : M → Type _) x).baseSet) :
    (localMetric n M x y).IsInvertible := by
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) x
  let q := (e.continuousLinearEquivAt ℝ y hy).symm
  let r := (InnerProductSpace.toDual ℝ (TangentSpace (model n) y)).toContinuousLinearEquiv
  refine ⟨q.trans (r.trans (q.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))), ?_⟩
  ext v w
  change inner ℝ (q v) (q w) = inner ℝ (e.symmL ℝ y v) (e.symmL ℝ y w)
  rw [e.symm_continuousLinearEquivAt_eq hy]

/-- Smooth dependence of the inverse metric in local coordinates. -/
theorem contMDiffAt_inverse_localMetric (x : M) :
    ContMDiffAt (model n) 𝓘(ℝ, (Model n →L[ℝ] ℝ) →L[ℝ] Model n) ∞
      (fun y ↦ (localMetric n M x y).inverse) x := by
  exact (localMetric_isInvertible n M x x
    (FiberBundle.mem_baseSet_trivializationAt' x)).contDiffAt_map_inverse.comp_contMDiffAt
      (contMDiffAt_localMetric n M x)

/-- A tangent section is smooth at a point when its metric pairings against
the constant local frame vectors are smooth there. -/
theorem contMDiffAt_section_of_inner_localFrame
    {W : (y : M) → TangentSpace (model n) y} {x : M}
    (hW : ∀ v : Model n, ContMDiffAt (model n) 𝓘(ℝ) ∞
      (fun y ↦ inner ℝ (W y) (localFrameVector n M x v y)) x) :
    ContMDiffAt (model n) (model n).tangent ∞ (T% W) x := by
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) x
  let b : M → Model n →L[ℝ] ℝ := fun y ↦ (innerSL ℝ (W y)).comp (e.symmL ℝ y)
  have hb : ContMDiffAt (model n) 𝓘(ℝ, Model n →L[ℝ] ℝ) ∞ b x :=
    contMDiffAt_clm_of_apply n M hW
  have hs := (contMDiffAt_inverse_localMetric n M x).clm_apply hb
  apply (contMDiffAt_section x).mpr
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  symm
  apply (localMetric_isInvertible n M x y hy).inverse_apply_eq.mpr
  ext v
  change inner ℝ (W y) (e.symmL ℝ y v) =
    inner ℝ (e.symmL ℝ y ((e ⟨y, W y⟩).2)) (e.symmL ℝ y v)
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hy,
    e.symmL_continuousLinearMapAt hy]

/-- Applying the actual Levi-Civita connection to locally smooth vector
fields produces a locally smooth tangent section. -/
theorem contMDiffAt_connection_apply
    {X Y : (x : M) → TangentSpace (model n) x} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x) :
    ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun y ↦ connection n M Y y (X y))) x := by
  apply contMDiffAt_section_of_inner_localFrame n M
  intro v
  exact contMDiffAt_inner_connection n M hX hY (contMDiffAt_localFrameVector n M x v)

/-- The covariant derivative of a locally smooth vector field is a smooth
section of the bundle of tangent-space endomorphisms. -/
theorem contMDiffAt_connection_section
    {Y : (x : M) → TangentSpace (model n) x} {x : M}
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x) :
    ContMDiffAt (model n) ((model n).prod 𝓘(ℝ, Model n →L[ℝ] Model n)) ∞
      (fun y ↦ TotalSpace.mk' (Model n →L[ℝ] Model n) y (connection n M Y y)) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply n M
  intro v
  have h := contMDiffAt_connection_apply n M (contMDiffAt_localFrameVector n M x v) hY
  have hc := (contMDiffAt_section x).mp h
  apply hc.congr_of_eventuallyEq
  let e := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) x
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hy _

/-- The actual connection in the Gauss–Bonnet–Chern statement is smooth. -/
theorem contMDiffCovariantDerivative_connection :
    CovariantDerivative.ContMDiffCovariantDerivative (connection n M) ∞ := by
  refine ⟨⟨?_⟩⟩
  intro Y hY x hx
  have hY' : ContMDiff (model n) (model n).tangent ∞ (T% Y) := by
    simpa [contMDiffOn_univ] using hY
  exact (contMDiffAt_connection_section n M (hY' x)).contMDiffWithinAt

end GaussBonnetChern
