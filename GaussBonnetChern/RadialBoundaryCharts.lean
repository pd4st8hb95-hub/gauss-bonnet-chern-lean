import GaussBonnetChern.PuncturedManifold
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Algebra.SMul

/-! # Radial boundary coordinates for complements of coordinate balls

The height is the actual radius minus the removed ball's radius. Thus the
domain is height nonnegative, and its outgoing normal at the inner boundary
is the negative radial direction. The derivative signs below verify this
convention in the Euclidean coordinates used for the balls.
-/

noncomputable section
open Set Metric TopologicalSpace
open scoped Topology ContDiff Manifold

namespace GaussBonnetChern.RadialBoundaryCharts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialHeight (r : ℝ) (x : E) : ℝ := ‖x‖ - r

def radialDirection (x : E) : E := ‖x‖⁻¹ • x

theorem contDiffAt_radialHeight (r : ℝ) (x : E) (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (radialHeight r) x :=
  (contDiffAt_norm ℝ hx).sub contDiffAt_const

theorem contDiffAt_radialDirection (x : E) (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ radialDirection x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

theorem radialHeight_nonneg_iff (r : ℝ) (x : E) :
    0 ≤ radialHeight r x ↔ x ∈ (ball (0 : E) r)ᶜ := by
  simp [radialHeight, mem_ball, dist_zero_right]

theorem radialHeight_zero_iff (r : ℝ) (x : E) :
    radialHeight r x = 0 ↔ x ∈ sphere (0 : E) r := by
  simp [radialHeight, sub_eq_zero]

theorem norm_radialDirection (x : E) (hx : x ≠ 0) : ‖radialDirection x‖ = 1 := by
  simp [radialDirection, norm_smul, norm_ne_zero_iff.mpr hx]

theorem radial_reconstruct (x : E) (hx : x ≠ 0) : ‖x‖ • radialDirection x = x := by
  simp [radialDirection, smul_smul, norm_ne_zero_iff.mpr hx]

theorem fderiv_radialHeight_radialDirection (r : ℝ) (x : E) (hx : x ≠ 0) :
    fderiv ℝ (radialHeight r) x (radialDirection x) = 1 := by
  have hd : DifferentiableAt ℝ (norm : E → ℝ) x :=
    (contDiffAt_norm (n := ∞) ℝ hx).differentiableAt (by simp)
  have hf : fderiv ℝ (radialHeight r) x = fderiv ℝ (norm : E → ℝ) x := by
    exact (hd.hasFDerivAt.sub_const r).fderiv
  rw [hf, radialDirection, map_smul, hd.fderiv_norm_self, smul_eq_mul,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- For the complement of a ball the outward normal points toward the
deleted ball, so the height derivative on that normal is negative. -/
theorem fderiv_radialHeight_inner_normal (r : ℝ) (x : E) (hx : x ≠ 0) :
    fderiv ℝ (radialHeight r) x (-radialDirection x) = -1 := by
  rw [map_neg, fderiv_radialHeight_radialDirection r x hx]

def radialCollar (r : ℝ) (u : sphere (0 : E) 1) (t : ℝ) : E := (r + t) • (u : E)

theorem radialHeight_radialCollar (r : ℝ) (u : sphere (0 : E) 1) (t : ℝ)
    (ht : 0 < r + t) : radialHeight r (radialCollar r u t) = t := by
  have hu : ‖(u : E)‖ = 1 := by simpa using u.property
  simp [radialHeight, radialCollar, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hu]

theorem radialDirection_radialCollar (r : ℝ) (u : sphere (0 : E) 1) (t : ℝ)
    (ht : 0 < r + t) : radialDirection (radialCollar r u t) = (u : E) := by
  have hu : ‖(u : E)‖ = 1 := by simpa using u.property
  simp [radialDirection, radialCollar, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hu,
    smul_smul, ht.ne']

theorem radialCollar_mem_compl_ball_iff (r : ℝ) (u : sphere (0 : E) 1) (t : ℝ)
    (ht : 0 < r + t) : radialCollar r u t ∈ (ball (0 : E) r)ᶜ ↔ 0 ≤ t := by
  rw [← radialHeight_nonneg_iff, radialHeight_radialCollar r u t ht]

/-- Recenter the actual positive radial coordinate at the removed sphere. -/
def positiveToHeight (r : ℝ) : Ioi (0 : ℝ) ≃ₜ Ioi (-r) where
  toFun t := ⟨t.1 - r, by change -r < t.1 - r; have ht : 0 < t.1 := t.2; linarith⟩
  invFun t := ⟨t.1 + r, by change 0 < t.1 + r; have ht : -r < t.1 := t.2; linarith⟩
  left_inv t := by ext; dsimp; ring
  right_inv t := by ext; dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The actual punctured Euclidean space in sphere and signed-height
coordinates. This retains a neighborhood on both sides of a positive-radius
sphere, so it is an ambient straightening construction. -/
def radialHeightHomeomorph (r : ℝ) :
    ({0}ᶜ : Set E) ≃ₜ (sphere (0 : E) 1 × Ioi (-r)) :=
  (homeomorphUnitSphereProd E).trans
    ((Homeomorph.refl (sphere (0 : E) 1)).prodCongr (positiveToHeight r))

@[simp] theorem radialHeightHomeomorph_fst (r : ℝ) (x : ({0}ᶜ : Set E)) :
    ((radialHeightHomeomorph r x).1 : E) = radialDirection (x : E) := by
  simp [radialHeightHomeomorph, positiveToHeight, radialDirection,
    homeomorphUnitSphereProd, homeomorphSphereProd]

@[simp] theorem radialHeightHomeomorph_snd (r : ℝ) (x : ({0}ᶜ : Set E)) :
    ((radialHeightHomeomorph r x).2 : ℝ) = radialHeight r (x : E) := by
  simp [radialHeightHomeomorph, positiveToHeight, radialHeight,
    homeomorphUnitSphereProd, homeomorphSphereProd]

@[simp] theorem radialHeightHomeomorph_symm (r : ℝ)
    (u : sphere (0 : E) 1) (t : Ioi (-r)) :
    ((radialHeightHomeomorph r).symm (u, t) : E) = radialCollar r u t := by
  simp [radialHeightHomeomorph, positiveToHeight, radialCollar,
    homeomorphUnitSphereProd, homeomorphSphereProd, add_comm]

theorem radialHeightHomeomorph_domain (r : ℝ) (x : ({0}ᶜ : Set E)) :
    (x : E) ∈ (ball (0 : E) r)ᶜ ↔ 0 ≤ ((radialHeightHomeomorph r x).2 : ℝ) := by
  rw [radialHeightHomeomorph_snd, radialHeight_nonneg_iff]

abbrev puncturedOpen : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩

theorem contMDiff_radialDirection :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x : (puncturedOpen (E := E)) ↦ radialDirection (x : E)) := by
  intro x
  have hx : (x : E) ≠ 0 := by
    exact x.property
  exact (contDiffAt_radialDirection (x : E) hx).contMDiffAt.comp x (contMDiff_subtype_val x)

def radialProjection (x : (puncturedOpen (E := E))) : sphere (0 : E) 1 :=
  ⟨radialDirection (x : E), by
    have hx : (x : E) ≠ 0 := by
      exact x.property
    simpa using norm_radialDirection (x : E) hx⟩

theorem contMDiff_radialProjection {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] :
    ContMDiff 𝓘(ℝ, E) (𝓡 n) ∞ (radialProjection (E := E)) := by
  exact contMDiff_radialDirection.codRestrict_sphere (fun x ↦ (radialProjection x).property)


theorem contMDiff_radialHeight (r : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x : (puncturedOpen (E := E)) ↦ radialHeight r (x : E)) := by
  intro x
  have hx : (x : E) ≠ 0 := by
    exact x.property
  exact (contDiffAt_radialHeight r (x : E) hx).contMDiffAt.comp x (contMDiff_subtype_val x)

theorem contMDiff_radialCollar {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] (r : ℝ) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : sphere (0 : E) 1 × ℝ ↦ radialCollar r p.1 p.2) := by
  exact (contMDiff_const.add contMDiff_snd).smul (contMDiff_coe_sphere.comp contMDiff_fst)


abbrev heightOpen (r : ℝ) : Opens ℝ := ⟨Ioi (-r), isOpen_Ioi⟩

def radialAmbientHomeomorph (r : ℝ) (u : sphere (0 : E) 1) :
    OpenPartialHomeomorph E (sphere (0 : E) 1 × Ioi (-r)) :=
  ((⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E).openPartialHomeomorphSubtypeCoe
    ⟨⟨u, by simpa using ne_zero_of_mem_unit_sphere u⟩⟩).symm.trans
      (radialHeightHomeomorph r).toOpenPartialHomeomorph

@[simp] theorem radialAmbientHomeomorph_source (r : ℝ) (u : sphere (0 : E) 1) :
    (radialAmbientHomeomorph r u).source = {0}ᶜ := by
  unfold radialAmbientHomeomorph
  rw [OpenPartialHomeomorph.trans_source]
  simp [puncturedOpen]

@[simp] theorem radialAmbientHomeomorph_target (r : ℝ) (u : sphere (0 : E) 1) :
    (radialAmbientHomeomorph r u).target = univ := by
  unfold radialAmbientHomeomorph
  rw [OpenPartialHomeomorph.trans_target]
  simp

@[simp] theorem radialAmbientHomeomorph_symm (r : ℝ) (u v : sphere (0 : E) 1) (t : Ioi (-r)) :
    (radialAmbientHomeomorph r u).symm (v, t) = radialCollar r v t := by
  change (((radialHeightHomeomorph r).symm (v, t)) : E) = _
  exact radialHeightHomeomorph_symm r v t

def radialProductChart {F : Type*} [TopologicalSpace F] (r : ℝ) (hr : 0 < r)
    (u : sphere (0 : E) 1) (c : OpenPartialHomeomorph (sphere (0 : E) 1) F) :
    OpenPartialHomeomorph E (F × ℝ) :=
  (radialAmbientHomeomorph r u).trans
    (c.prod ((heightOpen r).openPartialHomeomorphSubtypeCoe ⟨⟨0, by simpa [heightOpen] using hr⟩⟩))

-- Further statements to append after the product-chart constructor checks.
-- Boundary source/target and inverse formulas are actual functions.

theorem radialProductChart_target {F : Type*} [TopologicalSpace F] (r : ℝ) (hr : 0 < r)
    (u : sphere (0 : E) 1) (c : OpenPartialHomeomorph (sphere (0 : E) 1) F) :
    (radialProductChart r hr u c).target = c.target ×ˢ Ioi (-r) := by
  simp [radialProductChart, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.prod_target, heightOpen]

theorem radialProductChart_symm {F : Type*} [TopologicalSpace F] (r : ℝ) (hr : 0 < r)
    (u : sphere (0 : E) 1) (c : OpenPartialHomeomorph (sphere (0 : E) 1) F)
    (y : F) (t : ℝ) (ht : -r < t) :
    (radialProductChart r hr u c).symm (y, t) = radialCollar r (c.symm y) t := by
  let h := (heightOpen r).openPartialHomeomorphSubtypeCoe ⟨⟨0, by simpa [heightOpen] using hr⟩⟩
  have hi : ((h.symm t : heightOpen r) : ℝ) = t := by
    exact h.right_inv (by simpa [h, mfld_simps, heightOpen] using ht)
  change (radialAmbientHomeomorph r u).symm (c.symm y, h.symm t) = _
  rw [radialAmbientHomeomorph_symm]
  exact congrArg (radialCollar r (c.symm y)) hi

theorem radialProductChart_height {F : Type*} [TopologicalSpace F] (r : ℝ) (hr : 0 < r)
    (u : sphere (0 : E) 1) (c : OpenPartialHomeomorph (sphere (0 : E) 1) F)
    (x : E) (hx : x ∈ (radialProductChart r hr u c).source) :
    (radialProductChart r hr u c x).2 = radialHeight r x := by
  let e := radialProductChart r hr u c
  have ht := e.map_source hx
  rw [radialProductChart_target] at ht
  have hrange : 0 < r + (e x).2 := by have := ht.2; change -r < (e x).2 at this; linarith
  have hi := radialProductChart_symm r hr u c (e x).1 (e x).2 ht.2
  have hleft : e.symm (e x) = x := e.left_inv hx
  rw [← Prod.eta (e x)] at hleft
  rw [hi] at hleft
  calc
    (e x).2 = radialHeight r (radialCollar r (c.symm (e x).1) (e x).2) :=
      (radialHeight_radialCollar r (c.symm (e x).1) (e x).2 hrange).symm
    _ = radialHeight r x := congrArg (radialHeight r) hleft

theorem radialProductChart_domain {F : Type*} [TopologicalSpace F] (r : ℝ) (hr : 0 < r)
    (u : sphere (0 : E) 1) (c : OpenPartialHomeomorph (sphere (0 : E) 1) F)
    (x : E) (hx : x ∈ (radialProductChart r hr u c).source) :
    x ∈ (ball (0 : E) r)ᶜ ↔ 0 ≤ (radialProductChart r hr u c x).2 := by
  rw [radialProductChart_height r hr u c x hx, radialHeight_nonneg_iff]


-- Append in RadialBoundaryCharts namespace after radialProductChart checks.
-- Euclidean model identification puts height in coordinate zero.

def heightFirstEquiv (d : ℕ) :
    (EuclideanSpace ℝ (Fin d) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  (((ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin d)) ℝ).trans
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)))).trans
        (Fin.consEquivL ℝ (fun _ : Fin (d + 1) ↦ ℝ))).trans
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ ℝ)).symm

@[simp] theorem heightFirstEquiv_zero (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    heightFirstEquiv d (y, t) 0 = t := rfl

@[simp] theorem heightFirstEquiv_succ (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ)
    (j : Fin d) : heightFirstEquiv d (y, t) j.succ = y j := rfl

@[simp] theorem heightFirstEquiv_symm_snd (d : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ((heightFirstEquiv d).symm x).2 = x 0 := rfl

@[simp] theorem heightFirstEquiv_symm_fst (d : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1)))
    (j : Fin d) : ((heightFirstEquiv d).symm x).1 j = x j.succ := rfl

def radialEuclideanChart {d : ℕ} (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d))) :
    OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (d + 1))) :=
  (radialProductChart r hr u c).trans (heightFirstEquiv d).toHomeomorph.toOpenPartialHomeomorph

theorem radialEuclideanChart_source {d : ℕ} (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d))) :
    (radialEuclideanChart r hr u c).source = (radialProductChart r hr u c).source := by
  simp [radialEuclideanChart, mfld_simps]

theorem radialEuclideanChart_height {d : ℕ} (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (x : E) (hx : x ∈ (radialEuclideanChart r hr u c).source) :
    radialEuclideanChart r hr u c x 0 = radialHeight r x := by
  rw [radialEuclideanChart_source] at hx
  change heightFirstEquiv d (radialProductChart r hr u c x) 0 = _
  change (radialProductChart r hr u c x).2 = _
  exact radialProductChart_height r hr u c x hx

theorem radialEuclideanChart_domain {d : ℕ} (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (x : E) (hx : x ∈ (radialEuclideanChart r hr u c).source) :
    x ∈ (ball (0 : E) r)ᶜ ↔ 0 ≤ radialEuclideanChart r hr u c x 0 := by
  rw [radialEuclideanChart_height r hr u c x hx, radialHeight_nonneg_iff]

theorem radialAmbientHomeomorph_apply_subtype (r : ℝ) (u : sphere (0 : E) 1)
    (x : ({0}ᶜ : Set E)) :
    radialAmbientHomeomorph r u (x : E) = radialHeightHomeomorph r x := by
  let i := (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E).openPartialHomeomorphSubtypeCoe
    ⟨⟨u, by simpa using ne_zero_of_mem_unit_sphere u⟩⟩
  change radialHeightHomeomorph r (i.symm (x : E)) = radialHeightHomeomorph r x
  exact congrArg (radialHeightHomeomorph r) (i.left_inv (mem_univ x))

theorem radialProductChart_apply_subtype {F : Type*} [TopologicalSpace F]
    (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) F) (x : puncturedOpen (E := E)) :
    radialProductChart r hr u c (x : E) = (c (radialProjection x), radialHeight r (x : E)) := by
  change (c (radialAmbientHomeomorph r u (x : E)).1,
    ((radialAmbientHomeomorph r u (x : E)).2 : ℝ)) = _
  rw [radialAmbientHomeomorph_apply_subtype]
  have hf : (radialHeightHomeomorph r x).1 = radialProjection x :=
    Subtype.ext (radialHeightHomeomorph_fst r x)
  rw [hf, radialHeightHomeomorph_snd]

variable {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]

theorem contDiffOn_radialProductChart_symm
    (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : E) 1)) :
    ContDiffOn ℝ ∞ (radialProductChart r hr u c).symm
      (radialProductChart r hr u c).target := by
  intro p hp
  rw [radialProductChart_target] at hp
  have hc' := (contMDiffOn_symm_of_mem_maximalAtlas hc).contMDiffAt (c.open_target.mem_nhds hp.1)
  have hψ : ContDiffAt ℝ ∞ (fun y ↦ (c.symm y : E)) p.1 :=
    ((contMDiff_coe_sphere (n := d) (m := ∞) (c.symm p.1)).comp p.1 hc').contDiffAt
  have hcoll : ContDiffAt ℝ ∞
      (fun q : EuclideanSpace ℝ (Fin d) × ℝ ↦ radialCollar r (c.symm q.1) q.2) p :=
    (contDiffAt_const.add contDiffAt_snd).smul (hψ.comp p contDiffAt_fst)
  have hEq : (radialProductChart r hr u c).symm =ᶠ[nhds p]
      (fun q : EuclideanSpace ℝ (Fin d) × ℝ ↦ radialCollar r (c.symm q.1) q.2) := by
    filter_upwards [(isOpen_Ioi.preimage continuous_snd).mem_nhds hp.2] with q hq
    exact radialProductChart_symm r hr u c q.1 q.2 hq
  exact (hcoll.congr_of_eventuallyEq hEq).contDiffWithinAt

theorem contDiffOn_radialProductChart
    (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : E) 1)) :
    ContDiffOn ℝ ∞ (radialProductChart r hr u c) (radialProductChart r hr u c).source := by
  intro x hx
  have hx0 : x ≠ 0 := by
    have hx' : x ∈ (radialAmbientHomeomorph r u).source := hx.1
    simpa using hx'
  let z : puncturedOpen (E := E) := ⟨x, by simpa [puncturedOpen] using hx0⟩
  have hz : radialProjection z ∈ c.source := by
    have hx' : (radialAmbientHomeomorph r u x).1 ∈ c.source := hx.2.1
    rw [radialAmbientHomeomorph_apply_subtype r u (⟨x, by simpa using hx0⟩)] at hx'
    have hh : (radialHeightHomeomorph r (⟨x, by simpa using hx0⟩)).1 = radialProjection z := by
      apply Subtype.ext
      exact radialHeightHomeomorph_fst r z
    rwa [hh] at hx'
  have hcf := (contMDiffOn_of_mem_maximalAtlas hc).contMDiffAt (c.open_source.mem_nhds hz)
  have hfirst := hcf.comp z (contMDiff_radialProjection (E := E) (n := d) z)
  have hpair := hfirst.prodMk (contMDiff_radialHeight (E := E) r z)
  have hfun : (fun z : puncturedOpen (E := E) ↦ radialProductChart r hr u c (z : E)) =
      fun z : puncturedOpen (E := E) ↦ (c (radialProjection z), radialHeight r (z : E)) := by
    funext z
    exact radialProductChart_apply_subtype r hr u c z
  have he : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × ℝ) ∞
      (fun z : puncturedOpen (E := E) ↦ radialProductChart r hr u c (z : E)) z := by
    rw [hfun, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hpair
  exact (contMDiffAt_subtype_iff.mp he).contDiffAt.contDiffWithinAt


-- Append after the two product-chart smoothness theorems are available.

theorem radialProductChart_mem_source {F : Type*} [TopologicalSpace F]
    (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) F) (hu : u ∈ c.source) :
    r • (u : E) ∈ (radialProductChart r hr u c).source := by
  have hy : (c u, (0 : ℝ)) ∈ (radialProductChart r hr u c).target := by
    rw [radialProductChart_target]
    exact ⟨c.map_source hu, by simpa using hr⟩
  have hi := (radialProductChart r hr u c).map_target hy
  rw [radialProductChart_symm r hr u c (c u) 0 (by simpa using hr), c.left_inv hu] at hi
  simpa [radialCollar] using hi

theorem contDiffOn_radialEuclideanChart
    (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : E) 1)) :
    ContDiffOn ℝ ∞ (radialEuclideanChart r hr u c) (radialEuclideanChart r hr u c).source := by
  rw [radialEuclideanChart_source]
  exact (heightFirstEquiv d).contDiff.comp_contDiffOn (contDiffOn_radialProductChart r hr u c hc)

theorem contDiffOn_radialEuclideanChart_symm
    (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d)))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡 d) ∞ (sphere (0 : E) 1)) :
    ContDiffOn ℝ ∞ (radialEuclideanChart r hr u c).symm
      (radialEuclideanChart r hr u c).target := by
  intro z hz
  have hp : (heightFirstEquiv d).symm z ∈ (radialProductChart r hr u c).target := hz.2
  have hs := (contDiffOn_radialProductChart_symm r hr u c hc).contDiffAt
    ((radialProductChart r hr u c).open_target.mem_nhds hp)
  exact (hs.comp z (heightFirstEquiv d).symm.contDiff.contDiffAt).contDiffWithinAt

theorem radialEuclideanChart_mem_source
    (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1)
    (c : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin d))) (hu : u ∈ c.source) :
    r • (u : E) ∈ (radialEuclideanChart r hr u c).source := by
  rw [radialEuclideanChart_source]
  exact radialProductChart_mem_source r hr u c hu

end GaussBonnetChern.RadialBoundaryCharts


open Set Metric
namespace GaussBonnetChern.PuncturedManifold
variable {E M ι : Type*} [MetricSpace E] [ProperSpace E]
  [TopologicalSpace M] [T2Space M] [Fintype ι]

/-- A genuine open neighborhood removing all other closed coordinate balls. -/
def otherBallExterior (e : ι → OpenPartialHomeomorph M E) (c : ι → E) (r : ι → ℝ) (i : ι) : Set M :=
  (⋃ j : {j : ι // j ≠ i}, coordinateClosedBall (e j) (c j) (r j))ᶜ

theorem isOpen_otherBallExterior (e : ι → OpenPartialHomeomorph M E) (c : ι → E) (r : ι → ℝ)
    (hcover : ∀ i, closedBall (c i) (r i) ⊆ (e i).target) (i : ι) :
    IsOpen (otherBallExterior e c r i) :=
  (isClosed_iUnion_of_finite (fun j : {j : ι // j ≠ i} ↦
    (isCompact_coordinateClosedBall (e j) (c j) (r j) (hcover j)).isClosed)).isOpen_compl

theorem coordinateClosedBall_subset_otherBallExterior
    (e : ι → OpenPartialHomeomorph M E) (c : ι → E) (r : ι → ℝ)
    (hdis : Pairwise (fun i j ↦ Disjoint (coordinateClosedBall (e i) (c i) (r i))
      (coordinateClosedBall (e j) (c j) (r j)))) (i : ι) :
    coordinateClosedBall (e i) (c i) (r i) ⊆ otherBallExterior e c r i := by
  intro x hx hxU
  obtain ⟨j, hj⟩ := mem_iUnion.mp hxU
  exact Set.disjoint_left.mp (hdis (Ne.symm j.property)) hx hj

theorem puncturedDomain_local_iff
    (e : ι → OpenPartialHomeomorph M E) (c : ι → E) (r : ι → ℝ)
    (i : ι) (x : M) (hx : x ∈ otherBallExterior e c r i) :
    x ∈ puncturedDomain e c r ↔ x ∉ coordinateBall (e i) (c i) (r i) := by
  classical
  constructor
  · intro h hball
    exact h (mem_iUnion.mpr ⟨i, hball⟩)
  · intro h hball
    obtain ⟨j, hj⟩ := mem_iUnion.mp hball
    by_cases hji : j = i
    · subst j
      exact h hj
    · exact hx (mem_iUnion.mpr ⟨⟨j, hji⟩, ⟨hj.1, ball_subset_closedBall hj.2⟩⟩)

end GaussBonnetChern.PuncturedManifold
