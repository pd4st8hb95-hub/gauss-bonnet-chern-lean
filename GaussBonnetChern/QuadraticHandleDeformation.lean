import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! # Explicit deformations of the quadratic Morse handle

The two spaces may have dimension zero. The modified function is the actual
quadratic expression minus a radial cutoff. Its analytic cutoff properties
are explicit hypotheses of these model lemmas; they are supplied by the
separate smooth cutoff construction in the global Morse argument.
-/

noncomputable section

open Set Metric
open scoped Topology ContinuousMap

namespace GaussBonnetChern.QuadraticHandle

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def quadratic (x : U × V) : ℝ := ‖x.2‖ ^ 2 - ‖x.1‖ ^ 2

def radiusSquared (x : U × V) : ℝ := ‖x.1‖ ^ 2 + 2 * ‖x.2‖ ^ 2

def modified (μ : ℝ → ℝ) (x : U × V) : ℝ := quadratic x - μ (radiusSquared x)

/-- Contraction of just the positive coordinate. -/
def shrinkPositive (t : ℝ) (x : U × V) : U × V := (x.1, (1 - t) • x.2)

theorem continuous_shrinkPositive :
    Continuous (fun p : ℝ × (U × V) => shrinkPositive p.1 p.2) := by
  unfold shrinkPositive
  fun_prop

@[simp] theorem shrinkPositive_zero (x : U × V) : shrinkPositive 0 x = x := by
  simp [shrinkPositive]

@[simp] theorem shrinkPositive_one (x : U × V) : shrinkPositive 1 x = (x.1, 0) := by
  simp [shrinkPositive]

theorem norm_shrinkPositive_snd_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : U × V) :
    ‖(shrinkPositive t x).2‖ ≤ ‖x.2‖ := by
  simp only [shrinkPositive, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
  exact mul_le_of_le_one_left (norm_nonneg x.2) (by linarith [ht.1])

theorem quadratic_shrinkPositive_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : U × V) :
    quadratic (shrinkPositive t x) ≤ quadratic x := by
  have h := norm_shrinkPositive_snd_le ht x
  have hn := norm_nonneg (shrinkPositive t x).2
  unfold quadratic
  change ‖(shrinkPositive t x).2‖ ^ 2 - ‖x.1‖ ^ 2 ≤ ‖x.2‖ ^ 2 - ‖x.1‖ ^ 2
  nlinarith

theorem radiusSquared_nonneg (x : U × V) : 0 ≤ radiusSquared x := by
  unfold radiusSquared
  positivity

theorem radiusSquared_shrinkPositive_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : U × V) :
    radiusSquared (shrinkPositive t x) ≤ radiusSquared x := by
  have h := norm_shrinkPositive_snd_le ht x
  have hn := norm_nonneg (shrinkPositive t x).2
  unfold radiusSquared
  change ‖x.1‖ ^ 2 + 2 * ‖(shrinkPositive t x).2‖ ^ 2 ≤ ‖x.1‖ ^ 2 + 2 * ‖x.2‖ ^ 2
  nlinarith

theorem modified_shrinkPositive_le {μ : ℝ → ℝ} (hμ : AntitoneOn μ (Ici 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : U × V) :
    modified μ (shrinkPositive t x) ≤ modified μ x := by
  have hq := quadratic_shrinkPositive_le ht x
  have hm := hμ (radiusSquared_nonneg _) (radiusSquared_nonneg x)
    (radiusSquared_shrinkPositive_le ht x)
  unfold modified
  linarith

/-- Actual lower sublevel of the modified function in a product of closed balls. -/
def lowerBlock (μ : ℝ → ℝ) (ε r s : ℝ) : Set (U × V) :=
  {x | ‖x.1‖ ≤ r ∧ ‖x.2‖ ≤ s ∧ modified μ x ≤ -ε}

/-- Original lower sublevel as a genuine subset of the modified one. -/
def lowerAttaching (μ : ℝ → ℝ) (ε r s : ℝ) : Set (lowerBlock (U := U) (V := V) μ ε r s) :=
  {x | quadratic x.val ≤ -ε}

/-- The remaining negative annulus after contraction of the positive coordinate. -/
def negativeAnnulus (ε r : ℝ) : Set (closedBall (0 : U) r) := {u | ε ≤ ‖u.val‖ ^ 2}

theorem shrinkPositive_mem_lowerBlock {μ : ℝ → ℝ} (hμ : AntitoneOn μ (Ici 0))
    {ε r s t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : U × V}
    (hx : x ∈ lowerBlock μ ε r s) : shrinkPositive t x ∈ lowerBlock μ ε r s := by
  exact ⟨hx.1, (norm_shrinkPositive_snd_le ht x).trans hx.2.1,
    (modified_shrinkPositive_le hμ ht x).trans hx.2.2⟩

theorem zeroPositive_mem_lowerBlock {μ : ℝ → ℝ} {ε r s : ℝ} (hs : 0 ≤ s)
    (hcover : ∀ a ≥ 0, ε ≤ a + μ a) {u : U} (hu : ‖u‖ ≤ r) :
    (u, (0 : V)) ∈ lowerBlock μ ε r s := by
  refine ⟨hu, by simpa using hs, ?_⟩
  have h := hcover (‖u‖ ^ 2) (sq_nonneg _)
  simp only [modified, quadratic, radiusSquared, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero, zero_sub]
  linarith

theorem negative_projection_mem_annulus {μ : ℝ → ℝ} {ε r s : ℝ}
    (x : lowerBlock (U := U) (V := V) μ ε r s) (hx : x ∈ lowerAttaching μ ε r s) :
    ε ≤ ‖x.val.1‖ ^ 2 := by
  change ‖x.val.2‖ ^ 2 - ‖x.val.1‖ ^ 2 ≤ -ε at hx
  nlinarith [sq_nonneg ‖x.val.2‖]

/-- The negative projection of the actual modified sublevel. -/
def negativeProjection (μ : ℝ → ℝ) (ε r s : ℝ) :
    C(lowerBlock (U := U) (V := V) μ ε r s, closedBall (0 : U) r) where
  toFun x := ⟨x.val.1, by simpa using x.property.1⟩
  continuous_toFun := by fun_prop

/-- The zero section lands in the actual modified sublevel by the cutoff estimate. -/
def negativeSection (μ : ℝ → ℝ) (ε r s : ℝ) (hs : 0 ≤ s)
    (hcover : ∀ a ≥ 0, ε ≤ a + μ a) :
    C(closedBall (0 : U) r, lowerBlock (U := U) (V := V) μ ε r s) where
  toFun u := ⟨(u.val, 0), zeroPositive_mem_lowerBlock hs hcover
    (by simpa only [mem_closedBall, dist_zero_right] using u.property)⟩
  continuous_toFun := by fun_prop

/-- Explicit strong deformation, simultaneously preserving the original lower sublevel. -/
def positiveContraction (μ : ℝ → ℝ) (ε r s : ℝ) (hμ : AntitoneOn μ (Ici 0))
    (hs : 0 ≤ s) (hcover : ∀ a ≥ 0, ε ≤ a + μ a) :
    ContinuousMap.Homotopy (ContinuousMap.id (lowerBlock (U := U) (V := V) μ ε r s))
      ((negativeSection μ ε r s hs hcover).comp (negativeProjection μ ε r s)) where
  toFun p := ⟨shrinkPositive p.1.val p.2.val, shrinkPositive_mem_lowerBlock hμ p.1.property p.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun p : unitInterval × lowerBlock (U := U) (V := V) μ ε r s =>
        (p.1.val, p.2.val)) := by fun_prop
    exact continuous_shrinkPositive.comp hc
  map_zero_left x := by ext <;> simp [shrinkPositive]
  map_one_left x := by ext <;> simp [shrinkPositive, negativeSection, negativeProjection]

theorem positiveContraction_preserves_attaching (μ : ℝ → ℝ) (ε r s : ℝ)
    (hμ : AntitoneOn μ (Ici 0)) (hs : 0 ≤ s) (hcover : ∀ a ≥ 0, ε ≤ a + μ a)
    (t : unitInterval) : MapsTo (fun x => positiveContraction μ ε r s hμ hs hcover (t, x))
      (lowerAttaching (U := U) (V := V) μ ε r s) (lowerAttaching μ ε r s) := by
  intro x hx
  exact (quadratic_shrinkPositive_le t.property x.val).trans hx

/-- The actual modified lower block retracts onto the entire negative disk. -/
def lowerBlockHomotopyEquivDisk (μ : ℝ → ℝ) (ε r s : ℝ)
    (hμ : AntitoneOn μ (Ici 0)) (hs : 0 ≤ s) (hcover : ∀ a ≥ 0, ε ≤ a + μ a) :
    lowerBlock (U := U) (V := V) μ ε r s ≃ₕ closedBall (0 : U) r where
  toFun := negativeProjection μ ε r s
  invFun := negativeSection μ ε r s hs hcover
  left_inv := ⟨(positiveContraction μ ε r s hμ hs hcover).symm⟩
  right_inv := by
    have heq : (negativeProjection (U := U) (V := V) μ ε r s).comp
        (negativeSection μ ε r s hs hcover) = ContinuousMap.id (closedBall (0 : U) r) := by
      ext x
      rfl
    rw [heq]

def attachingProjection (μ : ℝ → ℝ) (ε r s : ℝ) :
    C(lowerAttaching (U := U) (V := V) μ ε r s, negativeAnnulus (U := U) ε r) where
  toFun x := ⟨negativeProjection μ ε r s x.val, negative_projection_mem_annulus x.val x.property⟩
  continuous_toFun := by fun_prop

def attachingSection (μ : ℝ → ℝ) (ε r s : ℝ) (hs : 0 ≤ s)
    (hcover : ∀ a ≥ 0, ε ≤ a + μ a) :
    C(negativeAnnulus (U := U) ε r, lowerAttaching (U := U) (V := V) μ ε r s) where
  toFun x := ⟨negativeSection μ ε r s hs hcover x.val, by
    change quadratic (x.val.val, (0 : V)) ≤ -ε
    simp only [quadratic, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_sub]
    exact neg_le_neg x.property⟩
  continuous_toFun := by fun_prop

def attachingContraction (μ : ℝ → ℝ) (ε r s : ℝ)
    (hμ : AntitoneOn μ (Ici 0)) (hs : 0 ≤ s) (hcover : ∀ a ≥ 0, ε ≤ a + μ a) :
    ContinuousMap.Homotopy (ContinuousMap.id (lowerAttaching (U := U) (V := V) μ ε r s))
      ((attachingSection μ ε r s hs hcover).comp (attachingProjection μ ε r s)) where
  toFun p := ⟨positiveContraction μ ε r s hμ hs hcover (p.1, p.2.val),
    positiveContraction_preserves_attaching μ ε r s hμ hs hcover p.1 p.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (positiveContraction μ ε r s hμ hs hcover).continuous.comp (by fun_prop)
  map_zero_left x := by
    apply Subtype.ext
    exact (positiveContraction μ ε r s hμ hs hcover).map_zero_left x.val
  map_one_left x := by
    apply Subtype.ext
    exact (positiveContraction μ ε r s hμ hs hcover).map_one_left x.val

/-- Restriction of the same negative projection is a genuine equivalence from
the original lower part to the negative annulus. -/
def lowerAttachingHomotopyEquivAnnulus (μ : ℝ → ℝ) (ε r s : ℝ)
    (hμ : AntitoneOn μ (Ici 0)) (hs : 0 ≤ s) (hcover : ∀ a ≥ 0, ε ≤ a + μ a) :
    lowerAttaching (U := U) (V := V) μ ε r s ≃ₕ negativeAnnulus (U := U) ε r where
  toFun := attachingProjection μ ε r s
  invFun := attachingSection μ ε r s hs hcover
  left_inv := ⟨(attachingContraction μ ε r s hμ hs hcover).symm⟩
  right_inv := by
    have heq : (attachingProjection (U := U) (V := V) μ ε r s).comp
        (attachingSection μ ε r s hs hcover) = ContinuousMap.id (negativeAnnulus (U := U) ε r) := by
      ext x
      rfl
    rw [heq]

section Radial

/-- Radial clipping followed by rescaling to the unit disk. -/
def radialRetraction (a : ℝ) (u : U) : U := (max a ‖u‖)⁻¹ • u

theorem continuous_radialRetraction {a : ℝ} (ha : 0 < a) :
    Continuous (radialRetraction (U := U) a) := by
  unfold radialRetraction
  exact ((continuous_const.max continuous_norm).inv₀
    (fun u => ne_of_gt (lt_of_lt_of_le ha (le_max_left _ _)))).smul continuous_id

theorem norm_radialRetraction {a : ℝ} (ha : 0 < a) (u : U) :
    ‖radialRetraction a u‖ = ‖u‖ / max a ‖u‖ := by
  rw [radialRetraction, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (le_trans ha.le (le_max_left _ _))), div_eq_inv_mul]

theorem norm_radialRetraction_le_one {a : ℝ} (ha : 0 < a) (u : U) :
    ‖radialRetraction a u‖ ≤ 1 := by
  rw [norm_radialRetraction ha, div_le_one (lt_of_lt_of_le ha (le_max_left _ _))]
  exact le_max_right _ _

theorem norm_radialRetraction_eq_one {a : ℝ} (ha : 0 < a) {u : U} (hu : a ≤ ‖u‖) :
    ‖radialRetraction a u‖ = 1 := by
  rw [norm_radialRetraction ha, max_eq_right hu, div_self (ne_of_gt (ha.trans_le hu))]

theorem radialRetraction_smul {a : ℝ} (ha : 0 < a) {u : U} (hu : ‖u‖ ≤ 1) :
    radialRetraction a (a • u) = u := by
  have hnorm : ‖a • u‖ ≤ a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    nlinarith
  rw [radialRetraction, max_eq_left hnorm, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]

def radialContraction (a t : ℝ) (u : U) : U :=
  (1 - t) • u + t • (a • radialRetraction a u)

theorem continuous_radialContraction {a : ℝ} (ha : 0 < a) :
    Continuous (fun p : ℝ × U => radialContraction a p.1 p.2) := by
  unfold radialContraction
  have hret : Continuous (fun p : ℝ × U => radialRetraction a p.2) :=
    (continuous_radialRetraction (U := U) ha).comp continuous_snd
  exact ((continuous_const.sub continuous_fst).smul continuous_snd).add
    (continuous_fst.smul (continuous_const.smul hret))

@[simp] theorem radialContraction_zero (a : ℝ) (u : U) : radialContraction a 0 u = u := by
  simp [radialContraction]

@[simp] theorem radialContraction_one (a : ℝ) (u : U) :
    radialContraction a 1 u = a • radialRetraction a u := by simp [radialContraction]

theorem norm_radialContraction {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1) (u : U) :
    ‖radialContraction a t u‖ = (1 - t) * ‖u‖ + t * a * ‖radialRetraction a u‖ := by
  have hm : 0 ≤ (max a ‖u‖)⁻¹ := inv_nonneg.mpr (ha.le.trans (le_max_left _ _))
  have hc : 0 ≤ 1 - t + t * a * (max a ‖u‖)⁻¹ := by
    exact add_nonneg (sub_nonneg.mpr ht.2) (mul_nonneg (mul_nonneg ht.1 ha.le) hm)
  rw [radialContraction, radialRetraction, smul_smul, smul_smul, ← add_smul,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hm]
  ring

theorem norm_radialContraction_le {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1) (u : U) :
    ‖radialContraction a t u‖ ≤ ‖u‖ := by
  have hnorm : a * ‖radialRetraction a u‖ ≤ ‖u‖ := by
    rw [norm_radialRetraction ha]
    have hm := lt_of_lt_of_le ha (le_max_left a ‖u‖)
    rw [← mul_div_assoc, div_le_iff₀ hm]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (le_max_left a ‖u‖) (norm_nonneg u)
  rw [norm_radialContraction ha ht]
  nlinarith [ht.1]

theorem norm_radialContraction_ge {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1)
    {u : U} (hu : a ≤ ‖u‖) : a ≤ ‖radialContraction a t u‖ := by
  rw [norm_radialContraction ha ht, norm_radialRetraction_eq_one ha hu]
  nlinarith [ht.1, ht.2]

def radialDiskProjection (a r : ℝ) (ha : 0 < a) :
    C(closedBall (0 : U) r, closedBall (0 : U) 1) where
  toFun u := ⟨radialRetraction a u.val, by
    simpa only [mem_closedBall, dist_zero_right] using norm_radialRetraction_le_one ha u.val⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_radialRetraction ha).comp continuous_subtype_val

def radialDiskSection (a r : ℝ) (ha : 0 < a) (har : a ≤ r) :
    C(closedBall (0 : U) 1, closedBall (0 : U) r) where
  toFun u := ⟨a • u.val, by
    have hu : ‖u.val‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using u.property
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    nlinarith⟩
  continuous_toFun := by fun_prop

def radialDiskHomotopy (a r : ℝ) (ha : 0 < a) (har : a ≤ r) :
    ContinuousMap.Homotopy (ContinuousMap.id (closedBall (0 : U) r))
      ((radialDiskSection a r ha har).comp (radialDiskProjection a r ha)) where
  toFun p := ⟨radialContraction a p.1.val p.2.val, by
    have hp : ‖p.2.val‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using p.2.property
    simpa only [mem_closedBall, dist_zero_right] using
      (norm_radialContraction_le ha p.1.property p.2.val).trans hp⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun p : unitInterval × closedBall (0 : U) r => (p.1.val, p.2.val)) := by
      fun_prop
    exact (continuous_radialContraction ha).comp hc
  map_zero_left x := by ext; simp [radialContraction]
  map_one_left x := by ext; simp [radialContraction, radialDiskSection, radialDiskProjection]

def radialDiskHomotopyEquiv (a r : ℝ) (ha : 0 < a) (har : a ≤ r) :
    closedBall (0 : U) r ≃ₕ closedBall (0 : U) 1 where
  toFun := radialDiskProjection a r ha
  invFun := radialDiskSection a r ha har
  left_inv := ⟨(radialDiskHomotopy a r ha har).symm⟩
  right_inv := by
    have heq : (radialDiskProjection (U := U) a r ha).comp (radialDiskSection a r ha har) =
        ContinuousMap.id (closedBall (0 : U) 1) := by
      ext u
      exact radialRetraction_smul ha (by simpa only [mem_closedBall, dist_zero_right] using u.property)
    rw [heq]

theorem annulus_norm_ge {a r : ℝ} (ha : 0 < a)
    (u : negativeAnnulus (U := U) (a ^ 2) r) : a ≤ ‖u.val.val‖ := by
  have hu := u.property
  change a ^ 2 ≤ ‖u.val.val‖ ^ 2 at hu
  nlinarith [norm_nonneg u.val.val]

def radialSphereProjection (a r : ℝ) (ha : 0 < a) :
    C(negativeAnnulus (U := U) (a ^ 2) r, sphere (0 : U) 1) where
  toFun u := ⟨radialRetraction a u.val.val, by
    simpa only [mem_sphere, dist_zero_right] using norm_radialRetraction_eq_one ha (annulus_norm_ge ha u)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_radialRetraction ha).comp (by fun_prop)

def radialSphereSection (a r : ℝ) (ha : 0 < a) (har : a ≤ r) :
    C(sphere (0 : U) 1, negativeAnnulus (U := U) (a ^ 2) r) where
  toFun u := ⟨radialDiskSection a r ha har ⟨u.val, sphere_subset_closedBall u.property⟩, by
    have hu : ‖u.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using u.property
    change a ^ 2 ≤ ‖a • u.val‖ ^ 2
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hu, mul_one, le_refl]⟩
  continuous_toFun := by fun_prop

def radialAnnulusHomotopy (a r : ℝ) (ha : 0 < a) (har : a ≤ r) :
    ContinuousMap.Homotopy (ContinuousMap.id (negativeAnnulus (U := U) (a ^ 2) r))
      ((radialSphereSection a r ha har).comp (radialSphereProjection a r ha)) where
  toFun p := ⟨radialDiskHomotopy a r ha har (p.1, p.2.val), by
    have hh := norm_radialContraction_ge ha p.1.property (annulus_norm_ge ha p.2)
    change a ^ 2 ≤ ‖radialContraction a p.1.val p.2.val.val‖ ^ 2
    nlinarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun p : unitInterval × negativeAnnulus (U := U) (a ^ 2) r =>
        (p.1, p.2.val)) := by fun_prop
    exact (radialDiskHomotopy a r ha har).continuous.comp hc
  map_zero_left x := by
    apply Subtype.ext
    exact (radialDiskHomotopy a r ha har).map_zero_left x.val
  map_one_left x := by
    apply Subtype.ext
    exact (radialDiskHomotopy a r ha har).map_one_left x.val

/-- On the attaching part, the very same radial map is a homotopy equivalence
with the actual unit sphere. This includes the empty sphere in dimension zero. -/
def radialAnnulusHomotopyEquivSphere (a r : ℝ) (ha : 0 < a) (har : a ≤ r) :
    negativeAnnulus (U := U) (a ^ 2) r ≃ₕ sphere (0 : U) 1 where
  toFun := radialSphereProjection a r ha
  invFun := radialSphereSection a r ha har
  left_inv := ⟨(radialAnnulusHomotopy a r ha har).symm⟩
  right_inv := by
    have heq : (radialSphereProjection (U := U) a r ha).comp (radialSphereSection a r ha har) =
        ContinuousMap.id (sphere (0 : U) 1) := by
      ext u
      apply radialRetraction_smul ha
      have hu : ‖u.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using u.property
      exact hu.le
    rw [heq]

end Radial

/-- Full explicit equivalence of the modified lower block with the negative unit disk. -/
def lowerBlockHomotopyEquivUnitDisk (μ : ℝ → ℝ) (a r s : ℝ)
    (ha : 0 < a) (har : a ≤ r) (hμ : AntitoneOn μ (Ici 0)) (hs : 0 ≤ s)
    (hcover : ∀ b ≥ 0, a ^ 2 ≤ b + μ b) :
    lowerBlock (U := U) (V := V) μ (a ^ 2) r s ≃ₕ closedBall (0 : U) 1 :=
  (lowerBlockHomotopyEquivDisk μ (a ^ 2) r s hμ hs hcover).trans
    (radialDiskHomotopyEquiv a r ha har)

/-- The same equivalence restricts on the original lower part to a sphere equivalence. -/
def lowerAttachingHomotopyEquivUnitSphere (μ : ℝ → ℝ) (a r s : ℝ)
    (ha : 0 < a) (har : a ≤ r) (hμ : AntitoneOn μ (Ici 0)) (hs : 0 ≤ s)
    (hcover : ∀ b ≥ 0, a ^ 2 ≤ b + μ b) :
    lowerAttaching (U := U) (V := V) μ (a ^ 2) r s ≃ₕ sphere (0 : U) 1 :=
  (lowerAttachingHomotopyEquivAnnulus μ (a ^ 2) r s hμ hs hcover).trans
    (radialAnnulusHomotopyEquivSphere a r ha har)

@[simp] theorem lowerBlockHomotopyEquivUnitDisk_apply (μ : ℝ → ℝ) (a r s : ℝ)
    (ha : 0 < a) (har : a ≤ r) (hμ : AntitoneOn μ (Ici 0)) (hs : 0 ≤ s)
    (hcover : ∀ b ≥ 0, a ^ 2 ≤ b + μ b)
    (x : lowerBlock (U := U) (V := V) μ (a ^ 2) r s) :
    ((lowerBlockHomotopyEquivUnitDisk μ a r s ha har hμ hs hcover).toFun x).val =
      radialRetraction a x.val.1 := rfl

theorem lowerBlockHomotopyEquivUnitDisk_boundary (μ : ℝ → ℝ) (a r s : ℝ)
    (ha : 0 < a) (har : a ≤ r) (hμ : AntitoneOn μ (Ici 0)) (hs : 0 ≤ s)
    (hcover : ∀ b ≥ 0, a ^ 2 ≤ b + μ b)
    (x : lowerBlock (U := U) (V := V) μ (a ^ 2) r s)
    (hx : x ∈ lowerAttaching μ (a ^ 2) r s) :
    ((lowerBlockHomotopyEquivUnitDisk μ a r s ha har hμ hs hcover).toFun x).val ∈
      sphere (0 : U) 1 := by
  rw [lowerBlockHomotopyEquivUnitDisk_apply]
  have hu : a ≤ ‖x.val.1‖ := by
    have h := negative_projection_mem_annulus x hx
    nlinarith [norm_nonneg x.val.1]
  simpa only [mem_sphere, dist_zero_right] using norm_radialRetraction_eq_one ha hu

/-- Equality of the actual ambient and attaching forward maps. This is the
compatibility needed for the relative singular-homology comparison. -/
theorem lowerBlockHomotopyEquivUnitDisk_restrict (μ : ℝ → ℝ) (a r s : ℝ)
    (ha : 0 < a) (har : a ≤ r) (hμ : AntitoneOn μ (Ici 0)) (hs : 0 ≤ s)
    (hcover : ∀ b ≥ 0, a ^ 2 ≤ b + μ b)
    (x : lowerAttaching (U := U) (V := V) μ (a ^ 2) r s) :
    ((lowerAttachingHomotopyEquivUnitSphere μ a r s ha har hμ hs hcover).toFun x).val =
      ((lowerBlockHomotopyEquivUnitDisk μ a r s ha har hμ hs hcover).toFun x.val).val := rfl

theorem original_lower_mem_modified {μ : ℝ → ℝ}
    (hμ : ∀ b ≥ 0, 0 ≤ μ b) {ε r s : ℝ} {x : U × V}
    (hu : ‖x.1‖ ≤ r) (hv : ‖x.2‖ ≤ s) (hx : quadratic x ≤ -ε) :
    x ∈ lowerBlock μ ε r s := by
  refine ⟨hu, hv, ?_⟩
  have hm := hμ (radiusSquared x) (radiusSquared_nonneg x)
  unfold modified
  linarith

end GaussBonnetChern.QuadraticHandle
