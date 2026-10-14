import GaussBonnetChern.ChernProductIdentities
import GaussBonnetChern.LocalExteriorDerivative

/-! # Exterior differentiation of the genuine ordered Chern products

The replacement terms preserve the order of the existing wedge product and
increase exactly one factor's degree. One-form products have the usual signed
Leibniz sum; two-form products have positive signs. Both global smoothness and
local chart-germ formulations are provided for the geometric construction.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

/-- Replace one factor of the ordered one-form product by an actual two-form.
The recursion preserves the order of all other factors. -/
def oneFormProductReplacement : (r : ℕ) →
    (Fin r → Form 𝓘(ℝ, E) P 1) → (Fin r → Form 𝓘(ℝ, E) P 2) →
    Fin r → Form 𝓘(ℝ, E) P (r+1)
  | 0, _, _, i => Fin.elim0 i
  | r+1, θ, δ, i => Fin.lastCases
      (wedge (k := r) (l := 2) (oneFormProduct r (fun j ↦ θ j.castSucc)) (δ (Fin.last r)))
      (fun j ↦ wedge (k := r+1) (l := 1) (oneFormProductReplacement r (fun j ↦ θ j.castSucc)
        (fun j ↦ δ j.castSucc) j) (θ (Fin.last r))) i

@[simp] theorem oneFormProductReplacement_last (r : ℕ)
    (θ : Fin (r+1) → Form 𝓘(ℝ, E) P 1) (δ : Fin (r+1) → Form 𝓘(ℝ, E) P 2) :
    oneFormProductReplacement (r+1) θ δ (Fin.last r) =
      wedge (oneFormProduct r (fun j ↦ θ j.castSucc)) (δ (Fin.last r)) := by
  simp [oneFormProductReplacement]

@[simp] theorem oneFormProductReplacement_castSucc (r : ℕ)
    (θ : Fin (r+1) → Form 𝓘(ℝ, E) P 1) (δ : Fin (r+1) → Form 𝓘(ℝ, E) P 2)
    (i : Fin r) :
    oneFormProductReplacement (r+1) θ δ i.castSucc =
      wedge (oneFormProductReplacement r (fun j ↦ θ j.castSucc)
        (fun j ↦ δ j.castSucc) i) (θ (Fin.last r)) := by
  simp [oneFormProductReplacement]

variable [IsManifold 𝓘(ℝ, E) ∞ P]

private theorem exteriorDerivative_product_unit :
    exteriorDerivative (ofFunction (I := 𝓘(ℝ, E)) (M := P) (fun _ ↦ (1 : ℝ))) = 0 := by
  funext x
  ext v
  change extDeriv (chartRepresentation (chartAt E x) (ofFunction (fun _ : P ↦ (1 : ℝ))))
    (chartAt E x x) (chartTangentMap (chartAt E x) x ∘ v) = 0
  rw [chartRepresentation_ofFunction, extDeriv_constOfIsEmpty]
  change (fderiv ℝ (fun _ : E ↦ (1 : ℝ)) (chartAt E x x))
    (chartTangentMap (chartAt E x) x (v 0)) = 0
  rw [fderiv_const_apply]
  rfl

/-- The exterior derivative of an arbitrary ordered product of smooth
one-forms is the signed sum replacing exactly one factor by its derivative. -/
theorem exteriorDerivative_oneFormProduct (r : ℕ)
    (θ : Fin r → Form 𝓘(ℝ, E) P 1) (hθ : ∀ i, IsSmooth (θ i)) :
    exteriorDerivative (oneFormProduct r θ) =
      ∑ i : Fin r, (-1 : ℝ) ^ i.val •
        oneFormProductReplacement r θ (fun i ↦ exteriorDerivative (θ i)) i := by
  induction r with
  | zero =>
    rw [oneFormProduct, exteriorDerivative_product_unit]
    simp
  | succ r ih =>
    have hs := isSmooth_oneFormProduct r (fun i ↦ θ i.castSucc) (fun i ↦ hθ i.castSucc)
    rw [oneFormProduct, exteriorDerivative_wedge _ _ hs (hθ (Fin.last r))]
    change wedge (exteriorDerivative (oneFormProduct r (fun i ↦ θ i.castSucc)))
      (θ (Fin.last r)) + (-1 : ℝ)^r •
        wedge (oneFormProduct r (fun i ↦ θ i.castSucc)) (exteriorDerivative (θ (Fin.last r))) = _
    rw [ih _ (fun i ↦ hθ i.castSucc), Fin.sum_univ_castSucc]
    simp only [oneFormProductReplacement_castSucc, oneFormProductReplacement_last,
      Fin.val_castSucc, Fin.val_last]
    congr 1
    change ((wedgeLinear (r+1) 1).flip (θ (Fin.last r)))
        (∑ i : Fin r, (-1 : ℝ)^i.val •
          oneFormProductReplacement r (fun i ↦ θ i.castSucc)
            (fun i ↦ exteriorDerivative (θ i.castSucc)) i) = _
    rw [map_sum]
    simp_rw [map_smul]
    rfl

/-- Replace one factor of the ordered two-form product by an actual three-form. -/
def twoFormProductReplacement : (r : ℕ) →
    (Fin r → Form 𝓘(ℝ, E) P 2) → (Fin r → Form 𝓘(ℝ, E) P 3) →
    Fin r → Form 𝓘(ℝ, E) P (2*r+1)
  | 0, _, _, i => Fin.elim0 i
  | r+1, B, δ, i => degreeCastForm (show 2*r+3 = 2*(r+1)+1 by omega)
      (Fin.lastCases
        (wedge (k := 2*r) (l := 3) (twoFormProduct r (fun j ↦ B j.castSucc)) (δ (Fin.last r)))
        (fun j ↦ wedge (k := 2*r+1) (l := 2) (twoFormProductReplacement r (fun j ↦ B j.castSucc)
          (fun j ↦ δ j.castSucc) j) (B (Fin.last r))) i)

@[simp] theorem twoFormProductReplacement_last (r : ℕ)
    (B : Fin (r+1) → Form 𝓘(ℝ, E) P 2) (δ : Fin (r+1) → Form 𝓘(ℝ, E) P 3) :
    twoFormProductReplacement (r+1) B δ (Fin.last r) =
      degreeCastForm (show 2*r+3 = 2*(r+1)+1 by omega)
        (wedge (twoFormProduct r (fun j ↦ B j.castSucc)) (δ (Fin.last r))) := by
  simp [twoFormProductReplacement]

@[simp] theorem twoFormProductReplacement_castSucc (r : ℕ)
    (B : Fin (r+1) → Form 𝓘(ℝ, E) P 2) (δ : Fin (r+1) → Form 𝓘(ℝ, E) P 3)
    (i : Fin r) :
    twoFormProductReplacement (r+1) B δ i.castSucc =
      degreeCastForm (show 2*r+3 = 2*(r+1)+1 by omega)
        (wedge (k := 2*r+1) (l := 2) (twoFormProductReplacement r (fun j ↦ B j.castSucc)
          (fun j ↦ δ j.castSucc) i) (B (Fin.last r))) := by
  simp [twoFormProductReplacement]

/-- All derivative summands of an ordered product of smooth two-forms have
positive sign, since every preceding factor has even degree. -/
theorem exteriorDerivative_twoFormProduct (r : ℕ)
    (B : Fin r → Form 𝓘(ℝ, E) P 2) (hB : ∀ i, IsSmooth (B i)) :
    exteriorDerivative (twoFormProduct r B) =
      ∑ i : Fin r, twoFormProductReplacement r B (fun i ↦ exteriorDerivative (B i)) i := by
  induction r with
  | zero =>
    rw [twoFormProduct, exteriorDerivative_product_unit]
    simp
  | succ r ih =>
    have hs := isSmooth_twoFormProduct r (fun i ↦ B i.castSucc) (fun i ↦ hB i.castSucc)
    rw [twoFormProduct, exteriorDerivative_degreeCast,
      exteriorDerivative_wedge _ _ hs (hB (Fin.last r))]
    have hsign : (-1 : ℝ)^(2*r) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
    rw [hsign, one_smul]
    change formCastLinear (show 2*r+3 = 2*(r+1)+1 by omega)
      (wedge (exteriorDerivative (twoFormProduct r (fun i ↦ B i.castSucc))) (B (Fin.last r)) +
        wedge (twoFormProduct r (fun i ↦ B i.castSucc)) (exteriorDerivative (B (Fin.last r)))) = _
    rw [map_add, ih _ (fun i ↦ hB i.castSucc), Fin.sum_univ_castSucc]
    simp only [twoFormProductReplacement_castSucc, twoFormProductReplacement_last,
      formCastLinear_apply]
    congr 1
    change ((formCastLinear (show 2*r+3 = 2*(r+1)+1 by omega)).comp
      ((wedgeLinear (2*r+1) 2).flip (B (Fin.last r))))
      (∑ i : Fin r, twoFormProductReplacement r (fun j ↦ B j.castSucc)
        (fun j ↦ exteriorDerivative (B j.castSucc)) i) = _
    rw [map_sum]
    rfl

end GaussBonnetChern.Chern


noncomputable section
open scoped Manifold ContDiff BigOperators

namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  [IsManifold 𝓘(ℝ, E) ∞ P]

theorem contDiffAt_chartRepresentation_oneFormProduct (r : ℕ)
    (e : OpenPartialHomeomorph P E) (θ : Fin r → Form 𝓘(ℝ, E) P 1) (y : E)
    (hθ : ∀ i, ContDiffAt ℝ ∞ (chartRepresentation e (θ i)) y) :
    ContDiffAt ℝ ∞ (chartRepresentation e (oneFormProduct r θ)) y := by
  induction r with
  | zero =>
    rw [oneFormProduct, chartRepresentation_ofFunction]
    exact contDiffAt_const
  | succ r ih =>
    have heq : chartRepresentation e (oneFormProduct (r+1) θ) =
        (fun z ↦ wedgeFiber (chartRepresentation e (oneFormProduct r (fun i ↦ θ i.castSucc)) z)
          (chartRepresentation e (θ (Fin.last r)) z)) := by
      funext z
      exact chartRepresentation_wedge e _ _ z
    rw [heq]
    exact contDiffAt_wedgeFiber (ih _ (fun i ↦ hθ i.castSucc)) (hθ (Fin.last r))

theorem contDiffAt_chartRepresentation_twoFormProduct (r : ℕ)
    (e : OpenPartialHomeomorph P E) (B : Fin r → Form 𝓘(ℝ, E) P 2) (y : E)
    (hB : ∀ i, ContDiffAt ℝ ∞ (chartRepresentation e (B i)) y) :
    ContDiffAt ℝ ∞ (chartRepresentation e (twoFormProduct r B)) y := by
  induction r with
  | zero =>
    rw [twoFormProduct, chartRepresentation_ofFunction]
    exact contDiffAt_const
  | succ r ih =>
    rw [twoFormProduct, chartRepresentation_degreeCast]
    have heq : chartRepresentation e
        (wedge (twoFormProduct r (fun i ↦ B i.castSucc)) (B (Fin.last r))) =
        (fun z ↦ wedgeFiber (chartRepresentation e (twoFormProduct r (fun i ↦ B i.castSucc)) z)
          (chartRepresentation e (B (Fin.last r)) z)) := by
      funext z
      exact chartRepresentation_wedge e _ _ z
    rw [heq]
    exact (degreeCastCLM (show 2*r+2 = 2*(r+1) by omega)).contDiff.contDiffAt.comp y
      (contDiffAt_wedgeFiber (ih _ (fun i ↦ hB i.castSucc)) (hB (Fin.last r)))

theorem chartDerivative_oneFormProduct (r : ℕ)
    (e : OpenPartialHomeomorph P E) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ P)
    (θ : Fin r → Form 𝓘(ℝ, E) P 1) (x : P) (hx : x ∈ e.source)
    (hθ : ∀ i, ContDiffAt ℝ ∞ (chartRepresentation e (θ i)) (e x)) :
    chartDerivative e (oneFormProduct r θ) x =
      ∑ i : Fin r, (-1 : ℝ)^i.val •
        oneFormProductReplacement r θ (fun i y ↦ chartDerivative e (θ i) y) i x := by
  induction r with
  | zero =>
    rw [oneFormProduct]
    simp only [Fin.sum_univ_zero]
    ext v
    change extDeriv (chartRepresentation e (ofFunction (fun _ : P ↦ (1 : ℝ))))
      (e x) (chartTangentMap e x ∘ v) = 0
    rw [chartRepresentation_ofFunction, extDeriv_constOfIsEmpty]
    change (fderiv ℝ (fun _ : E ↦ (1 : ℝ)) (e x)) (chartTangentMap e x (v 0)) = 0
    rw [fderiv_const_apply]
    rfl
  | succ r ih =>
    rw [oneFormProduct, chartDerivative_wedge e he _ _ x hx
      ((contDiffAt_chartRepresentation_oneFormProduct r e (fun i ↦ θ i.castSucc) (e x)
        (fun i ↦ hθ i.castSucc)).differentiableAt (by simp))
      ((hθ (Fin.last r)).differentiableAt (by simp))]
    change wedgeFiber (chartDerivative e (oneFormProduct r (fun i ↦ θ i.castSucc)) x)
      (θ (Fin.last r) x) + (-1 : ℝ)^r •
        wedgeFiber (oneFormProduct r (fun i ↦ θ i.castSucc) x)
          (chartDerivative e (θ (Fin.last r)) x) = _
    rw [ih _ (fun i ↦ hθ i.castSucc), Fin.sum_univ_castSucc]
    simp only [oneFormProductReplacement_castSucc, oneFormProductReplacement_last,
      Fin.val_castSucc, Fin.val_last, wedge]
    congr 1
    ext v
    have h := congrArg (fun z : Form 𝓘(ℝ, E) P (r+1+1) ↦ z x v)
      (map_sum ((wedgeLinear (r+1) 1).flip (θ (Fin.last r)))
        (fun i : Fin r ↦ (-1 : ℝ)^i.val •
          oneFormProductReplacement r (fun j ↦ θ j.castSucc)
            (fun j y ↦ chartDerivative e (θ j.castSucc) y) i) Finset.univ)
    simp only [map_smul, LinearMap.flip_apply, wedgeLinear_apply, wedge,
      Finset.sum_apply, Pi.smul_apply, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.smul_apply] at h
    simpa only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply] using h

theorem chartDerivative_twoFormProduct (r : ℕ)
    (e : OpenPartialHomeomorph P E) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ P)
    (B : Fin r → Form 𝓘(ℝ, E) P 2) (x : P) (hx : x ∈ e.source)
    (hB : ∀ i, ContDiffAt ℝ ∞ (chartRepresentation e (B i)) (e x)) :
    chartDerivative e (twoFormProduct r B) x =
      ∑ i : Fin r,
        twoFormProductReplacement r B (fun i y ↦ chartDerivative e (B i) y) i x := by
  induction r with
  | zero =>
    rw [twoFormProduct]
    simp only [Fin.sum_univ_zero]
    ext v
    change extDeriv (chartRepresentation e (ofFunction (fun _ : P ↦ (1 : ℝ))))
      (e x) (chartTangentMap e x ∘ v) = 0
    rw [chartRepresentation_ofFunction, extDeriv_constOfIsEmpty]
    change (fderiv ℝ (fun _ : E ↦ (1 : ℝ)) (e x)) (chartTangentMap e x (v 0)) = 0
    rw [fderiv_const_apply]
    rfl
  | succ r ih =>
    rw [twoFormProduct, chartDerivative_degreeCast]
    ext v
    rw [degreeCastForm_apply_intrinsic,
      chartDerivative_wedge_apply e he _ _ x hx
        ((contDiffAt_chartRepresentation_twoFormProduct r e (fun i ↦ B i.castSucc) (e x)
          (fun i ↦ hB i.castSucc)).differentiableAt (by simp))
        ((hB (Fin.last r)).differentiableAt (by simp))]
    have hsign : (-1 : ℝ)^(2*r) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
    rw [hsign, one_mul, ih _ (fun i ↦ hB i.castSucc), Fin.sum_univ_castSucc]
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply,
      twoFormProductReplacement_castSucc, twoFormProductReplacement_last,
      degreeCastForm_apply_intrinsic, wedge]
    congr 1
    have h := congrArg (fun z : Form 𝓘(ℝ, E) P (2*r+1+2) ↦
      z x (v ∘ finCongr (show 2*r+1+2 = 2*(r+1)+1 by omega)))
      (map_sum ((wedgeLinear (2*r+1) 2).flip (B (Fin.last r)))
        (fun i : Fin r ↦ twoFormProductReplacement r (fun j ↦ B j.castSucc)
          (fun j y ↦ chartDerivative e (B j.castSucc) y) i) Finset.univ)
    simp only [LinearMap.flip_apply, wedgeLinear_apply, wedge,
      Finset.sum_apply, ContinuousAlternatingMap.sum_apply] at h
    have hvec :
        ((v ∘ finCongr (show 2*r+2+1 = 2*(r+1)+1 by omega)) ∘
          finCongr (show 2*r+1+2 = 2*r+2+1 by omega)) =
        v ∘ finCongr (show 2*r+1+2 = 2*(r+1)+1 by omega) := by
      funext i
      apply congrArg v
      apply Fin.ext
      rfl
    rw [hvec]
    exact h

theorem oneFormProductReplacement_congr_at (r : ℕ)
    (θ θ' : Fin r → Form 𝓘(ℝ, E) P 1) (δ δ' : Fin r → Form 𝓘(ℝ, E) P 2)
    (x : P) (hθ : ∀ i, θ i x = θ' i x) (hδ : ∀ i, δ i x = δ' i x) (i : Fin r) :
    oneFormProductReplacement r θ δ i x = oneFormProductReplacement r θ' δ' i x := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [oneFormProductReplacement_last, oneFormProductReplacement_last]
      change wedgeFiber _ _ = wedgeFiber _ _
      rw [oneFormProduct_congr_at r x (fun j ↦ hθ j.castSucc), hδ]
    · rw [oneFormProductReplacement_castSucc, oneFormProductReplacement_castSucc]
      change wedgeFiber _ _ = wedgeFiber _ _
      rw [ih _ _ _ _ (fun j ↦ hθ j.castSucc) (fun j ↦ hδ j.castSucc) j, hθ]

theorem twoFormProductReplacement_congr_at (r : ℕ)
    (B B' : Fin r → Form 𝓘(ℝ, E) P 2) (δ δ' : Fin r → Form 𝓘(ℝ, E) P 3)
    (x : P) (hB : ∀ i, B i x = B' i x) (hδ : ∀ i, δ i x = δ' i x) (i : Fin r) :
    twoFormProductReplacement r B δ i x = twoFormProductReplacement r B' δ' i x := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [twoFormProductReplacement_last, twoFormProductReplacement_last]
      ext v
      simp only [degreeCastForm_apply_intrinsic, wedge]
      rw [twoFormProduct_congr_at r x (fun j ↦ hB j.castSucc), hδ]
    · rw [twoFormProductReplacement_castSucc, twoFormProductReplacement_castSucc]
      ext v
      simp only [degreeCastForm_apply_intrinsic, wedge]
      rw [ih _ _ _ _ (fun j ↦ hB j.castSucc) (fun j ↦ hδ j.castSucc) j, hB]

/-- The actual globally defined derivative of a product, at a point where
its factors are smooth in the centered chart. Factors need not be smooth elsewhere. -/
theorem exteriorDerivative_oneFormProduct_at (r : ℕ)
    (θ : Fin r → Form 𝓘(ℝ, E) P 1) (x : P)
    (hθ : ∀ i, ContDiffAt ℝ ∞ (chartRepresentation (chartAt E x) (θ i)) (chartAt E x x)) :
    exteriorDerivative (oneFormProduct r θ) x =
      ∑ i : Fin r, (-1 : ℝ)^i.val •
        oneFormProductReplacement r θ (fun i ↦ exteriorDerivative (θ i)) i x := by
  rw [exteriorDerivative, chartDerivative_oneFormProduct r (chartAt E x)
    (IsManifold.chart_mem_maximalAtlas x) θ x (mem_chart_source E x) hθ]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun z ↦ (-1 : ℝ)^i.val • z)
  exact oneFormProductReplacement_congr_at r θ θ
    (fun i y ↦ chartDerivative (chartAt E x) (θ i) y)
    (fun i ↦ exteriorDerivative (θ i)) x (fun _ ↦ rfl) (fun _ ↦ rfl) i

theorem exteriorDerivative_twoFormProduct_at (r : ℕ)
    (B : Fin r → Form 𝓘(ℝ, E) P 2) (x : P)
    (hB : ∀ i, ContDiffAt ℝ ∞ (chartRepresentation (chartAt E x) (B i)) (chartAt E x x)) :
    exteriorDerivative (twoFormProduct r B) x =
      ∑ i : Fin r, twoFormProductReplacement r B (fun i ↦ exteriorDerivative (B i)) i x := by
  rw [exteriorDerivative, chartDerivative_twoFormProduct r (chartAt E x)
    (IsManifold.chart_mem_maximalAtlas x) B x (mem_chart_source E x) hB]
  apply Finset.sum_congr rfl
  intro i _
  exact twoFormProductReplacement_congr_at r B B
    (fun i y ↦ chartDerivative (chartAt E x) (B i) y)
    (fun i ↦ exteriorDerivative (B i)) x (fun _ ↦ rfl) (fun _ ↦ rfl) i

end GaussBonnetChern.Chern

noncomputable section
open scoped Manifold BigOperators
namespace GaussBonnetChern.Chern
open DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

/-- Split off the first one-form without changing the order of the remaining factors. -/
theorem oneFormProduct_cons (r : ℕ) (θ : Fin (r+1) → Form 𝓘(ℝ, E) P 1) :
    oneFormProduct (r+1) θ =
      degreeCastForm (show 1+r = r+1 by omega)
        (wedge (θ 0) (oneFormProduct r (fun i ↦ θ i.succ))) := by
  have hp := graded_oneFormProduct (r+1) θ
  rw [List.ofFn_succ, List.prod_cons, graded_oneFormProduct] at hp
  have h := GradedForm.eq_of_degreeCast
    (a := (⟨1, θ 0⟩ : GradedForm) * ⟨r, oneFormProduct r (fun i ↦ θ i.succ)⟩)
    (b := (⟨r+1, degreeCastForm (show 1+r = r+1 by omega)
      (wedge (θ 0) (oneFormProduct r (fun i ↦ θ i.succ)))⟩ : GradedForm))
    (show 1+r = r+1 by omega) rfl
  exact GradedForm.mk_injective (hp.symm.trans h)

/-- Split off the first two-form with only the canonical degree transport. -/
theorem twoFormProduct_cons (r : ℕ) (B : Fin (r+1) → Form 𝓘(ℝ, E) P 2) :
    twoFormProduct (r+1) B =
      degreeCastForm (show 2+2*r = 2*(r+1) by omega)
        (wedge (B 0) (twoFormProduct r (fun i ↦ B i.succ))) := by
  have hp := graded_twoFormProduct (r+1) B
  rw [List.ofFn_succ, List.prod_cons, graded_twoFormProduct] at hp
  have h := GradedForm.eq_of_degreeCast
    (a := (⟨2, B 0⟩ : GradedForm) * ⟨2*r, twoFormProduct r (fun i ↦ B i.succ)⟩)
    (b := (⟨2*(r+1), degreeCastForm (show 2+2*r = 2*(r+1) by omega)
      (wedge (B 0) (twoFormProduct r (fun i ↦ B i.succ)))⟩ : GradedForm))
    (show 2+2*r = 2*(r+1) by omega) rfl
  exact GradedForm.mk_injective (hp.symm.trans h)

end GaussBonnetChern.Chern
