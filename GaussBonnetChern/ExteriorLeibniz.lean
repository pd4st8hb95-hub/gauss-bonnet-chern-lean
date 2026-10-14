import GaussBonnetChern.ExteriorProduct
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! # The graded Leibniz rule for the normalized exterior product

The finite-permutation proof tracks the derivative slot and block permutations.
The coefficient `(k+1)` cancels against `(k+1)!`; the derivative and exterior
product are the actual operations defined in the preceding modules.
-/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators
namespace GaussBonnetChern.DifferentialForm
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} {n : ℕ}
def signedPermutationSum (f : (Fin n → E) → ℝ) (v : Fin n → E) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), permutationSignReal σ * f (v ∘ σ)

theorem signedPermutationSum_precomp
    (f : (Fin n → E) → ℝ) (τ : Equiv.Perm (Fin n)) (v : Fin n → E) :
    signedPermutationSum (fun w ↦ f (w ∘ τ)) v =
      permutationSignReal τ * signedPermutationSum f v := by
  let S : Equiv.Perm (Fin n) → ℝ := fun σ ↦ permutationSignReal σ * f (v ∘ σ)
  have h (σ : Equiv.Perm (Fin n)) :
      permutationSignReal σ * f ((v ∘ σ) ∘ τ) = permutationSignReal τ * S (σ * τ) := by
    simp only [S, permutationSignReal_mul, Equiv.Perm.coe_mul]
    change permutationSignReal σ * f (v ∘ σ ∘ τ) = _
    calc
      _ = (permutationSignReal τ * permutationSignReal τ) *
          permutationSignReal σ * f (v ∘ σ ∘ τ) := by rw [permutationSignReal_sq]; ring
      _ = _ := by ring
  unfold signedPermutationSum
  simp_rw [h]
  rw [← Finset.mul_sum]
  change permutationSignReal τ * (∑ i, S ((Equiv.mulRight τ) i)) =
    permutationSignReal τ * (∑ i, S i)
  rw [Equiv.sum_comp (Equiv.mulRight τ) S]

theorem signedPermutationSum_decompose
    (f : (Fin (n + 1) → E) → ℝ) (v : Fin (n + 1) → E) :
    signedPermutationSum f v = ∑ i : Fin (n + 1), (-1 : ℝ)^i.val *
      ∑ σ : Equiv.Perm (Fin n), permutationSignReal σ *
        f (Fin.cons (v i) (fun j ↦ v (i.succAbove (σ j)))) := by
  cases n with
  | zero =>
    simp [signedPermutationSum, permutationSignReal]
    congr 1
    funext j
    exact Fin.cases rfl (fun i ↦ Fin.elim0 i) j
  | succ n =>
    let S : Equiv.Perm (Fin (n + 2)) → ℝ :=
      fun σ ↦ permutationSignReal σ * f (v ∘ σ)
    have hsign (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
        permutationSignReal (Equiv.Perm.decomposeFin'Symm i σ) =
          (-1 : ℝ)^i.val * permutationSignReal σ := by
      simp [permutationSignReal, Equiv.Perm.sign_decomposeFin'Symm]
    have harg (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
        v ∘ Equiv.Perm.decomposeFin'Symm i σ =
          Fin.cons (v i) (fun j ↦ v (i.succAbove (σ j))) := by
      funext j
      refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp
    change (∑ σ, S σ) = _
    rw [← Equiv.Perm.decomposeFin'.symm.sum_comp S, Fintype.sum_prod_type]
    simp only [Equiv.Perm.decomposeFin'_symm, S, hsign, harg, mul_assoc, Finset.mul_sum]

def firstBlockCycle (k l : ℕ) (i : Fin (k + 1)) : Equiv.Perm (Fin (k + 1 + l)) :=
  (finSumFinEquiv : Fin (k + 1) ⊕ Fin l ≃ Fin (k + 1 + l)).permCongr
    (Equiv.Perm.sumCongr i.cycleRange.symm 1)

@[simp] theorem firstBlockCycle_castAdd (k l : ℕ) (i j : Fin (k + 1)) :
    firstBlockCycle k l i (Fin.castAdd l j) = Fin.castAdd l (i.cycleRange.symm j) := by
  simp [firstBlockCycle, Equiv.permCongr_def]

@[simp] theorem firstBlockCycle_natAdd (k l : ℕ) (i : Fin (k + 1)) (j : Fin l) :
    firstBlockCycle k l i (Fin.natAdd (k + 1) j) = Fin.natAdd (k + 1) j := by
  simp [firstBlockCycle, Equiv.permCongr_def]

@[simp] theorem permutationSignReal_firstBlockCycle (k l : ℕ) (i : Fin (k + 1)) :
    permutationSignReal (firstBlockCycle k l i) = (-1 : ℝ)^i.val := by
  simp [firstBlockCycle, permutationSignReal, Equiv.Perm.sign_sumCongr]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}

def rawDerivativeBlock
    (p : E →L[ℝ] ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (w : Fin (k + 1 + l) → E) : ℝ :=
  p (w (Fin.castAdd l 0)) (fun j ↦ w (Fin.castAdd l j.succ)) *
    b (fun j ↦ w (Fin.natAdd (k + 1) j))

theorem blockProduct_uncurry_apply
    (p : E →L[ℝ] ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (w : Fin (k + 1 + l) → E) :
    blockProduct (ContinuousAlternatingMap.alternatizeUncurryFin p) b w =
      ∑ i : Fin (k + 1), (-1 : ℝ)^i.val *
        rawDerivativeBlock p b (w ∘ firstBlockCycle k l i) := by
  rw [blockProduct_apply, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp [rawDerivativeBlock, Function.comp_def, Fin.removeNth_apply,
    Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ, zsmul_eq_mul,
    mul_assoc]
  left
  rfl

theorem signedPermutationSum_blockProduct_uncurry
    (p : E →L[ℝ] ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (v : Fin (k + 1 + l) → E) :
    signedPermutationSum (fun w ↦ blockProduct
      (ContinuousAlternatingMap.alternatizeUncurryFin p) b w) v =
      (k + 1 : ℝ) * signedPermutationSum (rawDerivativeBlock p b) v := by
  unfold signedPermutationSum
  simp_rw [blockProduct_uncurry_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsum (i : Fin (k + 1)) :
      (∑ σ : Equiv.Perm (Fin (k + 1 + l)), permutationSignReal σ *
        ((-1 : ℝ)^i.val * rawDerivativeBlock p b
          ((v ∘ σ) ∘ firstBlockCycle k l i))) =
        signedPermutationSum (rawDerivativeBlock p b) v := by
    calc
      _ = (-1 : ℝ)^i.val * signedPermutationSum
          (fun w ↦ rawDerivativeBlock p b (w ∘ firstBlockCycle k l i)) v := by
        unfold signedPermutationSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ _
        ring
      _ = _ := by
        rw [signedPermutationSum_precomp, permutationSignReal_firstBlockCycle]
        rw [← mul_assoc, ← pow_add, show i.val + i.val = 2 * i.val by omega,
          pow_mul, neg_one_sq, one_pow, one_mul]
  simp_rw [hsum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_one]
  unfold signedPermutationSum
  rw [Finset.mul_sum]

theorem signedPermutationSum_domCongr {m : ℕ} (e : Fin m ≃ Fin n)
    (f : (Fin m → E) → ℝ) (v : Fin n → E) :
    signedPermutationSum f (v ∘ e) =
      signedPermutationSum (fun w ↦ f (w ∘ e)) v := by
  unfold signedPermutationSum
  refine Fintype.sum_equiv e.permCongr _ _ ?_
  intro σ
  rw [permutationSignReal_permCongr]
  congr 2
  funext j
  simp [Equiv.permCongr_def, Function.comp_def]

def rawExteriorLeft
    (p : E →L[ℝ] ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (w : Fin (k + l + 1) → E) : ℝ :=
  p (w 0) (fun j ↦ w (Fin.castAdd l j).succ) *
    b (fun j ↦ w (Fin.natAdd k j).succ)

theorem uncurry_wedgeFiber_left_sum
    (p : E →L[ℝ] ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (v : Fin (k + l + 1) → E) :
    (∑ i : Fin (k + l + 1), (-1 : ℝ)^i.val *
        wedgeFiber (p (v i)) b (i.removeNth v)) =
      ((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹ *
        signedPermutationSum (rawExteriorLeft p b) v := by
  rw [signedPermutationSum_decompose, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [wedgeFiber_apply_realSign]
  simp only [rawExteriorLeft, Fin.cons_zero, Fin.cons_succ,
    Fin.removeNth_apply]
  ring

theorem rawDerivativeBlock_degreeCast
    (p : E →L[ℝ] ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (v : Fin (k + l + 1) → E) :
    rawDerivativeBlock p b (v ∘ finCongr (show k + 1 + l = k + l + 1 by omega)) =
      rawExteriorLeft p b v := by
  unfold rawDerivativeBlock rawExteriorLeft
  congr 1
  congr 1
  funext j
  apply congrArg v
  apply Fin.ext
  change k + 1 + j.val = k + j.val + 1
  omega
theorem uncurry_wedgeFiber_left
    (p : E →L[ℝ] ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (v : Fin (k + l + 1) → E) :
    (∑ i : Fin (k + l + 1), (-1 : ℝ)^i.val *
        wedgeFiber (p (v i)) b (i.removeNth v)) =
      wedgeFiber (ContinuousAlternatingMap.alternatizeUncurryFin p) b
        (v ∘ finCongr (show k + 1 + l = k + l + 1 by omega)) := by
  rw [uncurry_wedgeFiber_left_sum, wedgeFiber_apply_realSign]
  change _ = ((↑((k + 1).factorial) : ℝ) * ↑l.factorial)⁻¹ *
    signedPermutationSum (fun w ↦ blockProduct
      (ContinuousAlternatingMap.alternatizeUncurryFin p) b w)
      (v ∘ finCongr (show k + 1 + l = k + l + 1 by omega))
  rw [signedPermutationSum_blockProduct_uncurry, signedPermutationSum_domCongr]
  have hfun : (fun w ↦ rawDerivativeBlock p b
      (w ∘ finCongr (show k + 1 + l = k + l + 1 by omega))) = rawExteriorLeft p b := by
    funext w
    exact rawDerivativeBlock_degreeCast p b w
  rw [hfun]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hl : (l.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr l.factorial_ne_zero
  have hs : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

/-- The canonical transport of a degree equality as a continuous linear map. -/
def degreeCastCLM {k l : ℕ} (h : k = l) :
    ContinuousAlternatingMap ℝ E ℝ (Fin k) →L[ℝ]
      ContinuousAlternatingMap ℝ E ℝ (Fin l) := by
  subst l
  exact ContinuousLinearMap.id ℝ _

@[simp] theorem degreeCastCLM_apply {k l : ℕ} (h : k = l)
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k)) (v : Fin l → E) :
    degreeCastCLM h a v = a (v ∘ finCongr h) := by
  subst l
  rfl

@[simp] theorem degreeCastCLM_trans {k l m : ℕ} (h : k = l) (h' : l = m)
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k)) :
    degreeCastCLM h' (degreeCastCLM h a) = degreeCastCLM (h.trans h') a := by
  subst l m
  rfl

theorem alternatizeUncurryFin_degreeCast {k l : ℕ} (h : k = l)
    (p : E →L[ℝ] ContinuousAlternatingMap ℝ E ℝ (Fin k)) :
    ContinuousAlternatingMap.alternatizeUncurryFin ((degreeCastCLM h).comp p) =
      degreeCastCLM (congrArg (fun n ↦ n + 1) h)
        (ContinuousAlternatingMap.alternatizeUncurryFin p) := by
  subst l
  rfl

theorem alternatizeUncurryFin_wedge_left
    (p : E →L[ℝ] ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) :
    ContinuousAlternatingMap.alternatizeUncurryFin
      ((wedgeFiberBilinear k l).precompL E p b) =
      degreeCastCLM (show k + 1 + l = k + l + 1 by omega)
        (wedgeFiber (ContinuousAlternatingMap.alternatizeUncurryFin p) b) := by
  ext v
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, degreeCastCLM_apply]
  simp only [ContinuousLinearMap.precompL_apply, wedgeFiberBilinear_apply,
    zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact uncurry_wedgeFiber_left p b v

theorem alternatizeUncurryFin_wedge_right
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (p : E →L[ℝ] ContinuousAlternatingMap ℝ E ℝ (Fin l)) :
    ContinuousAlternatingMap.alternatizeUncurryFin ((wedgeFiberBilinear k l a).comp p) =
      (-1 : ℝ)^k • degreeCastCLM (show k + (l + 1) = k + l + 1 by omega)
        (wedgeFiber a (ContinuousAlternatingMap.alternatizeUncurryFin p)) := by
  have hswap : (wedgeFiberBilinear k l a).comp p = (-1 : ℝ)^(l * k) •
      (degreeCastCLM (Nat.add_comm l k)).comp
        ((wedgeFiberBilinear l k).precompL E p a) := by
    ext u v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousAlternatingMap.smul_apply, degreeCastCLM_apply,
      ContinuousLinearMap.precompL_apply, wedgeFiberBilinear_apply, smul_eq_mul]
    exact wedgeFiber_graded_comm (p u) a (v ∘ finCongr (Nat.add_comm l k))
  rw [hswap, ContinuousAlternatingMap.alternatizeUncurryFin_smul,
    alternatizeUncurryFin_degreeCast, alternatizeUncurryFin_wedge_left,
    degreeCastCLM_trans]
  ext v
  simp only [ContinuousAlternatingMap.smul_apply, degreeCastCLM_apply, smul_eq_mul]
  have hswap' : wedgeFiber (ContinuousAlternatingMap.alternatizeUncurryFin p) a
      (v ∘ finCongr (show l + 1 + k = k + l + 1 by omega)) =
      (-1 : ℝ)^(k * (l + 1)) *
        wedgeFiber a (ContinuousAlternatingMap.alternatizeUncurryFin p)
          (v ∘ finCongr (show k + (l + 1) = k + l + 1 by omega)) :=
    wedgeFiber_graded_comm a (ContinuousAlternatingMap.alternatizeUncurryFin p)
      (v ∘ finCongr (show k + (l + 1) = k + l + 1 by omega))
  rw [hswap', ← mul_assoc, ← pow_add,
    show l * k + k * (l + 1) = 2 * (k * l) + k by ring,
    pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

variable {a : E → ContinuousAlternatingMap ℝ E ℝ (Fin k)}
  {b : E → ContinuousAlternatingMap ℝ E ℝ (Fin l)} {x : E}
/-- The actual directional derivative of exterior multiplication. -/
theorem fderiv_wedgeFiber_apply (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) (u : E) :
    fderiv ℝ (fun y ↦ wedgeFiber (a y) (b y)) x u =
      wedgeFiber (fderiv ℝ a x u) (b x) + wedgeFiber (a x) (fderiv ℝ b x u) := by
  have h := (wedgeFiberBilinear (E := E) k l).fderiv_of_bilinear ha hb
  change fderiv ℝ (fun y ↦ wedgeFiber (a y) (b y)) x = _ at h
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, wedgeFiberBilinear_apply]
  exact add_comm _ _

/-- Exterior differentiation distributes over the two factors before the
finite permutations are regrouped by their derivative slot. This formula
retains the exact normalized exterior products in every summand. -/
theorem extDeriv_wedgeFiber_apply (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) (v : Fin (k + l + 1) → E) :
    extDeriv (fun y ↦ wedgeFiber (a y) (b y)) x v =
      ∑ i : Fin (k + l + 1), (-1 : ℝ) ^ (i : ℕ) *
        (wedgeFiber (fderiv ℝ a x (v i)) (b x) (i.removeNth v) +
          wedgeFiber (a x) (fderiv ℝ b x (v i)) (i.removeNth v)) := by
  rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_wedgeFiber_apply ha hb]
  simp only [ContinuousAlternatingMap.add_apply, zsmul_eq_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one]


/-- The usual graded Leibniz identity for actual model-space forms, including
zero degrees. The two casts only identify equal total degrees. -/
theorem extDeriv_wedgeFiber (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    extDeriv (fun y ↦ wedgeFiber (a y) (b y)) x =
      degreeCastCLM (show k + 1 + l = k + l + 1 by omega)
        (wedgeFiber (extDeriv a x) (b x)) +
      (-1 : ℝ)^k • degreeCastCLM (show k + (l + 1) = k + l + 1 by omega)
        (wedgeFiber (a x) (extDeriv b x)) := by
  have h := (wedgeFiberBilinear (E := E) k l).fderiv_of_bilinear ha hb
  change fderiv ℝ (fun y ↦ wedgeFiber (a y) (b y)) x = _ at h
  simp only [extDeriv]
  rw [h, ContinuousAlternatingMap.alternatizeUncurryFin_add]
  change ContinuousAlternatingMap.alternatizeUncurryFin
      ((wedgeFiberBilinear k l (a x)).comp (fderiv ℝ b x)) +
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((wedgeFiberBilinear k l).precompL E (fderiv ℝ a x) (b x)) = _
  rw [alternatizeUncurryFin_wedge_right, alternatizeUncurryFin_wedge_left]
  exact add_comm _ _

section ManifoldLeibniz
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual global exterior derivative obeys the graded product identity
on every smooth real manifold, with no dimension or compactness assumption. -/
theorem exteriorDerivative_wedge_apply
    (α : Form 𝓘(ℝ, E) M k) (β : Form 𝓘(ℝ, E) M l)
    (hα : IsSmooth α) (hβ : IsSmooth β)
    (x : M) (v : Fin (k + l + 1) → TangentSpace 𝓘(ℝ, E) x) :
    exteriorDerivative (wedge α β) x v =
      wedge (exteriorDerivative α) β x
        (v ∘ finCongr (show k + 1 + l = k + l + 1 by omega)) +
      (-1 : ℝ)^k * wedge α (exteriorDerivative β) x
        (v ∘ finCongr (show k + (l + 1) = k + l + 1 by omega)) := by
  let e := chartAt E x
  let L := chartTangentMap e x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  have hy : e x ∈ e.target := e.map_source hx
  have hA : DifferentiableAt ℝ (chartRepresentation e α) (e x) :=
    ((hα e he).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have hB : DifferentiableAt ℝ (chartRepresentation e β) (e x) :=
    ((hβ e he).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have hchart : chartRepresentation e (wedge α β) =
      (fun y ↦ wedgeFiber (chartRepresentation e α y) (chartRepresentation e β y)) := by
    funext y
    exact chartRepresentation_wedge e α β y
  change extDeriv (chartRepresentation e (wedge α β)) (e x) (L ∘ v) = _
  rw [hchart, extDeriv_wedgeFiber hA hB]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    degreeCastCLM_apply, smul_eq_mul]
  change _ = wedgeFiber (exteriorDerivative α x) (β x)
      (v ∘ finCongr (show k + 1 + l = k + l + 1 by omega)) +
    (-1 : ℝ)^k * wedgeFiber (α x) (exteriorDerivative β x)
      (v ∘ finCongr (show k + (l + 1) = k + l + 1 by omega))
  rw [← chartRepresentation_recover e he α x hx, ← chartRepresentation_recover e he β x hx]
  change _ = wedgeFiber
      ((extDeriv (chartRepresentation e α) (e x)).compContinuousLinearMap L)
      ((chartRepresentation e β (e x)).compContinuousLinearMap L)
      (v ∘ finCongr (show k + 1 + l = k + l + 1 by omega)) +
    (-1 : ℝ)^k * wedgeFiber
      ((chartRepresentation e α (e x)).compContinuousLinearMap L)
      ((extDeriv (chartRepresentation e β) (e x)).compContinuousLinearMap L)
      (v ∘ finCongr (show k + (l + 1) = k + l + 1 by omega))
  rw [← wedgeFiber_compContinuousLinearMap, ← wedgeFiber_compContinuousLinearMap]
  rfl

/-- Transport between equal form degrees; this introduces no permutation. -/
def degreeCastForm {r s : ℕ} (h : r = s) (α : Form 𝓘(ℝ, E) M r) :
    Form 𝓘(ℝ, E) M s := by
  subst s
  exact α

@[simp] theorem degreeCastForm_apply {r s : ℕ} (h : r = s)
    (α : Form 𝓘(ℝ, E) M r) (x : M) (v : Fin s → TangentSpace 𝓘(ℝ, E) x) :
    degreeCastForm h α x v = α x (v ∘ finCongr h) := by
  subst s
  rfl

/-- Global graded Leibniz rule for smooth manifold forms in arbitrary degrees. -/
theorem exteriorDerivative_wedge
    (α : Form 𝓘(ℝ, E) M k) (β : Form 𝓘(ℝ, E) M l)
    (hα : IsSmooth α) (hβ : IsSmooth β) :
    exteriorDerivative (wedge α β) =
      degreeCastForm (show k + 1 + l = k + l + 1 by omega)
        (wedge (exteriorDerivative α) β) +
      (-1 : ℝ)^k • degreeCastForm (show k + (l + 1) = k + l + 1 by omega)
        (wedge α (exteriorDerivative β)) := by
  funext x
  ext v
  simp only [Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, degreeCastForm_apply, smul_eq_mul]
  exact exteriorDerivative_wedge_apply α β hα hβ x v

end ManifoldLeibniz
end GaussBonnetChern.DifferentialForm
