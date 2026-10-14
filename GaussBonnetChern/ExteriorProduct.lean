import GaussBonnetChern.ExteriorDerivativeNaturality
import GaussBonnetChern.BlockSwapSign
import Mathlib.LinearAlgebra.Multilinear.TensorProduct
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Genuine scalar exterior products

The product is normalized alternatization of the scalar multilinear block
product. The factor is `1/(k! l!)` and the block indices are explicit.
The fiber construction is topological, so no artificial norm on manifold tangent
spaces is chosen. Operator norms are used only for the model-space smoothness proof.
-/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.DifferentialForm
set_option backward.isDefEq.respectTransparency false

section FiberProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {k l : ℕ}

/-- Scalar multilinear block product, using the genuine algebraic `domCoprod`
and scalar multiplication on the tensor codomain. -/
def blockProductLinear (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) :
    MultilinearMap ℝ (fun _ : Fin (k + l) ↦ E) ℝ :=
  (LinearMap.mul' ℝ ℝ).compMultilinearMap
    ((MultilinearMap.domCoprod a.toAlternatingMap.toMultilinearMap
      b.toAlternatingMap.toMultilinearMap).domDomCongr finSumFinEquiv)

@[simp] theorem blockProductLinear_apply
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (v : Fin (k + l) → E) :
    blockProductLinear a b v =
      a (fun i ↦ v (Fin.castAdd l i)) * b (fun j ↦ v (Fin.natAdd k j)) := by
  simp [blockProductLinear, MultilinearMap.domCoprod_apply, Function.comp_def]

/-- The multilinear block product is continuous as a product of two actual
continuous maps evaluated on the corresponding finite blocks. -/
def blockProduct (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + l) ↦ E) ℝ where
  toMultilinearMap := blockProductLinear a b
  cont := by
    change Continuous (fun v : Fin (k + l) → E ↦
      a (fun i ↦ v (Fin.castAdd l i)) * b (fun j ↦ v (Fin.natAdd k j)))
    exact (a.toContinuousMultilinearMap.cont.comp
      (continuous_pi (fun i ↦ continuous_apply (Fin.castAdd l i)))).mul
      (b.toContinuousMultilinearMap.cont.comp
        (continuous_pi (fun j ↦ continuous_apply (Fin.natAdd k j))))

@[simp] theorem blockProduct_apply
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (v : Fin (k + l) → E) :
    blockProduct a b v =
      a (fun i ↦ v (Fin.castAdd l i)) * b (fun j ↦ v (Fin.natAdd k j)) :=
  blockProductLinear_apply a b v

/-- The usual normalized exterior product of continuous scalar forms.
This finite alternatization definition is intrinsic to each topological fiber. -/
def wedgeFiber (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) :
    ContinuousAlternatingMap ℝ E ℝ (Fin (k + l)) :=
  ((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹ •
    ContinuousMultilinearMap.alternatization (blockProduct a b)

/-- Explicit all-permutations formula, with the conventional `1/(k! l!)`
normalization and the exact finite block embeddings. -/
theorem wedgeFiber_apply
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (v : Fin (k + l) → E) :
    wedgeFiber a b v = ((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹ *
      ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
        (a (fun i ↦ v (σ (Fin.castAdd l i))) *
          b (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  simp only [wedgeFiber, ContinuousAlternatingMap.smul_apply,
    ContinuousMultilinearMap.alternatization_apply_apply, blockProduct_apply,
    Function.comp_def, smul_eq_mul]

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- Exterior product commutes with every actual continuous linear pullback. -/
theorem wedgeFiber_compContinuousLinearMap
    (a : ContinuousAlternatingMap ℝ F ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ F ℝ (Fin l)) (L : E →L[ℝ] F) :
    (wedgeFiber a b).compContinuousLinearMap L =
      wedgeFiber (a.compContinuousLinearMap L) (b.compContinuousLinearMap L) := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, wedgeFiber_apply,
    Function.comp_def]

/-- Integer permutation sign interpreted in the scalar field of the forms. -/
def permutationSignReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : ℝ := ((Equiv.Perm.sign σ : ℤ) : ℝ)

@[simp] theorem permutationSignReal_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ τ : Equiv.Perm ι) :
    permutationSignReal (σ * τ) = permutationSignReal σ * permutationSignReal τ := by
  simp [permutationSignReal, map_mul]

@[simp] theorem permutationSignReal_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : permutationSignReal σ * permutationSignReal σ = 1 := by
  simp only [permutationSignReal, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
    Units.val_one, Int.cast_one]

@[simp] theorem permutationSignReal_permCongr {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (σ : Equiv.Perm ι) :
    permutationSignReal (e.permCongr σ) = permutationSignReal σ := by
  simp only [permutationSignReal, Equiv.Perm.sign_permCongr]

/-- The same all-permutations formula with permutation signs represented as
actual real coefficients. -/
theorem wedgeFiber_apply_realSign
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (v : Fin (k + l) → E) :
    wedgeFiber a b v = ((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹ *
      ∑ σ : Equiv.Perm (Fin (k + l)), permutationSignReal σ *
        (a (fun i ↦ v (σ (Fin.castAdd l i))) *
          b (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  rw [wedgeFiber_apply]
  simp only [permutationSignReal, Units.smul_def, zsmul_eq_mul]

/-- Swapping the two factors produces exactly the sign of the concrete block
permutation, after the canonical order-preserving degree cast. -/
theorem wedgeFiber_swap_sign
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (v : Fin (k + l) → E) :
    wedgeFiber b a (fun i ↦ v (finCongr (Nat.add_comm l k) i)) =
      permutationSignReal
        ((finAddFlip : Fin (k + l) ≃ Fin (l + k)).trans (finCongr (Nat.add_comm l k))) *
        wedgeFiber a b v := by
  let θ : Fin (l + k) ≃ Fin (k + l) := finCongr (Nat.add_comm l k)
  let q : Equiv.Perm (Fin (k + l)) :=
    (finAddFlip : Fin (k + l) ≃ Fin (l + k)).trans θ
  let ψ : Equiv.Perm (Fin (l + k)) ≃ Equiv.Perm (Fin (k + l)) :=
    θ.permCongr.trans (Equiv.mulRight q)
  have hsign (σ : Equiv.Perm (Fin (l + k))) :
      permutationSignReal (ψ σ) = permutationSignReal σ * permutationSignReal q := by
    simp [ψ]
  have hfirst (σ : Equiv.Perm (Fin (l + k))) :
      (fun i : Fin k ↦ v (ψ σ (Fin.castAdd l i))) =
        (fun i : Fin k ↦ v (θ (σ (Fin.natAdd l i)))) := by
    funext i
    simp [ψ, q, Equiv.Perm.mul_apply]
  have hsecond (σ : Equiv.Perm (Fin (l + k))) :
      (fun i : Fin l ↦ v (ψ σ (Fin.natAdd k i))) =
        (fun i : Fin l ↦ v (θ (σ (Fin.castAdd k i)))) := by
    funext i
    simp [ψ, q, Equiv.Perm.mul_apply]
  let S : Equiv.Perm (Fin (k + l)) → ℝ := fun σ ↦ permutationSignReal σ *
    (a (fun i ↦ v (σ (Fin.castAdd l i))) * b (fun j ↦ v (σ (Fin.natAdd k j))))
  have hsummand (σ : Equiv.Perm (Fin (l + k))) :
      permutationSignReal σ *
        (b (fun i ↦ v (θ (σ (Fin.castAdd k i)))) *
          a (fun j ↦ v (θ (σ (Fin.natAdd l j))))) = permutationSignReal q * S (ψ σ) := by
    unfold S
    rw [hsign, hfirst, hsecond]
    calc
      _ = (permutationSignReal q * permutationSignReal q) * permutationSignReal σ *
          (b (fun i ↦ v (θ (σ (Fin.castAdd k i)))) *
            a (fun j ↦ v (θ (σ (Fin.natAdd l j))))) := by rw [permutationSignReal_sq]; ring
      _ = _ := by ring
  have hsum : (∑ σ : Equiv.Perm (Fin (l + k)), permutationSignReal σ *
      (b (fun i ↦ v (θ (σ (Fin.castAdd k i)))) *
        a (fun j ↦ v (θ (σ (Fin.natAdd l j)))))) =
      permutationSignReal q * ∑ σ : Equiv.Perm (Fin (k + l)), S σ := by
    calc
      _ = ∑ σ : Equiv.Perm (Fin (l + k)), permutationSignReal q * S (ψ σ) := by
        apply Finset.sum_congr rfl
        intro σ _
        exact hsummand σ
      _ = permutationSignReal q * ∑ σ : Equiv.Perm (Fin (l + k)), S (ψ σ) :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by rw [ψ.sum_comp S]
  rw [wedgeFiber_apply_realSign, wedgeFiber_apply_realSign]
  change ((l.factorial : ℝ) * (k.factorial : ℝ))⁻¹ *
    (∑ σ : Equiv.Perm (Fin (l + k)), permutationSignReal σ *
      (b (fun i ↦ v (θ (σ (Fin.castAdd k i)))) *
        a (fun j ↦ v (θ (σ (Fin.natAdd l j)))))) =
    permutationSignReal q * (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹ * ∑ σ, S σ)
  rw [hsum, mul_comm (l.factorial : ℝ) (k.factorial : ℝ)]
  ring

/-- The ordinary graded-commutativity sign for the normalized fiber product.
The degree cast is order-preserving and does not itself insert a permutation. -/
theorem wedgeFiber_graded_comm
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (v : Fin (k + l) → E) :
    wedgeFiber b a (fun i ↦ v (finCongr (Nat.add_comm l k) i)) =
      (-1 : ℝ) ^ (k * l) * wedgeFiber a b v := by
  rw [wedgeFiber_swap_sign]
  congr 1
  change ((Equiv.Perm.sign (blockSwapPerm k l) : ℤ) : ℝ) = _
  rw [sign_blockSwapPerm]
  simp

end FiberProduct

section ModelNorms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}

/-- The contiguous index blocks partition all `k+l` arguments. -/
theorem block_norm_product (v : Fin (k + l) → E) :
    (∏ i : Fin k, ‖v (Fin.castAdd l i)‖) *
      (∏ j : Fin l, ‖v (Fin.natAdd k j)‖) = ∏ i : Fin (k + l), ‖v i‖ := by
  simpa only [Fintype.prod_sum_type, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    using (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l)).prod_comp (fun i ↦ ‖v i‖)

/-- Explicit bound for the scalar block multilinear map. -/
theorem blockProduct_apply_bound
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) (v : Fin (k + l) → E) :
    ‖blockProduct a b v‖ ≤ (‖a‖ * ‖b‖) * ∏ i : Fin (k + l), ‖v i‖ := by
  rw [blockProduct_apply, norm_mul]
  calc
    _ ≤ (‖a‖ * ∏ i : Fin k, ‖v (Fin.castAdd l i)‖) *
        (‖b‖ * ∏ j : Fin l, ‖v (Fin.natAdd k j)‖) :=
      mul_le_mul (a.le_opNorm _) (b.le_opNorm _) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _)))
    _ = _ := by rw [← block_norm_product v]; ring

/-- Operator norm of the block product is bounded by the product of norms. -/
theorem norm_blockProduct_le
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) : ‖blockProduct a b‖ ≤ ‖a‖ * ‖b‖ :=
  ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (blockProduct_apply_bound a b)

/-- On normed model spaces, the intrinsic exterior product is precisely the
previously proved bounded alternatization operator with its normalization. -/
theorem wedgeFiber_eq_alternatizationCLM
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) :
    wedgeFiber a b = ((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹ •
      alternatizationCLM (k + l) (blockProduct a b) := rfl

/-- The scalar multilinear block product is bilinear in its two forms. -/
def blockProductBilinearLinear (k l : ℕ) :
    ContinuousAlternatingMap ℝ E ℝ (Fin k) →ₗ[ℝ]
      ContinuousAlternatingMap ℝ E ℝ (Fin l) →ₗ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (k + l) ↦ E) ℝ :=
  LinearMap.mk₂ ℝ blockProduct
    (fun a₁ a₂ b ↦ by ext v; simp [blockProduct_apply, add_mul])
    (fun c a b ↦ by ext v; simp [blockProduct_apply, smul_eq_mul, mul_assoc])
    (fun a b₁ b₂ ↦ by ext v; simp [blockProduct_apply, mul_add])
    (fun c a b ↦ by ext v; simp [blockProduct_apply, smul_eq_mul, mul_left_comm])

/-- The model-space block product is a bounded bilinear operation. -/
def blockProductBilinear (k l : ℕ) :
    ContinuousAlternatingMap ℝ E ℝ (Fin k) →L[ℝ]
      ContinuousAlternatingMap ℝ E ℝ (Fin l) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (k + l) ↦ E) ℝ :=
  (blockProductBilinearLinear k l).mkContinuous₂ 1
    (fun a b ↦ by simpa only [blockProductBilinearLinear, LinearMap.mk₂_apply, one_mul] using norm_blockProduct_le a b)

/-- The normalized exterior product is itself a bounded bilinear operation
on the normed model-space forms. -/
def wedgeFiberBilinear (k l : ℕ) :
    ContinuousAlternatingMap ℝ E ℝ (Fin k) →L[ℝ]
      ContinuousAlternatingMap ℝ E ℝ (Fin l) →L[ℝ]
        ContinuousAlternatingMap ℝ E ℝ (Fin (k + l)) :=
  (ContinuousLinearMap.compL ℝ
    (ContinuousAlternatingMap ℝ E ℝ (Fin l))
    (ContinuousMultilinearMap ℝ (fun _ : Fin (k + l) ↦ E) ℝ)
    (ContinuousAlternatingMap ℝ E ℝ (Fin (k + l)))
    (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹ • alternatizationCLM (k + l))).comp
      (blockProductBilinear k l)

@[simp] theorem wedgeFiberBilinear_apply
    (a : ContinuousAlternatingMap ℝ E ℝ (Fin k))
    (b : ContinuousAlternatingMap ℝ E ℝ (Fin l)) :
    wedgeFiberBilinear k l a b = wedgeFiber a b := rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {a : V → ContinuousAlternatingMap ℝ E ℝ (Fin k)}
  {b : V → ContinuousAlternatingMap ℝ E ℝ (Fin l)} {x : V}

/-- Smooth dependence of the actual exterior product on both of its forms. -/
theorem contDiffAt_wedgeFiber (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) :
    ContDiffAt ℝ ∞ (fun z ↦ wedgeFiber (a z) (b z)) x := by
  have hop : ContDiffAt ℝ ∞
      (wedgeFiberBilinear (E := E) k l) (a x) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (E := ContinuousAlternatingMap ℝ E ℝ (Fin k))
      (F := ContinuousAlternatingMap ℝ E ℝ (Fin l) →L[ℝ]
        ContinuousAlternatingMap ℝ E ℝ (Fin (k + l)))
      (wedgeFiberBilinear (E := E) k l)).contDiffAt (x := a x)
  have h := (hop.comp x ha).clm_apply hb
  exact h

end ModelNorms

section ManifoldProduct
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {k l : ℕ}

/-- Intrinsic pointwise exterior product of genuine tangent-space forms. -/
def wedge (α : Form 𝓘(ℝ, E) M k) (β : Form 𝓘(ℝ, E) M l) :
    Form 𝓘(ℝ, E) M (k + l) := fun x ↦ wedgeFiber (α x) (β x)

/-- Actual sum formula for the manifold form exterior product. -/
theorem wedge_apply (α : Form 𝓘(ℝ, E) M k) (β : Form 𝓘(ℝ, E) M l)
    (x : M) (v : Fin (k + l) → TangentSpace 𝓘(ℝ, E) x) :
    wedge α β x v = ((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹ *
      ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
        (α x (fun i ↦ v (σ (Fin.castAdd l i))) *
          β x (fun j ↦ v (σ (Fin.natAdd k j)))) :=
  wedgeFiber_apply (α x) (β x) v

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

/-- Manifold pullback commutes with the actual exterior product. Since this
identity is fiberwise algebra, it does not require smoothness of the map. -/
theorem pullback_wedge (f : M → N)
    (α : Form 𝓘(ℝ, F) N k) (β : Form 𝓘(ℝ, F) N l) :
    pullback (I := 𝓘(ℝ, E)) f (wedge α β) =
      wedge (pullback (I := 𝓘(ℝ, E)) f α) (pullback (I := 𝓘(ℝ, E)) f β) := by
  funext x
  exact wedgeFiber_compContinuousLinearMap (α (f x)) (β (f x))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The intrinsic exterior product has the usual pointwise wedge as its
representation in every actual chart. -/
theorem chartRepresentation_wedge (e : OpenPartialHomeomorph M E)
    (α : Form 𝓘(ℝ, E) M k) (β : Form 𝓘(ℝ, E) M l) (y : E) :
    chartRepresentation e (wedge α β) y =
      wedgeFiber (chartRepresentation e α y) (chartRepresentation e β y) := by
  rw [chartRepresentation_eq, chartRepresentation_eq, chartRepresentation_eq]
  exact wedgeFiber_compContinuousLinearMap (α (e.symm y)) (β (e.symm y))
    (inverseChartTangentMap e y)

/-- Exterior products preserve actual chartwise smoothness. -/
theorem IsSmooth.wedge {α : Form 𝓘(ℝ, E) M k} {β : Form 𝓘(ℝ, E) M l}
    (hα : IsSmooth α) (hβ : IsSmooth β) : IsSmooth (wedge α β) := by
  intro e he
  have hlocal : ContDiffOn ℝ ∞
      (fun y ↦ wedgeFiber (chartRepresentation e α y) (chartRepresentation e β y)) e.target := by
    intro y hy
    exact (contDiffAt_wedgeFiber
      ((hα e he).contDiffAt (e.open_target.mem_nhds hy))
      ((hβ e he).contDiffAt (e.open_target.mem_nhds hy))).contDiffWithinAt
  exact hlocal.congr (fun y _ ↦ chartRepresentation_wedge e α β y)

/-- Pointwise graded commutativity of genuine manifold forms, in every degree. -/
theorem wedge_graded_comm (α : Form 𝓘(ℝ, E) M k) (β : Form 𝓘(ℝ, E) M l)
    (x : M) (v : Fin (k + l) → TangentSpace 𝓘(ℝ, E) x) :
    wedge β α x (fun i ↦ v (finCongr (Nat.add_comm l k) i)) =
      (-1 : ℝ) ^ (k * l) * wedge α β x v :=
  wedgeFiber_graded_comm (α x) (β x) v

end ManifoldProduct
end GaussBonnetChern.DifferentialForm




