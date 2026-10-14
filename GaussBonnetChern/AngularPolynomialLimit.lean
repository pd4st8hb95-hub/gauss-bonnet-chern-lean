import GaussBonnetChern.ChernProductIdentities
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import GaussBonnetChern.AngularPullbackScaling
import GaussBonnetChern.NormalizedSphereLimit

/-! # Continuous dependence of the genuine Chern angular polynomial

Every fiber polynomial below is an evaluation of the existing Chern form
definition on constant Euclidean forms. The evaluation identities connect
these normed model-space operations back to the same actual form polynomial.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
namespace GaussBonnetChern
namespace Chern
open DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

theorem oneFormProduct_smul_all (r : ℕ) (c : ℝ)
    (θ : Fin r → Form 𝓘(ℝ, E) P 1) :
    oneFormProduct r (fun i => c • θ i) = c ^ r • oneFormProduct r θ := by
  simpa only [oneFormFactorsMultilinear_apply, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using
    (oneFormFactorsMultilinear (E := E) (P := P) r).map_smul_univ (fun _ => c) θ

theorem twoFormProduct_smul_all (r : ℕ) (c : ℝ)
    (B : Fin r → Form 𝓘(ℝ, E) P 2) :
    twoFormProduct r (fun i => c • B i) = c ^ r • twoFormProduct r B := by
  simpa only [twoFormFactorsMultilinear_apply, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using
    (twoFormFactorsMultilinear (E := E) (P := P) r).map_smul_univ (fun _ => c) B

/-- The real Chern term is homogeneous of curvature degree `k`, uniformly
for symbolic dimension. -/
theorem angularTerm_smul_curvature (n : ℕ) (k : Fin n) (c : ℝ)
    (u : Fin (2*n) → P → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ, E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ, E) P 2) :
    angularTerm n k u θ (fun i j => c • B i j) = c ^ k.val • angularTerm n k u θ B := by
  have hw {r s : ℕ} (α : Form 𝓘(ℝ, E) P r) (β : Form 𝓘(ℝ, E) P s) (t : ℝ) :
      wedge α (t • β) = t • wedge α β := (wedgeLinear r s α).map_smul t β
  have hcst {r s : ℕ} (h : r = s) (α : Form 𝓘(ℝ, E) P r) (t : ℝ) :
      degreeCastForm h (t • α) = t • degreeCastForm h α := by subst s; rfl
  simp only [angularTerm, twoFormProduct_smul_all, hw, hcst]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  funext x
  simp only [Pi.smul_apply, smul_smul]
  congr 1
  ring

section Pullback
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace F Q]

def angularPullbackLinear (f : P → Q) (r : ℕ) :
    Form 𝓘(ℝ, F) Q r →ₗ[ℝ] Form 𝓘(ℝ, E) P r where
  toFun := pullback (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F)) f
  map_add' _ _ := by funext x; ext v; rfl
  map_smul' _ _ := by funext x; ext v; rfl

theorem angularPullback_sum {ι : Type*} (s : Finset ι) (f : P → Q) {r : ℕ}
    (α : ι → Form 𝓘(ℝ, F) Q r) :
    pullback (I := 𝓘(ℝ, E)) f (∑ i ∈ s, α i) =
      ∑ i ∈ s, pullback (I := 𝓘(ℝ, E)) f (α i) :=
  map_sum (angularPullbackLinear f r) α s

theorem angularPullback_smul (f : P → Q) {r : ℕ} (c : ℝ) (α : Form 𝓘(ℝ, F) Q r) :
    pullback (I := 𝓘(ℝ, E)) f (c • α) = c • pullback (I := 𝓘(ℝ, E)) f α :=
  (angularPullbackLinear f r).map_smul c α

theorem angularPullback_fsmul (f : P → Q) {r : ℕ} (g : Q → ℝ) (α : Form 𝓘(ℝ, F) Q r) :
    pullback (I := 𝓘(ℝ, E)) f (fun x => g x • α x) =
      fun x => g (f x) • pullback (I := 𝓘(ℝ, E)) f α x := by
  funext x
  ext v
  rfl

theorem angularPullback_degreeCast (f : P → Q) {r s : ℕ} (h : r = s)
    (α : Form 𝓘(ℝ, F) Q r) :
    pullback (I := 𝓘(ℝ, E)) f (degreeCastForm h α) =
      degreeCastForm h (pullback (I := 𝓘(ℝ, E)) f α) := by subst s; rfl

/-- Pullback of the existing ordered product, allowing different model dimensions. -/
theorem pullback_oneFormProduct (f : P → Q) (r : ℕ) (θ : Fin r → Form 𝓘(ℝ, F) Q 1) :
    pullback (I := 𝓘(ℝ, E)) f (oneFormProduct r θ) =
      oneFormProduct r (fun i => pullback (I := 𝓘(ℝ, E)) f (θ i)) := by
  induction r with
  | zero => simp only [oneFormProduct, pullback_ofFunction, Function.comp_def]
  | succ r ih => simp only [oneFormProduct, pullback_wedge, ih]

theorem pullback_twoFormProduct (f : P → Q) (r : ℕ) (B : Fin r → Form 𝓘(ℝ, F) Q 2) :
    pullback (I := 𝓘(ℝ, E)) f (twoFormProduct r B) =
      twoFormProduct r (fun i => pullback (I := 𝓘(ℝ, E)) f (B i)) := by
  induction r with
  | zero => simp only [twoFormProduct, pullback_ofFunction, Function.comp_def]
  | succ r ih =>
    simp only [twoFormProduct, angularPullback_degreeCast, pullback_wedge, ih]

/-- The actual Chern term commutes with the actual differential-form pullback. -/
theorem pullback_angularTerm (f : P → Q) (n : ℕ) (k : Fin n)
    (u : Fin (2*n) → Q → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ, F) Q 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ, F) Q 2) :
    pullback (I := 𝓘(ℝ, E)) f (angularTerm n k u θ B) =
      angularTerm n k (fun i => u i ∘ f)
        (fun i => pullback (I := 𝓘(ℝ, E)) f (θ i))
        (fun i j => pullback (I := 𝓘(ℝ, E)) f (B i j)) := by
  simp only [angularTerm, angularPullback_sum, angularPullback_smul,
    angularPullback_fsmul, angularPullback_degreeCast, pullback_wedge,
    pullback_oneFormProduct, pullback_twoFormProduct, Function.comp_def]

theorem pullback_angularForm (f : P → Q) (n : ℕ)
    (u : Fin (2*n) → Q → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ, F) Q 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ, F) Q 2) :
    pullback (I := 𝓘(ℝ, E)) f (angularForm n u θ B) =
      angularForm n (fun i => u i ∘ f)
        (fun i => pullback (I := 𝓘(ℝ, E)) f (θ i))
        (fun i j => pullback (I := 𝓘(ℝ, E)) f (B i j)) := by
  simp only [angularForm, angularPullback_sum, angularPullback_smul, pullback_angularTerm]

end Pullback

end Chern

namespace AngularPolynomial
open DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance euclideanTangentNormedAddCommGroup (x : E) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x) :=
  inferInstanceAs (NormedAddCommGroup E)

local instance euclideanTangentNormedSpace (x : E) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ,E) x) :=
  inferInstanceAs (NormedSpace ℝ E)

abbrev Fiber (k : ℕ) := E [⋀^Fin k]→L[ℝ] ℝ

def oneProductFiber (r : ℕ) (θ : Fin r → Fiber (E := E) 1) : Fiber (E := E) r :=
  Chern.oneFormProduct (E := E) (P := E) r (fun i _ => θ i) 0

def twoProductFiber (r : ℕ) (B : Fin r → Fiber (E := E) 2) : Fiber (E := E) (2*r) :=
  Chern.twoFormProduct (E := E) (P := E) r (fun i _ => B i) 0

theorem oneProductFiber_evaluation (r : ℕ) (θ : Fin r → Form 𝓘(ℝ, E) E 1) (x : E) :
    Chern.oneFormProduct r θ x = oneProductFiber r (fun i => θ i x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change wedgeFiber (Chern.oneFormProduct r (fun i => θ i.castSucc) x) (θ (Fin.last r) x) =
      wedgeFiber (oneProductFiber r (fun i => θ i.castSucc x)) (θ (Fin.last r) x)
    rw [ih]

theorem twoProductFiber_evaluation (r : ℕ) (B : Fin r → Form 𝓘(ℝ, E) E 2) (x : E) :
    Chern.twoFormProduct r B x = twoProductFiber r (fun i => B i x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    ext v
    simp only [Chern.twoFormProduct, twoProductFiber, degreeCastForm_apply_intrinsic, wedge]
    rw [ih]
    rfl

theorem continuous_oneProductFiber (r : ℕ) :
    Continuous (oneProductFiber (E := E) r) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih =>
    change Continuous (fun θ : Fin (r+1) → Fiber (E := E) 1 =>
      wedgeFiber (oneProductFiber r (fun i => θ i.castSucc)) (θ (Fin.last r)))
    have hleft : Continuous (fun θ : Fin (r+1) → Fiber (E := E) 1 =>
        oneProductFiber r (fun i => θ i.castSucc)) :=
      ih.comp (continuous_pi (fun i => continuous_apply i.castSucc))
    exact (wedgeFiberBilinear r 1).isBoundedBilinearMap.continuous.comp
      (hleft.prodMk (continuous_apply (Fin.last r)))

theorem continuous_twoProductFiber (r : ℕ) :
    Continuous (twoProductFiber (E := E) r) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih =>
    change Continuous (fun B : Fin (r+1) → Fiber (E := E) 2 =>
      degreeCastCLM (show 2*r+2 = 2*(r+1) by omega)
        (wedgeFiber (twoProductFiber r (fun i => B i.castSucc)) (B (Fin.last r))))
    have hleft : Continuous (fun B : Fin (r+1) → Fiber (E := E) 2 =>
        twoProductFiber r (fun i => B i.castSucc)) :=
      ih.comp (continuous_pi (fun i => continuous_apply i.castSucc))
    have hw : Continuous (fun B : Fin (r+1) → Fiber (E := E) 2 =>
        wedgeFiber (twoProductFiber r (fun i => B i.castSucc)) (B (Fin.last r))) := by
      simpa only [Function.comp_def, wedgeFiberBilinear_apply] using
        ((wedgeFiberBilinear (E := E) (2*r) 2).isBoundedBilinearMap.continuous.comp
          (hleft.prodMk (continuous_apply (Fin.last r))))
    simpa only [Function.comp_def] using
      (degreeCastCLM (E := E) (show 2*r+2 = 2*(r+1) by omega)).continuous.comp hw

abbrev Input (n : ℕ) :=
  (Fin (2*n) → ℝ) × (Fin (2*n) → Fiber (E := E) 1) ×
    (Fin (2*n) → Fin (2*n) → Fiber (E := E) 2)

/-- Evaluation of the existing Chern polynomial on constant model-space forms. -/
def angularTermFiber (n : ℕ) (k : Fin n) (z : Input (E := E) n) : Fiber (E := E) (2*n-1) :=
  Chern.angularTerm (E := E) (P := E) n k (fun i _ => z.1 i)
    (fun i _ => z.2.1 i) (fun i j _ => z.2.2 i j) 0

theorem degreeCastForm_euclidean_at {r s : ℕ} (h : r = s)
    (α : Form 𝓘(ℝ,E) E r) (x : E) :
    (show Fiber (E := E) s from degreeCastForm h α x) =
      degreeCastCLM h (show Fiber (E := E) r from α x) := by
  subst s
  rfl

theorem angularTermFiber_formula (n : ℕ) (k : Fin n) (z : Input (E := E) n) :
    angularTermFiber n k z = ∑ σ : Equiv.Perm (Fin (2*n)),
      (↑(Equiv.Perm.sign σ) : ℝ) •
        (z.1 (σ ⟨0, by have := k.isLt; omega⟩) •
          degreeCastCLM (show (2*n-2*k.val-1)+2*k.val=2*n-1 by have := k.isLt; omega)
            (wedgeFiber (oneProductFiber (2*n-2*k.val-1)
              (fun i => z.2.1 (σ (Chern.directionIndex k i))))
              (twoProductFiber k.val (fun j => z.2.2 (σ (Chern.curvatureIndexFirst k j))
                (σ (Chern.curvatureIndexSecond k j)))))) := by
  unfold angularTermFiber Chern.angularTerm
  simp only [Finset.sum_apply, Pi.smul_apply, degreeCastForm_euclidean_at]
  rfl

/-- Exact evaluation bridge to the existing Chern angular form on Euclidean coordinates. -/
theorem angularTerm_evaluation (n : ℕ) (k : Fin n)
    (u : Fin (2*n) → E → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ, E) E 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ, E) E 2) (x : E) :
    Chern.angularTerm n k u θ B x =
      angularTermFiber n k (fun i => u i x, fun i => θ i x, fun i j => B i j x) := by
  rw [angularTermFiber_formula]
  ext v
  simp only [Chern.angularTerm, Finset.sum_apply, Pi.smul_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    degreeCastForm_apply_intrinsic, degreeCastCLM_apply, wedge]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [oneProductFiber_evaluation, twoProductFiber_evaluation]

theorem continuous_angularTermFiber (n : ℕ) (k : Fin n) :
    Continuous (angularTermFiber (E := E) n k) := by
  change Continuous (fun z : Input (E := E) n => angularTermFiber n k z)
  simp_rw [angularTermFiber_formula]
  apply continuous_finset_sum
  intro σ hσ
  have hOne : Continuous (fun z : Input (E := E) n =>
      oneProductFiber (2*n-2*k.val-1) (fun i => z.2.1 (σ (Chern.directionIndex k i)))) :=
    (continuous_oneProductFiber (E := E) _).comp
      (continuous_pi (fun i => (continuous_apply _).comp (continuous_fst.comp continuous_snd)))
  have hTwo : Continuous (fun z : Input (E := E) n =>
      twoProductFiber k.val (fun j => z.2.2 (σ (Chern.curvatureIndexFirst k j))
        (σ (Chern.curvatureIndexSecond k j)))) :=
    (continuous_twoProductFiber (E := E) _).comp (continuous_pi (fun j =>
      (continuous_apply _).comp ((continuous_apply _).comp (continuous_snd.comp continuous_snd))))
  have hW : Continuous (fun z : Input (E := E) n =>
      wedgeFiber
        (oneProductFiber (2*n-2*k.val-1) (fun i => z.2.1 (σ (Chern.directionIndex k i))))
        (twoProductFiber k.val (fun j => z.2.2 (σ (Chern.curvatureIndexFirst k j))
          (σ (Chern.curvatureIndexSecond k j))))) := by
    simpa only [Function.comp_def, wedgeFiberBilinear_apply] using
      (wedgeFiberBilinear (E := E) _ _).isBoundedBilinearMap.continuous.comp (hOne.prodMk hTwo)
  have hCast : Continuous (fun z : Input (E := E) n =>
      degreeCastCLM (show (2*n-2*k.val-1)+2*k.val=2*n-1 by have := k.isLt; omega)
        (wedgeFiber
          (oneProductFiber (2*n-2*k.val-1) (fun i => z.2.1 (σ (Chern.directionIndex k i))))
          (twoProductFiber k.val (fun j => z.2.2 (σ (Chern.curvatureIndexFirst k j))
            (σ (Chern.curvatureIndexSecond k j)))))) := by
    simpa only [Function.comp_def] using
      (degreeCastCLM (E := E) (show (2*n-2*k.val-1)+2*k.val=2*n-1 by have := k.isLt; omega)).continuous.comp hW
  have hScalar : Continuous (fun z : Input (E := E) n => z.1 (σ ⟨0, by have := k.isLt; omega⟩)) :=
    (continuous_apply _).comp continuous_fst
  convert (hScalar.smul hCast).const_smul (↑(Equiv.Perm.sign σ) : ℝ) using 1

instance finiteDimensionalFiber [FiniteDimensional ℝ E] (r : ℕ) :
    FiniteDimensional ℝ (Fiber (E := E) r) := by
  let L : Fiber (E := E) r →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
    (AlternatingMap.toMultilinearMapLM (R := ℝ) (S := ℝ)).comp
      (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ))
  apply Module.Finite.of_injective L
  intro α β h
  ext v
  exact congrArg (fun f : MultilinearMap ℝ (fun _ : Fin r => E) ℝ => f v) h

theorem angularTermFiber_zero_curvature (n : ℕ) (k : Fin n) (hk : 0 < k.val)
    (u : Fin (2*n) → ℝ) (θ : Fin (2*n) → Fiber (E := E) 1) :
    angularTermFiber n k (u, θ, fun _ _ => 0) = 0 := by
  exact congrFun (Chern.angularTerm_zero_curvature (E := E) (P := E) n k hk
    (fun i _ => u i) (fun i _ => θ i)) 0

def angularFormFiber (n : ℕ) (z : Input (E := E) n) : Fiber (E := E) (2*n-1) :=
  ∑ k : Fin n, Chern.angularCoefficient n k.val • angularTermFiber n k z

theorem angularForm_evaluation (n : ℕ)
    (u : Fin (2*n) → E → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ, E) E 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ, E) E 2) (x : E) :
    Chern.angularForm n u θ B x =
      angularFormFiber n (fun i => u i x, fun i => θ i x, fun i j => B i j x) := by
  simp only [Chern.angularForm, angularFormFiber, Finset.sum_apply, Pi.smul_apply,
    angularTerm_evaluation]

theorem continuous_angularFormFiber (n : ℕ) :
    Continuous (angularFormFiber (E := E) n) := by
  change Continuous (fun z : Input (E := E) n =>
    ∑ k : Fin n, Chern.angularCoefficient n k.val • angularTermFiber n k z)
  apply continuous_finset_sum
  intro k hk
  convert (continuous_angularTermFiber (E := E) n k).const_smul
    (Chern.angularCoefficient n k.val) using 1

theorem angularFormFiber_zero_curvature (n : ℕ) (hn : 0 < n)
    (u : Fin (2*n) → ℝ) (θ : Fin (2*n) → Fiber (E := E) 1) :
    angularFormFiber n (u, θ, fun _ _ => 0) = Chern.angularCoefficient n 0 •
      angularTermFiber n ⟨0, hn⟩ (u, θ, fun _ _ => 0) := by
  have h := congrArg (fun α : Form 𝓘(ℝ,E) E (2*n-1) =>
    (show Fiber (E := E) (2*n-1) from α (0:E)))
    (Chern.angularForm_zero_curvature (E := E) (P := E) n hn
      (fun i _ => u i) (fun i _ => θ i))
  change Chern.angularForm n (fun i (_:E) => u i) (fun i (_:E) => θ i)
      (fun _ _ => 0) (0:E) = Chern.angularCoefficient n 0 •
    Chern.angularTerm n ⟨0, hn⟩ (fun i (_:E) => u i) (fun i (_:E) => θ i)
      (fun _ _ => 0) (0:E) at h
  rw [angularForm_evaluation, angularTerm_evaluation] at h
  exact h

open Set Filter Metric

theorem uniform_angularTermFiber {T X : Type*} [TopologicalSpace X]
    [FiniteDimensional ℝ E] {l : Filter T} {s : Set X} (hs : IsCompact s)
    (n : ℕ) (k : Fin n) {z : T → X → Input (E := E) n} {z₀ : X → Input (E := E) n}
    (hz₀ : ContinuousOn z₀ s) (hz : TendstoUniformlyOn z z₀ l s) :
    TendstoUniformlyOn (fun t x => angularTermFiber n k (z t x))
      (fun x => angularTermFiber n k (z₀ x)) l s :=
  AngularScaling.uniform_comp_continuous_of_compact hs hz₀ hz (continuous_angularTermFiber n k)

end AngularPolynomial

namespace AngularPolynomial
open DifferentialForm Set Filter Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def componentDifferential {N : ℕ} (b : OrthonormalBasis (Fin N) ℝ E) (i : Fin N)
    (D : E →L[ℝ] E) : Fiber (E := E) 1 :=
  ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1) ((innerSL ℝ (b i)).comp D)

theorem continuous_componentDifferential {N : ℕ} (b : OrthonormalBasis (Fin N) ℝ E) (i : Fin N) :
    Continuous (componentDifferential b i) := by
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).continuous.comp (continuous_const.clm_comp continuous_id)

/-- Raw geometric data: radius, normalized direction, its derivative, connection and curvature. -/
abbrev RawInput (n : ℕ) := ℝ × E × (E →L[ℝ] E) ×
  (Fin (2*n) → Fin (2*n) → Fiber (E := E) 1) ×
  (Fin (2*n) → Fin (2*n) → Fiber (E := E) 2)

/-- The exact radial factors of the pulled-back actual direction and curvature.
The following expression is polynomial in its raw arguments. -/
def radialAngularInput (n : ℕ) (b : OrthonormalBasis (Fin (2*n)) ℝ E)
    (z : RawInput (E := E) n) : Input (E := E) n :=
  (fun i => inner ℝ (b i) z.2.1,
    fun i => componentDifferential b i z.2.2.1 +
      z.1 • ∑ j, inner ℝ (b j) z.2.1 • z.2.2.2.1 i j,
    fun i j => z.1 ^ 2 • z.2.2.2.2 i j)

theorem continuous_radialAngularInput (n : ℕ) (b : OrthonormalBasis (Fin (2*n)) ℝ E) :
    Continuous (radialAngularInput n b) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    exact (innerSL ℝ (b i)).continuous.comp (continuous_fst.comp continuous_snd)
  · apply Continuous.prodMk
    · apply continuous_pi
      intro i
      apply Continuous.add
      · exact (continuous_componentDifferential b i).comp
          (continuous_fst.comp (continuous_snd.comp continuous_snd))
      · apply Continuous.smul continuous_fst
        apply continuous_finset_sum
        intro j hj
        have hs : Continuous (fun z : RawInput (E := E) n => inner ℝ (b j) z.2.1) :=
          (innerSL ℝ (b j)).continuous.comp (continuous_fst.comp continuous_snd)
        have ha : Continuous (fun z : RawInput (E := E) n => z.2.2.2.1 i j) := by fun_prop
        convert hs.smul ha using 1
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (continuous_fst.pow 2).smul (by fun_prop)

theorem radialAngularInput_zero (n : ℕ) (b : OrthonormalBasis (Fin (2*n)) ℝ E)
    (q : E) (D : E →L[ℝ] E)
    (A : Fin (2*n) → Fin (2*n) → Fiber (E := E) 1)
    (B : Fin (2*n) → Fin (2*n) → Fiber (E := E) 2) :
    radialAngularInput n b (0, q, D, A, B) =
      (fun i => inner ℝ (b i) q, fun i => componentDifferential b i D, fun _ _ => 0) := by
  simp [radialAngularInput]

theorem angularTermFiber_radial_zero (n : ℕ) (b : OrthonormalBasis (Fin (2*n)) ℝ E)
    (k : Fin n) (hk : 0 < k.val) (q : E) (D : E →L[ℝ] E)
    (A : Fin (2*n) → Fin (2*n) → Fiber (E := E) 1)
    (B : Fin (2*n) → Fin (2*n) → Fiber (E := E) 2) :
    angularTermFiber n k (radialAngularInput n b (0, q, D, A, B)) = 0 := by
  rw [radialAngularInput_zero]
  exact angularTermFiber_zero_curvature n k hk _ _

/-- Raw data of the actual normalized rescaled map and the base connection
and curvature coefficients evaluated at the actual rescaled point. -/
def rawRadialInput (n : ℕ) (f : E → E)
    (A : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 1)
    (B : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 2)
    (r : ℝ) (u : E) : RawInput (E := E) n :=
  (r, LocalIndex.normalize (f (r • u)),
    fderiv ℝ (fun v => LocalIndex.normalize (f (r • v))) u, A (r • u), B (r • u))

def rawLinearInput (n : ℕ) (L : E ≃L[ℝ] E)
    (A : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 1)
    (B : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 2) (u : E) : RawInput (E := E) n :=
  (0, LocalIndex.normalize (L u), fderiv ℝ (fun v => LocalIndex.normalize (L v)) u, A 0, B 0)

theorem uniform_rawRadialInput [FiniteDimensional ℝ E] (n : ℕ) {f : E → E}
    (L : E ≃L[ℝ] E) (hf : ContDiffAt ℝ 1 f 0)
    (hL : fderiv ℝ f 0 = L.toContinuousLinearMap) (hzero : f 0 = 0)
    {A : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 1}
    {B : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 2}
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0) :
    TendstoUniformlyOn (rawRadialInput n f A B) (rawLinearInput n L A B)
      (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left inf_le_left
  have hd : HasFDerivAt f L.toContinuousLinearMap 0 :=
    hL ▸ (hf.differentiableAt (by norm_num)).hasFDerivAt
  exact LocalIndex.uniform_product_same_parameter (hr.tendstoUniformlyOn_const _) <|
    LocalIndex.uniform_product_same_parameter (LocalIndex.tendstoUniformlyOn_normalize_rescale L hd hzero) <|
      LocalIndex.uniform_product_same_parameter
        (LocalIndex.tendstoUniformlyOn_fderiv_normalized_linear L hf hL hzero) <|
        LocalIndex.uniform_product_same_parameter
          (LocalIndex.tendstoUniformlyOn_smul_of_continuousAt hA)
          (LocalIndex.tendstoUniformlyOn_smul_of_continuousAt hB)

theorem continuousOn_rawLinearInput [FiniteDimensional ℝ E] (n : ℕ) (L : E ≃L[ℝ] E)
    (A : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 1)
    (B : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 2) :
    ContinuousOn (rawLinearInput n L A B) (sphere (0 : E) 1) := by
  intro u hu
  have hne : L u ≠ 0 := by
    intro h
    exact ne_of_mem_sphere hu one_ne_zero (L.injective (by simpa using h))
  have hN : ContDiffAt ℝ ∞ (fun v => LocalIndex.normalize (L v)) u :=
    (LocalIndex.contDiffAt_normalize hne).comp u L.contDiff.contDiffAt
  exact (continuousAt_const.prodMk (hN.continuousAt.prodMk
    ((hN.continuousAt_fderiv (by simp)).prodMk
      (continuousAt_const.prodMk continuousAt_const)))).continuousWithinAt

/-- Every actual Chern term containing curvature converges uniformly to zero
under a nondegenerate normalized rescaling. The radius factors and boundedness
are proved from the input regularity; no uniform estimates are extra inputs. -/
theorem uniform_mixed_angularTerm_zero [FiniteDimensional ℝ E]
    (n : ℕ) (b : OrthonormalBasis (Fin (2*n)) ℝ E) (k : Fin n) (hk : 0 < k.val)
    {f : E → E} (L : E ≃L[ℝ] E) (hf : ContDiffAt ℝ 1 f 0)
    (hL : fderiv ℝ f 0 = L.toContinuousLinearMap) (hzero : f 0 = 0)
    {A : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 1}
    {B : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 2}
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0) :
    TendstoUniformlyOn (fun r u => angularTermFiber n k
      (radialAngularInput n b (rawRadialInput n f A B r u)))
      (fun _ => (0 : Fiber (E := E) (2*n-1)))
      (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
  have hc := AngularScaling.uniform_comp_continuous_of_compact (isCompact_sphere (0 : E) 1)
    (continuousOn_rawLinearInput n L A B) (uniform_rawRadialInput n L hf hL hzero hA hB)
    ((continuous_angularTermFiber n k).comp (continuous_radialAngularInput n b))
  simpa only [Function.comp_def, rawLinearInput, angularTermFiber_radial_zero n b k hk] using hc

/-- Uniform limit of the whole finite Chern polynomial; all curvature terms
and all connection corrections disappear, leaving its genuine vertical term. -/
theorem uniform_radial_angularForm [FiniteDimensional ℝ E]
    (n : ℕ) (hn : 0 < n) (b : OrthonormalBasis (Fin (2*n)) ℝ E)
    {f : E → E} (L : E ≃L[ℝ] E) (hf : ContDiffAt ℝ 1 f 0)
    (hL : fderiv ℝ f 0 = L.toContinuousLinearMap) (hzero : f 0 = 0)
    {A : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 1}
    {B : E → Fin (2*n) → Fin (2*n) → Fiber (E := E) 2}
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0) :
    TendstoUniformlyOn (fun r u => angularFormFiber n
      (radialAngularInput n b (rawRadialInput n f A B r u)))
      (fun u => Chern.angularCoefficient n 0 • angularTermFiber n ⟨0, hn⟩
        (fun i => inner ℝ (b i) (LocalIndex.normalize (L u)),
         fun i => componentDifferential b i (fderiv ℝ (fun v => LocalIndex.normalize (L v)) u),
         fun _ _ => 0))
      (𝓝[>] (0 : ℝ)) (sphere (0 : E) 1) := by
  have hc := AngularScaling.uniform_comp_continuous_of_compact (isCompact_sphere (0 : E) 1)
    (continuousOn_rawLinearInput n L A B) (uniform_rawRadialInput n L hf hL hzero hA hB)
    ((continuous_angularFormFiber n).comp (continuous_radialAngularInput n b))
  simpa only [Function.comp_def, rawLinearInput, radialAngularInput_zero,
    angularFormFiber_zero_curvature n hn] using hc

end AngularPolynomial
end GaussBonnetChern
