import GaussBonnetChern.PfaffianAlgebra
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # The Pfaffian as a genuine alternating form

The alternating pair polynomial is built from a bilinear form, not supplied
as arbitrary data. Its evaluation agrees with `pfaffianSum`. The top-degree
alternating-map determinant theorem then proves the full basis transformation
law in symbolic even dimension, including singular transformations.
-/

noncomputable section

namespace GaussBonnetChern

open scoped BigOperators
open Module

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

/-- A bilinear pairing viewed as a two-input multilinear map. -/
def pairingMultilinear (A : E →ₗ[R] E →ₗ[R] R) :
    MultilinearMap R (fun _ : Fin 2 ↦ E) R where
  toFun v := A (v 0) (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp

def pairEquiv (n : ℕ) : (Σ _ : Fin n, Fin 2) ≃ Fin (2 * n) :=
  (Equiv.sigmaEquivProd (Fin n) (Fin 2)).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))

@[simp] theorem pairEquiv_first {n : ℕ} (k : Fin n) :
    pairEquiv n ⟨k, 0⟩ = pairFirst k := by
  apply Fin.ext
  simp [pairEquiv, pairFirst, finProdFinEquiv, Nat.mul_comm]

@[simp] theorem pairEquiv_second {n : ℕ} (k : Fin n) :
    pairEquiv n ⟨k, 1⟩ = pairSecond k := by
  apply Fin.ext
  simp [pairEquiv, pairSecond, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- The product of `n` bilinear pairings, bundled as a multilinear map. -/
def pairedMultilinear (n : ℕ) (A : E →ₗ[R] E →ₗ[R] R) :
    MultilinearMap R (fun _ : Fin (2 * n) ↦ E) R :=
  ((MultilinearMap.mkPiAlgebra R (Fin n) R).compMultilinearMap
    (fun _ : Fin n ↦ pairingMultilinear A)).domDomCongr (pairEquiv n)

theorem pairedMultilinear_apply (n : ℕ) (A : E →ₗ[R] E →ₗ[R] R)
    (v : Fin (2 * n) → E) :
    pairedMultilinear n A v = ∏ k : Fin n, A (v (pairFirst k)) (v (pairSecond k)) := by
  simp [pairedMultilinear, MultilinearMap.domDomCongr_apply,
    MultilinearMap.compMultilinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    pairingMultilinear, Sigma.curry]

/-- Alternatizing the pair product gives the unnormalized Pfaffian form. -/
def alternatingPairForm (n : ℕ) (A : E →ₗ[R] E →ₗ[R] R) :
    E [⋀^Fin (2 * n)]→ₗ[R] R :=
  (pairedMultilinear n A).alternatization

theorem alternatingPairForm_apply (n : ℕ) (A : E →ₗ[R] E →ₗ[R] R)
    (v : Fin (2 * n) → E) :
    alternatingPairForm n A v = pfaffianSum n (fun i j ↦ A (v i) (v j)) := by
  simp [alternatingPairForm, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, pairedMultilinear_apply, pfaffianSum,
    Units.smul_def, zsmul_eq_mul]

/-- Full congruence transformation law for the unnormalized Pfaffian over any
commutative ring. It follows from a genuine top-degree alternating form. -/
theorem pfaffianSum_congruence (n : ℕ) (A : E →ₗ[R] E →ₗ[R] R)
    (b : Basis (Fin (2 * n)) R E) (T : E →ₗ[R] E) :
    pfaffianSum n (fun i j ↦ A (T (b i)) (T (b j))) =
      LinearMap.det T * pfaffianSum n (fun i j ↦ A (b i) (b j)) := by
  rw [← alternatingPairForm_apply, ← alternatingPairForm_apply]
  have h := congrArg (fun f : E [⋀^Fin (2 * n)]→ₗ[R] R ↦ f (fun i ↦ T (b i)))
    ((alternatingPairForm n A).eq_smul_basis_det b)
  have hb : b.det (fun i ↦ T (b i)) = LinearMap.det T := by
    change b.det (T ∘ b) = LinearMap.det T
    rw [Basis.det_comp, Basis.det_self, mul_one]
  simpa only [AlternatingMap.smul_apply, smul_eq_mul, hb, mul_comm] using h

theorem pfaffian_congruence {E : Type*} [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (A : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : Basis (Fin (2 * n)) ℝ E) (T : E →ₗ[ℝ] E) :
    pfaffian n (fun i j ↦ A (T (b i)) (T (b j))) =
      LinearMap.det T * pfaffian n (fun i j ↦ A (b i) (b j)) := by
  simp only [pfaffian]
  rw [pfaffianSum_congruence]
  ring

/-- Matrix version of the full congruence law. No invertibility assumption is
made: the identity also covers singular changes of coordinates. -/
theorem pfaffianSum_matrix_congruence (n : ℕ)
    (B P : Matrix (Fin (2 * n)) (Fin (2 * n)) R) :
    pfaffianSum n (P.transpose * B * P) = P.det * pfaffianSum n B := by
  let A := Matrix.toBilin' B
  let T := Matrix.toLin' P
  let b := Pi.basisFun R (Fin (2 * n))
  have h := pfaffianSum_congruence n A b T
  have hm : (A.comp T T).toMatrix' = P.transpose * B * P := by
    simp [A, T, LinearMap.BilinForm.toMatrix'_comp]
  have hl : (fun i j ↦ A (T (b i)) (T (b j))) = P.transpose * B * P := by
    rw [← hm]
    ext i j
    simp [b, LinearMap.BilinForm.toMatrix'_apply, LinearMap.BilinForm.comp_apply]
  have hr : (fun i j ↦ A (b i) (b j)) = B := by
    ext i j
    simp [A, b]
  rw [hl, hr] at h
  simpa [T, LinearMap.det_toMatrix (Pi.basisFun R (Fin (2 * n)))] using h

theorem pfaffian_matrix_congruence (n : ℕ)
    (B P : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) :
    pfaffian n (P.transpose * B * P) = P.det * pfaffian n B := by
  simp only [pfaffian]
  rw [pfaffianSum_matrix_congruence]
  ring

end GaussBonnetChern
