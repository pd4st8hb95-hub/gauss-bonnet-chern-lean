import GaussBonnetChern.AngularPolynomialLimit
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import GaussBonnetChern.AngularBoundaryLimit
import GaussBonnetChern.SphereLinearPullback
import GaussBonnetChern.ScalarDifferential

/-! # The factorial in Chern's purely vertical term

The calculation retains the existing normalized wedge product. First the
ordered product of one-forms is expanded, then the independent frame and
tangent alternations are combined into a determinant with the normal first.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators

namespace GaussBonnetChern.AngularVertical
open DifferentialForm AngularPolynomial

private def leftBlockPerm (r s : ℕ) (τ : Equiv.Perm (Fin r)) :
    Equiv.Perm (Fin (r + s)) :=
  (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)).permCongr
    (Equiv.sumCongr τ (Equiv.refl _))

private theorem leftBlockPerm_sign (r s : ℕ) (τ : Equiv.Perm (Fin r)) :
    permutationSignReal (leftBlockPerm r s τ) = permutationSignReal τ := by
  simp [leftBlockPerm, permutationSignReal]

private theorem signedSum_absorb {N r : ℕ}
    (e : Equiv.Perm (Fin r) → Equiv.Perm (Fin N))
    (he : ∀ τ, permutationSignReal (e τ) = permutationSignReal τ)
    (H : Equiv.Perm (Fin N) → ℝ) :
    (∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin r),
      permutationSignReal σ * permutationSignReal τ * H (σ * e τ)) =
      (r.factorial : ℝ) * ∑ σ : Equiv.Perm (Fin N), permutationSignReal σ * H σ := by
  rw [Finset.sum_comm]
  have hτ (τ : Equiv.Perm (Fin r)) :
      (∑ σ : Equiv.Perm (Fin N),
        permutationSignReal σ * permutationSignReal τ * H (σ * e τ)) =
        ∑ σ : Equiv.Perm (Fin N), permutationSignReal σ * H σ := by
    simp_rw [← he τ, ← permutationSignReal_mul]
    exact Equiv.sum_comp (Equiv.mulRight (e τ)) (fun σ => permutationSignReal σ * H σ)
  simp_rw [hτ]
  simp [Fintype.card_perm]

private theorem signedSum_left {E : Type*} (r s : ℕ)
    (h : (Fin r → E) → ℝ) (g : (Fin s → E) → ℝ) (v : Fin (r + s) → E) :
    (∑ σ : Equiv.Perm (Fin (r + s)), permutationSignReal σ *
      ((∑ τ : Equiv.Perm (Fin r), permutationSignReal τ *
        h (fun i => v (σ (Fin.castAdd s (τ i))))) *
        g (fun i => v (σ (Fin.natAdd r i))))) =
      (r.factorial : ℝ) * ∑ σ : Equiv.Perm (Fin (r + s)), permutationSignReal σ *
        (h (fun i => v (σ (Fin.castAdd s i))) * g (fun i => v (σ (Fin.natAdd r i)))) := by
  let H : Equiv.Perm (Fin (r + s)) → ℝ := fun σ =>
    h (fun i => v (σ (Fin.castAdd s i))) * g (fun i => v (σ (Fin.natAdd r i)))
  have ha := signedSum_absorb (leftBlockPerm r s) (leftBlockPerm_sign r s) H
  convert ha using 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  simp [H, leftBlockPerm, Equiv.Perm.mul_apply, mul_assoc]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact expansion of the actual iterated normalized wedge of one-forms. -/
theorem oneProductFiber_apply (r : ℕ) (θ : Fin r → Fiber (E := E) 1) (v : Fin r → E) :
    oneProductFiber r θ v = ∑ σ : Equiv.Perm (Fin r), permutationSignReal σ *
      ∏ i : Fin r, θ i (fun _ : Fin 1 => v (σ i)) := by
  induction r with
  | zero =>
    simp [oneProductFiber, Chern.oneFormProduct, ofFunction, permutationSignReal]
    rfl
  | succ r ih =>
    change wedgeFiber (oneProductFiber r (fun i => θ i.castSucc)) (θ (Fin.last r)) v = _
    rw [wedgeFiber_apply_realSign]
    simp_rw [ih]
    let h : (Fin r → E) → ℝ := fun w => ∏ i : Fin r, θ i.castSucc (fun _ : Fin 1 => w i)
    let g : (Fin 1 → E) → ℝ := fun w => θ (Fin.last r) w
    have hs := signedSum_left r 1 h g v
    have hcast (i : Fin r) : Fin.castAdd 1 i = i.castSucc := by
      apply Fin.ext
      rfl
    have hlast (σ : Equiv.Perm (Fin (r+1))) :
        θ (Fin.last r) (fun j => v (σ (Fin.natAdd r j))) =
          θ (Fin.last r) (fun _ : Fin 1 => v (σ (Fin.last r))) := by
      congr 1
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rfl
    have heq : (∑ σ : Equiv.Perm (Fin (r+1)), permutationSignReal σ *
        ((∑ τ : Equiv.Perm (Fin r), permutationSignReal τ *
          ∏ i : Fin r, θ i.castSucc (fun _ : Fin 1 => v (σ (Fin.castAdd 1 (τ i))))) *
          θ (Fin.last r) (fun j => v (σ (Fin.natAdd r j))))) =
        (r.factorial : ℝ) * ∑ σ : Equiv.Perm (Fin (r+1)), permutationSignReal σ *
          ∏ i : Fin (r+1), θ i (fun _ : Fin 1 => v (σ i)) := by
      simpa only [h, g, Fin.prod_univ_castSucc, hlast, hcast] using hs
    rw [heq]
    simp only [Nat.factorial_one, Nat.cast_one, mul_one]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr r.factorial_ne_zero), one_mul]

private def fixFirstPerm {r : ℕ} (τ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r+1)) :=
  Equiv.Perm.decomposeFin.symm (0, τ)

@[simp] private theorem fixFirstPerm_zero {r : ℕ} (τ : Equiv.Perm (Fin r)) :
    fixFirstPerm τ 0 = 0 := by simp [fixFirstPerm]

@[simp] private theorem fixFirstPerm_succ {r : ℕ} (τ : Equiv.Perm (Fin r)) (i : Fin r) :
    fixFirstPerm τ i.succ = (τ i).succ := by simp [fixFirstPerm]

@[simp] private theorem sign_fixFirstPerm {r : ℕ} (τ : Equiv.Perm (Fin r)) :
    permutationSignReal (fixFirstPerm τ) = permutationSignReal τ := by
  simp [fixFirstPerm, permutationSignReal]

/-- The leading scalar coordinate occupies the first determinant column. -/
def verticalMatrix (r : ℕ) (u : Fin (r+1) → ℝ)
    (θ : Fin (r+1) → Fiber (E := E) 1) (v : Fin r → E) :
    Matrix (Fin (r+1)) (Fin (r+1)) ℝ :=
  fun i => Fin.cons (u i) (fun j => θ i (fun _ : Fin 1 => v j))

theorem verticalMatrix_det_permute (r : ℕ) (u : Fin (r+1) → ℝ)
    (θ : Fin (r+1) → Fiber (E := E) 1) (v : Fin r → E) (τ : Equiv.Perm (Fin r)) :
    Matrix.det (verticalMatrix r u θ (v ∘ τ)) =
      permutationSignReal τ * Matrix.det (verticalMatrix r u θ v) := by
  have hM : verticalMatrix r u θ (v ∘ τ) =
      (verticalMatrix r u θ v).submatrix id (fixFirstPerm τ) := by
    ext i j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [verticalMatrix, Function.comp_def]
  rw [hM, Matrix.det_permute']
  simp [permutationSignReal, fixFirstPerm, Equiv.Perm.decomposeFin.symm_sign]

/-- Full frame alternation of the actual vertical wedge is `r!` times the
normal-first determinant, including `r = 0`. -/
theorem vertical_alternation_eq_factorial_det (r : ℕ) (u : Fin (r+1) → ℝ)
    (θ : Fin (r+1) → Fiber (E := E) 1) (v : Fin r → E) :
    (∑ σ : Equiv.Perm (Fin (r+1)), permutationSignReal σ * u (σ 0) *
      oneProductFiber r (fun i => θ (σ i.succ)) v) =
      (r.factorial : ℝ) * Matrix.det (verticalMatrix r u θ v) := by
  simp_rw [oneProductFiber_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner (τ : Equiv.Perm (Fin r)) :
      (∑ σ : Equiv.Perm (Fin (r+1)), permutationSignReal σ * u (σ 0) *
        (permutationSignReal τ * ∏ i : Fin r, θ (σ i.succ) (fun _ : Fin 1 => v (τ i)))) =
      permutationSignReal τ * Matrix.det (verticalMatrix r u θ (v ∘ τ)) := by
    rw [Matrix.det_apply', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Fin.prod_univ_succ]
    simp only [verticalMatrix, Fin.cons_zero, Fin.cons_succ, Function.comp_apply,
      permutationSignReal]
    ring
  simp_rw [hinner, verticalMatrix_det_permute, ← mul_assoc, permutationSignReal_sq, one_mul]
  simp [Fintype.card_perm]

/-- Exact zero-curvature-degree evaluation before relabeling the ambient dimension. -/
theorem angularTermFiber_zero_apply (n : ℕ) (hn : 0 < n)
    (u : Fin (2*n) → ℝ) (θ : Fin (2*n) → Fiber (E := E) 1)
    (B : Fin (2*n) → Fin (2*n) → Fiber (E := E) 2) (v : Fin (2*n-1) → E) :
    angularTermFiber n ⟨0, hn⟩ (u, θ, B) v =
      ∑ σ : Equiv.Perm (Fin (2*n)), permutationSignReal σ *
        u (σ ⟨0, by omega⟩) *
          oneProductFiber (2*n-1) (fun i => θ (σ (Chern.directionIndex ⟨0, hn⟩ i))) v := by
  rw [angularTermFiber_formula]
  have htwo (t : Fin 0 → Fiber (E := E) 2) :
      twoProductFiber 0 t = ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1 := by
    rfl
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    Fin.val_zero, Nat.mul_zero, Nat.sub_zero, Nat.add_zero, degreeCastCLM_apply,
    htwo, wedgeFiber_const_right, finCongr_refl, Equiv.refl_apply,
    one_mul, Function.comp_def, smul_eq_mul, permutationSignReal, mul_assoc]
  apply Finset.sum_congr rfl
  intro σ _
  apply congrArg (fun t : ℝ => (↑(Equiv.Perm.sign σ) : ℝ) * (u (σ ⟨0, by omega⟩) * t))
  change wedgeFiber
      (oneProductFiber (2*n-1) (fun i => θ (σ (Chern.directionIndex ⟨0, hn⟩ i))))
      (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1) v = _
  exact (wedgeFiber_const_right (E := E)
    (oneProductFiber (2*n-1) (fun i => θ (σ (Chern.directionIndex ⟨0, hn⟩ i)))) 1 v).trans
      (one_mul _)

def evenSuccEquiv (n : ℕ) (hn : 0 < n) : Fin ((2*n-1)+1) ≃ Fin (2*n) :=
  finCongr (by omega)

/-- `Φ₀` of the actual Chern polynomial equals the factorial times the
normal-first determinant. There is no restriction to low dimensions. -/
theorem angularTermFiber_zero_eq_factorial_det (n : ℕ) (hn : 0 < n)
    (u : Fin (2*n) → ℝ) (θ : Fin (2*n) → Fiber (E := E) 1)
    (B : Fin (2*n) → Fin (2*n) → Fiber (E := E) 2) (v : Fin (2*n-1) → E) :
    angularTermFiber n ⟨0, hn⟩ (u, θ, B) v =
      ((2*n-1).factorial : ℝ) * Matrix.det
        (verticalMatrix (2*n-1) (u ∘ evenSuccEquiv n hn) (θ ∘ evenSuccEquiv n hn) v) := by
  rw [angularTermFiber_zero_apply]
  let e := evenSuccEquiv n hn
  have h0 : e 0 = (⟨0, by omega⟩ : Fin (2*n)) := by apply Fin.ext; rfl
  have hi (i : Fin (2*n-1)) : e i.succ = Chern.directionIndex ⟨0, hn⟩ i := by
    apply Fin.ext
    rfl
  let H : Equiv.Perm (Fin (2*n)) → ℝ := fun σ => permutationSignReal σ *
    u (σ ⟨0, by omega⟩) * oneProductFiber (2*n-1)
      (fun i => θ (σ (Chern.directionIndex ⟨0, hn⟩ i))) v
  change (∑ σ, H σ) = _
  rw [show (∑ σ, H σ) = ∑ τ, H (e.permCongr τ) from (e.permCongr.sum_comp H).symm]
  have heq (τ : Equiv.Perm (Fin ((2*n-1)+1))) :
      H (e.permCongr τ) = permutationSignReal τ * (u ∘ e) (τ 0) *
        oneProductFiber (2*n-1) (fun i => (θ ∘ e) (τ i.succ)) v := by
    unfold H
    rw [permutationSignReal_permCongr]
    simp only [Equiv.permCongr_apply, ← h0, ← hi, Equiv.symm_apply_apply, Function.comp_apply]
  simp_rw [heq]
  exact vertical_alternation_eq_factorial_det (2*n-1) (u ∘ e) (θ ∘ e) v

end GaussBonnetChern.AngularVertical



namespace GaussBonnetChern.AngularVertical
open DifferentialForm AngularPolynomial Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- In orthonormal coordinates the genuine vertical Chern term is the
normal-first ambient volume determinant, with its exact factorial. -/
theorem angularTermFiber_component_zero (n : ℕ) (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2*n)) ℝ E) (q : E) (D : E →L[ℝ] E)
    (B : Fin (2*n) → Fin (2*n) → Fiber (E := E) 2) (v : Fin (2*n-1) → E) :
    angularTermFiber n ⟨0, hn⟩
      (fun i => inner ℝ (b i) q, fun i => componentDifferential b i D, B) v =
      ((2*n-1).factorial : ℝ) *
        (b.reindex (evenSuccEquiv n hn).symm).toBasis.det (Fin.cons q (fun i => D (v i))) := by
  rw [angularTermFiber_zero_eq_factorial_det, Basis.det_apply]
  congr 1
  apply congrArg Matrix.det
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [verticalMatrix, Fin.cons_zero, Function.comp_apply, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.reindex_apply, Equiv.symm_symm]
  · simp only [verticalMatrix, Fin.cons_succ, Function.comp_apply, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.reindex_apply, Equiv.symm_symm, componentDifferential,
      ContinuousAlternatingMap.ofSubsingleton_apply_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]

end GaussBonnetChern.AngularVertical

namespace GaussBonnetChern.AngularVertical
open DifferentialForm AngularPolynomial AngularBoundary Module MeasureTheory Metric Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (n : ℕ) (hn : 0 < n) [Fact (finrank ℝ E = (2*n-1)+1)]

local instance sphereEuclideanTangentNormedAddCommGroup (x : E) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x) :=
  inferInstanceAs (NormedAddCommGroup E)

local instance sphereEuclideanTangentNormedSpace (x : E) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ,E) x) :=
  inferInstanceAs (NormedSpace ℝ E)

local instance sphereEuclideanTangentInnerProductSpace (x : E) :
    InnerProductSpace ℝ (TangentSpace 𝓘(ℝ,E) x) :=
  inferInstanceAs (InnerProductSpace ℝ E)

/-- The purely vertical Chern polynomial restricted by the actual sphere inclusion. -/
def verticalSphereForm (b : OrthonormalBasis (Fin (2*n)) ℝ E) :
    Form (𝓡 (2*n-1)) (sphere (0 : E) 1) (2*n-1) :=
  ambientSphereRestriction (fun u => angularTermFiber n ⟨0, hn⟩
    (fun i => inner ℝ (b i) (u : E),
     fun i => componentDifferential b i (ContinuousLinearMap.id ℝ E), fun _ _ => 0))

/-- Exact all-dimensional form identity underlying the fiber normalization. -/
theorem verticalSphereForm_eq_factorial_volume (b : OrthonormalBasis (Fin (2*n)) ℝ E) :
    verticalSphereForm n hn b = ((2*n-1).factorial : ℝ) •
      sphereVolumeForm (b.reindex (evenSuccEquiv n hn).symm) := by
  funext u
  ext v
  change angularTermFiber n ⟨0, hn⟩
      (fun i => inner ℝ (b i) (u : E),
       fun i => componentDifferential b i (ContinuousLinearMap.id ℝ E), fun _ _ => 0)
      (fun i => mvfderiv (𝓡 (2*n-1)) ((↑) : sphere (0 : E) 1 → E) u (v i)) = _
  rw [angularTermFiber_component_zero]
  rfl

/-- The actual scalar differentials of sphere coordinates give exactly the
same vertical polynomial as ambient restriction. -/
theorem sphere_angularTerm_zero_eq_verticalSphereForm
    (b : OrthonormalBasis (Fin (2*n)) ℝ E) :
    Chern.angularTerm n ⟨0, hn⟩
      (fun i (u : sphere (0:E) 1) => inner ℝ (b i) (u:E))
      (fun i => scalarDifferential (E := EuclideanSpace ℝ (Fin (2*n-1)))
        (fun u : sphere (0:E) 1 => inner ℝ (b i) (u:E)))
      (fun _ _ => 0) = verticalSphereForm n hn b := by
  let ι : sphere (0:E) 1 → E := (↑)
  let U : Fin (2*n) → E → ℝ := fun i x => inner ℝ (b i) x
  let Θ : Fin (2*n) → Form 𝓘(ℝ,E) E 1 := fun i x =>
    (componentDifferential (E := E) b i (ContinuousLinearMap.id ℝ E)).compContinuousLinearMap
      (NormedSpace.fromTangentSpace x).toContinuousLinearMap
  let K : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) E 2 := fun _ _ => 0
  have hθ (i : Fin (2*n)) :
      scalarDifferential (E := EuclideanSpace ℝ (Fin (2*n-1)))
        (fun u : sphere (0:E) 1 => inner ℝ (b i) (u:E)) =
        pullback (I := 𝓡 (2*n-1)) (I' := 𝓘(ℝ,E)) ι (Θ i) := by
    funext u
    ext v
    have hlin : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ) (innerSL ℝ (b i)) (u:E) :=
      ((innerSL ℝ (b i)).contMDiffAt (n := ∞)).mdifferentiableAt (by simp)
    have hc := mvfderiv_comp u
      hlin
      ((contMDiff_coe_sphere (n := 2*n-1) (m := ∞) u).mdifferentiableAt (by simp))
    have hi : mvfderiv 𝓘(ℝ,E) (innerSL ℝ (b i)) (u:E) = innerSL ℝ (b i) := by
      rw [mvfderiv_eq_fderiv]
      exact (innerSL ℝ (b i)).hasFDerivAt.fderiv
    simp only [scalarDifferential_apply, pullback_apply, Θ, componentDifferential,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.ofSubsingleton_apply_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply]
    exact congrArg (fun D => D (v 0)) (hc.trans (by rw [hi]))
  have hB : (fun i j => pullback (I := 𝓡 (2*n-1)) (I' := 𝓘(ℝ,E)) ι (K i j)) =
      (fun (_ _:Fin (2*n)) => (0 : Form (𝓡 (2*n-1)) (sphere (0:E) 1) 2)) := by
    funext i j
    funext u
    ext v
    rfl
  have hU : (fun i => U i ∘ ι) = (fun i (u : sphere (0:E) 1) => inner ℝ (b i) (u:E)) := rfl
  have hp := Chern.pullback_angularTerm
    (E := EuclideanSpace ℝ (Fin (2*n-1))) (F := E) (P := sphere (0:E) 1) (Q := E)
    ι n ⟨0, hn⟩ U Θ K
  rw [hU, hB] at hp
  simp_rw [← hθ] at hp
  refine hp.symm.trans ?_
  funext u
  ext v
  change Chern.angularTerm n ⟨0, hn⟩ U Θ K (u:E)
      (fun j => mvfderiv (𝓡 (2*n-1)) ι u (v j)) = _
  rw [angularTerm_evaluation]
  rfl

/-- Chern's genuine sphere-coordinate `Φ₀` is the exact factorial times
the outward normal-first sphere volume form in every positive dimension. -/
theorem sphere_angularTerm_zero_eq_factorial_volume
    (b : OrthonormalBasis (Fin (2*n)) ℝ E) :
    Chern.angularTerm n ⟨0, hn⟩
      (fun i (u : sphere (0:E) 1) => inner ℝ (b i) (u:E))
      (fun i => scalarDifferential (E := EuclideanSpace ℝ (Fin (2*n-1)))
        (fun u : sphere (0:E) 1 => inner ℝ (b i) (u:E)))
      (fun _ _ => 0) = ((2*n-1).factorial : ℝ) •
        sphereVolumeForm (b.reindex (evenSuccEquiv n hn).symm) := by
  rw [sphere_angularTerm_zero_eq_verticalSphereForm, verticalSphereForm_eq_factorial_volume]

/-- The vertical limit with the actual normalized invertible linear map. -/
def verticalLinearSphereForm (b : OrthonormalBasis (Fin (2*n)) ℝ E) (L : E ≃L[ℝ] E) :
    Form (𝓡 (2*n-1)) (sphere (0 : E) 1) (2*n-1) :=
  ambientSphereRestriction (fun u => angularTermFiber n ⟨0, hn⟩
    (fun i => inner ℝ (b i) (LocalIndex.normalize (L u)),
     fun i => componentDifferential b i (fderiv ℝ (fun v => LocalIndex.normalize (L v)) u),
     fun _ _ => 0))

theorem verticalLinearSphereForm_eq_pullback (b : OrthonormalBasis (Fin (2*n)) ℝ E)
    (L : E ≃L[ℝ] E) :
    verticalLinearSphereForm n hn b L = ((2*n-1).factorial : ℝ) •
      pullback (I := 𝓡 (2*n-1)) (I' := 𝓡 (2*n-1)) (sphereNormalizedLinearMap L)
        (sphereVolumeForm (b.reindex (evenSuccEquiv n hn).symm)) := by
  funext u
  ext v
  change angularTermFiber n ⟨0, hn⟩
      (fun i => inner ℝ (b i) (LocalIndex.normalize (L u)),
       fun i => componentDifferential b i (fderiv ℝ (fun z => LocalIndex.normalize (L z)) u),
       fun _ _ => 0)
      (fun i => mvfderiv (𝓡 (2*n-1)) ((↑) : sphere (0 : E) 1 → E) u (v i)) = _
  rw [angularTermFiber_component_zero]
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    pullback_apply, sphereVolumeForm_apply, sphereNormalizedLinearMap_coe,
    sphereNormalizedLinearMap_derivative]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem verticalLinearSphereForm_integral (b : OrthonormalBasis (Fin (2*n)) ℝ E)
    (L : E ≃L[ℝ] E) :
    sphereFormIntegral (b.reindex (evenSuccEquiv n hn).symm) (verticalLinearSphereForm n hn b L) =
      ((2*n-1).factorial : ℝ) *
        (Real.sign (LinearMap.det L.toLinearMap) * (volume : Measure E).toSphere.real univ) := by
  rw [verticalLinearSphereForm_eq_pullback, sphereFormIntegral_smul,
    sphereFormIntegral_normalizedLinear_pullback]

end GaussBonnetChern.AngularVertical


namespace GaussBonnetChern.AngularVertical
open DifferentialForm AngularPolynomial AngularBoundary Module MeasureTheory Metric Set Filter
open scoped ContDiff Topology

variable (n : ℕ) [Fact (0 < n)]

local instance evenModelSphereDimension : Fact (finrank ℝ (Model n) = (2*n-1)+1) :=
  ⟨by
    simp only [Model, finrank_euclideanSpace, Fintype.card_fin]
    have hn : 0 < n := Fact.out
    omega⟩

/-- The actual model angular polynomial on a rescaled sphere, restricted by
the genuine derivative of the sphere inclusion. Geometric frame pullback
identification is deliberately kept as a separate equality. -/
def radialBoundaryModelForm (b : OrthonormalBasis (Fin (2*n)) ℝ (Model n))
    (f : Model n → Model n)
    (A : Model n → Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 1)
    (B : Model n → Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 2) (r : ℝ) :
    Form (𝓡 (2*n-1)) (sphere (0 : Model n) 1) (2*n-1) :=
  ambientSphereRestriction (fun u => angularFormFiber n
    (radialAngularInput n b (rawRadialInput n f A B r (u : Model n))))

/-- The polar integral of the vertical limiting polynomial is exactly the
local determinant sign, with Chern's full-dimensional normalization. -/
theorem normalized_verticalLinearSphereForm_integral
    (b : OrthonormalBasis (Fin (2*n)) ℝ (Model n)) (L : Model n ≃L[ℝ] Model n) :
    sphereFormIntegral (b.reindex (evenSuccEquiv n Fact.out).symm)
      (Chern.angularCoefficient n 0 • verticalLinearSphereForm n Fact.out b L) =
      Real.sign (LinearMap.det L.toLinearMap) := by
  rw [sphereFormIntegral_smul, verticalLinearSphereForm_integral]
  calc
    _ = Real.sign (LinearMap.det L.toLinearMap) *
        (Chern.angularCoefficient n 0 * ((2*n-1).factorial : ℝ) *
          (volume : Measure (Model n)).toSphere.real univ) := by ring
    _ = _ := by rw [Chern.angularCoefficient_mul_sphereMeasure n Fact.out, mul_one]

/-- Analytic model limit after smoothness of the actual pulled-back forms
has been established. The geometric construction must supply that smoothness
and identify its pullback with `radialBoundaryModelForm`; this statement does
not silently assume either geometric bridge. -/
theorem tendsto_radialBoundaryModelIntegral_of_smooth
    (b : OrthonormalBasis (Fin (2*n)) ℝ (Model n))
    {f : Model n → Model n} (L : Model n ≃L[ℝ] Model n) (hf : ContDiffAt ℝ 1 f 0)
    (hL : fderiv ℝ f 0 = L.toContinuousLinearMap) (hzero : f 0 = 0)
    {A : Model n → Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 1}
    {B : Model n → Fin (2*n) → Fin (2*n) → Fiber (E := Model n) 2}
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0)
    (hSmooth : ∀ᶠ r in 𝓝[>] (0 : ℝ), IsSmooth (radialBoundaryModelForm n b f A B r)) :
    Tendsto (fun r => sphereFormIntegral (b.reindex (evenSuccEquiv n Fact.out).symm)
      (radialBoundaryModelForm n b f A B r)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sign (LinearMap.det L.toLinearMap))) := by
  let γ : sphere (0 : Model n) 1 → Fiber (E := Model n) (2*n-1) := fun u =>
    Chern.angularCoefficient n 0 • angularTermFiber n ⟨0, Fact.out⟩
      (fun i => inner ℝ (b i) (LocalIndex.normalize (L u)),
       fun i => componentDifferential b i
         (fderiv ℝ (fun v => LocalIndex.normalize (L v)) u), fun _ _ => 0)
  have hγ : ambientSphereRestriction γ =
      Chern.angularCoefficient n 0 • verticalLinearSphereForm n Fact.out b L := by
    funext u
    ext v
    rfl
  have hγSmooth : IsSmooth (ambientSphereRestriction γ) := by
    rw [hγ, verticalLinearSphereForm_eq_pullback]
    exact (((isSmooth_sphereVolumeForm _).pullback (sphereNormalizedLinearMap L)
      (contMDiff_sphereNormalizedLinearMap L)).const_smul _).const_smul _
  have hconv := uniform_radial_angularForm n Fact.out b L hf hL hzero hA hB
  have hsphere : TendstoUniformlyOn
      (fun r (u : sphere (0 : Model n) 1) => angularFormFiber n
        (radialAngularInput n b (rawRadialInput n f A B r (u : Model n)))) γ
      (𝓝[>] (0 : ℝ)) univ :=
    (hconv.comp ((↑) : sphere (0 : Model n) 1 → Model n)).mono (fun u hu => u.property)
  have ht := tendsto_sphereFormIntegral_of_uniform_ambient
    (b.reindex (evenSuccEquiv n Fact.out).symm) hSmooth hγSmooth hsphere
  rw [hγ, normalized_verticalLinearSphereForm_integral] at ht
  exact ht

end GaussBonnetChern.AngularVertical
