import GaussBonnetChern.ChernAngularAlgebra

/-! # Algebraic identities for Chern's unit-sphere recurrence

The trace of the rank-one map `v ↦ U(v) • u` is `U(u)`. Applying the
corresponding insertion identity to the actual alternating Chern polynomials
is the algebraic mechanism behind the unit-sphere contraction coefficient.
No connection structure equation or transgression identity is assumed.
-/

noncomputable section
open scoped BigOperators Manifold
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false

section RankOneInsertion
variable {ι W V : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup V] [Module ℝ V]

/-- Replacing a basis vector in a top alternating map reads precisely that coordinate. -/
theorem alternating_basis_update (A : W [⋀^ι]→ₗ[ℝ] V)
    (b : Basis ι ℝ W) (i : ι) (u : W) :
    A (Function.update b i u) = b.repr u i • A b := by
  classical
  conv_lhs => rw [← b.sum_repr u]
  rw [A.map_update_sum]
  simp_rw [A.map_update_smul]
  rw [Finset.sum_eq_single i]
  · rw [Function.update_eq_self]
  · intro j _ hji
    rw [A.map_update_self b hji.symm, smul_zero]
  · simp

/-- Inserting a rank-one operator in every frame slot has its actual trace
as coefficient. This identity holds for any module-valued alternating map. -/
theorem alternating_rankOne_sum (A : W [⋀^ι]→ₗ[ℝ] V)
    (b : Basis ι ℝ W) (U : W →ₗ[ℝ] ℝ) (u : W) :
    (∑ i, A (Function.update b i (U (b i) • u))) = U u • A b := by
  simp_rw [A.map_update_smul, alternating_basis_update, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  calc
    (∑ i, U (b i) * b.repr u i) = ∑ i, b.repr u i * U (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = U (∑ i, b.repr u i • b i) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
    _ = U u := by rw [b.sum_repr]

/-- A top alternating expression annihilating the unit direction in every
slot vanishes; the normalization hypothesis is the actual scalar pairing. -/
theorem alternating_zero_of_rankOne (A : W [⋀^ι]→ₗ[ℝ] V)
    (b : Basis ι ℝ W) (U : W →ₗ[ℝ] ℝ) (u : W) (hu : U u = 1)
    (hA : ∀ i, A (Function.update b i u) = 0) : A b = 0 := by
  have h := alternating_rankOne_sum A b U u
  simp only [A.map_update_smul, hA, smul_zero, Finset.sum_const_zero, hu, one_smul] at h
  exact h.symm

/-- The complete infinitesimal determinant law, with its diagonal trace
written in the given basis. -/
theorem alternating_endomorphism_sum (A : W [⋀^ι]→ₗ[ℝ] V)
    (b : Basis ι ℝ W) (T : W →ₗ[ℝ] W) :
    (∑ i, A (Function.update b i (T (b i)))) =
      (∑ i, b.repr (T (b i)) i) • A b := by
  simp_rw [alternating_basis_update]
  exact (Finset.sum_smul ..).symm
end RankOneInsertion

section AlternatizationInsertion
variable {ι W V : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup V] [Module ℝ V]

/-- Apply a linear operator in exactly one input slot of a multilinear expression. -/
def slotInsertion (f : MultilinearMap ℝ (fun _ : ι ↦ W) V)
    (T : W →ₗ[ℝ] W) (i : ι) : MultilinearMap ℝ (fun _ : ι ↦ W) V :=
  f.compLinearMap (Function.update (fun _ ↦ LinearMap.id) i T)

@[simp] theorem slotInsertion_apply (f : MultilinearMap ℝ (fun _ : ι ↦ W) V)
    (T : W →ₗ[ℝ] W) (i : ι) (w : ι → W) :
    slotInsertion f T i w = f (Function.update w i (T (w i))) := by
  unfold slotInsertion
  rw [MultilinearMap.compLinearMap_apply]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp [Function.update_of_ne hj]

/-- Summed slot insertion commutes with actual alternatization. -/
theorem alternatization_sum_slotInsertion
    (f : MultilinearMap ℝ (fun _ : ι ↦ W) V) (T : W →ₗ[ℝ] W) (w : ι → W) :
    (∑ i, (slotInsertion f T i).alternatization w) =
      ∑ i, f.alternatization (Function.update w i (T (w i))) := by
  simp only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    slotInsertion_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  calc
    _ = ∑ i, Equiv.Perm.sign σ •
      f ((Function.update w (σ i) (T (w (σ i)))) ∘ σ) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      rw [Function.update_comp_equiv, Equiv.symm_apply_apply]
      rfl
    _ = _ := Equiv.sum_comp σ (fun i ↦ Equiv.Perm.sign σ •
      f ((Function.update w i (T (w i))) ∘ σ))

/-- The all-slot rank-one insertion identity for an unalternated polynomial.
This transfers the unit-direction trace identity to its concrete factor slots. -/
theorem alternatization_rankOne_sum
    (f : MultilinearMap ℝ (fun _ : ι ↦ W) V) (b : Basis ι ℝ W)
    (U : W →ₗ[ℝ] ℝ) (u : W) :
    (∑ i, (slotInsertion f (U.smulRight u) i).alternatization b) =
      U u • f.alternatization b := by
  rw [alternatization_sum_slotInsertion]
  exact alternating_rankOne_sum f.alternatization b U u

/-- Full endomorphism insertion commutes with alternation and gives its trace. -/
theorem alternatization_endomorphism_sum
    (f : MultilinearMap ℝ (fun _ : ι ↦ W) V) (b : Basis ι ℝ W)
    (T : W →ₗ[ℝ] W) :
    (∑ i, (slotInsertion f T i).alternatization b) =
      (∑ i, b.repr (T (b i)) i) • f.alternatization b := by
  rw [alternatization_sum_slotInsertion]
  exact alternating_endomorphism_sum f.alternatization b T

/-- Trace-zero frame variations cancel exactly in the alternating polynomial. -/
theorem alternatization_endomorphism_sum_zero
    (f : MultilinearMap ℝ (fun _ : ι ↦ W) V) (b : Basis ι ℝ W)
    (T : W →ₗ[ℝ] W) (hT : ∑ i, b.repr (T (b i)) i = 0) :
    (∑ i, (slotInsertion f T i).alternatization b) = 0 := by
  rw [alternatization_endomorphism_sum, hT, zero_smul]
end AlternatizationInsertion
section AlternatizationPermutation
variable {ι W V : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup V] [Module ℝ V]

/-- Permuting the unalternated input slots has exactly the permutation sign
after alternatization, for module-valued polynomials. -/
theorem alternatization_domPerm (f : MultilinearMap ℝ (fun _ : ι ↦ W) V)
    (τ : Equiv.Perm ι) :
    (f.domDomCongr τ).alternatization = Equiv.Perm.sign τ • f.alternatization := by
  ext w
  simp only [AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  let H : Equiv.Perm ι → V := fun σ ↦ Equiv.Perm.sign σ • f (w ∘ σ)
  change (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f ((w ∘ σ) ∘ τ)) =
    Equiv.Perm.sign τ • ∑ σ : Equiv.Perm ι, H σ
  rw [← Equiv.sum_comp (Equiv.mulRight τ) H, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  change Equiv.Perm.sign σ • f ((w ∘ σ) ∘ τ) =
    Equiv.Perm.sign τ • (Equiv.Perm.sign (σ * τ) • f (w ∘ (σ * τ)))
  rw [Equiv.Perm.sign_mul, mul_smul,
    smul_comm (Equiv.Perm.sign τ) (Equiv.Perm.sign σ),
    ← mul_smul (Equiv.Perm.sign τ) (Equiv.Perm.sign τ), Int.units_mul_self, one_smul]
  rfl

/-- Transport an insertion slot through a genuine permutation of frame inputs. -/
theorem slotInsertion_domPerm (f : MultilinearMap ℝ (fun _ : ι ↦ W) V)
    (T : W →ₗ[ℝ] W) (i : ι) (τ : Equiv.Perm ι) :
    slotInsertion (f.domDomCongr τ) T i =
      (slotInsertion f T (τ.symm i)).domDomCongr τ := by
  ext w
  simp only [slotInsertion_apply, MultilinearMap.domDomCongr_apply]
  congr 1
  change Function.update w i (T (w i)) ∘ τ =
    Function.update (w ∘ τ) (τ.symm i) (T (w (τ (τ.symm i))))
  exact (Function.update_comp_equiv w τ i (T (w i))).trans
    (congrArg (Function.update (w ∘ τ) (τ.symm i))
      (congrArg (fun j ↦ T (w j)) (τ.apply_symm_apply i).symm))

@[simp] theorem slotInsertion_sign_smul
    (f : MultilinearMap ℝ (fun _ : ι ↦ W) V) (T : W →ₗ[ℝ] W) (i : ι) (s : ℤˣ) :
    slotInsertion (s • f) T i = s • slotInsertion f T i := by
  ext w
  simp [slotInsertion_apply]

theorem alternatization_sign_smul
    (f : MultilinearMap ℝ (fun _ : ι ↦ W) V) (s : ℤˣ) :
    (s • f).alternatization = s • f.alternatization := by
  simp only [Units.smul_def, map_zsmul]

/-- Slots related by a signed symmetry of the actual raw polynomial have
equal alternated insertion contributions. This yields the multiplicities
of interchangeable one-form and curvature factors. -/
theorem alternatization_slotInsertion_exchange
    (f : MultilinearMap ℝ (fun _ : ι ↦ W) V) (T : W →ₗ[ℝ] W)
    (i : ι) (τ : Equiv.Perm ι)
    (hf : f.domDomCongr τ = Equiv.Perm.sign τ • f) :
    (slotInsertion f T i).alternatization =
      (slotInsertion f T (τ.symm i)).alternatization := by
  have h := congrArg MultilinearMap.alternatization (slotInsertion_domPerm f T i τ)
  rw [hf, slotInsertion_sign_smul, alternatization_sign_smul,
    alternatization_domPerm] at h
  exact (smul_left_cancel_iff (Equiv.Perm.sign τ)).mp h

end AlternatizationPermutation

section VerticalVanishing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem oneFormProduct_zero_of_factor (r : ℕ)
    (θ : Fin r → Form 𝓘(ℝ,E) P 1) (i : Fin r) (hi : θ i = 0) :
    oneFormProduct r θ = 0 := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    by_cases hilast : i = Fin.last r
    · subst i
      rw [oneFormProduct, hi]
      exact (wedgeLinear r 1 (oneFormProduct r (fun j ↦ θ j.castSucc))).map_zero
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hilast
      rw [oneFormProduct, ih (fun j ↦ θ j.castSucc) j hi]
      change (wedgeLinear r 1) 0 (θ (Fin.last r)) = 0
      rw [map_zero]
      rfl

theorem oneFormProductMultilinear_zero_of_factor
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1) (r : ℕ) (w : Fin r → W)
    (i : Fin r) (hi : Θ (w i) = 0) : oneFormProductMultilinear Θ r w = 0 := by
  rw [oneFormProductMultilinear_apply]
  exact oneFormProduct_zero_of_factor r (fun j ↦ Θ (w j)) i hi

theorem oneFormProduct_zero_of_factor_at (r : ℕ)
    (θ : Fin r → Form 𝓘(ℝ,E) P 1) (i : Fin r) (x : P) (hi : θ i x = 0) :
    oneFormProduct r θ x = 0 := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    by_cases hilast : i = Fin.last r
    · subst i
      change wedgeFiber _ (θ (Fin.last r) x) = 0
      rw [hi]
      ext v
      simp [wedgeFiber_apply_realSign]
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hilast
      change wedgeFiber (oneFormProduct r (fun j ↦ θ j.castSucc) x) _ = 0
      rw [ih (fun j ↦ θ j.castSucc) j hi]
      ext v
      simp [wedgeFiber_apply_realSign]

/-- The all-direction alternating product vanishes when the one-form map
annihilates a normalized frame direction. This is the actual initial `Y₀=0`
mechanism in Chern's recurrence, in arbitrary dimension. -/
theorem pureTheta_alternatization_zero (d : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1) (b : Basis (Fin d) ℝ W)
    (U : W →ₗ[ℝ] ℝ) (u : W) (hu : U u = 1) (hΘ : Θ u = 0) :
    (oneFormProductMultilinear Θ d).alternatization b = 0 := by
  apply alternating_zero_of_rankOne _ b U u hu
  intro i
  rw [MultilinearMap.alternatization_apply]
  apply Finset.sum_eq_zero
  intro σ _
  rw [MultilinearMap.domDomCongr_apply,
    oneFormProductMultilinear_zero_of_factor Θ d _ (σ.symm i)]
  · exact smul_zero _
  · simpa using hΘ

/-- The same all-direction vanishing requires only the genuine fiber relation
at the point where the expression is evaluated. -/
theorem pureTheta_alternatization_zero_at (d : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1) (b : Basis (Fin d) ℝ W)
    (U : W →ₗ[ℝ] ℝ) (u : W) (x : P) (hu : U u = 1) (hΘ : Θ u x = 0) :
    (oneFormProductMultilinear Θ d).alternatization b x = 0 := by
  let ev : Form 𝓘(ℝ,E) P d →ₗ[ℝ]
      ContinuousAlternatingMap ℝ (TangentSpace 𝓘(ℝ,E) x) ℝ (Fin d) := LinearMap.proj x
  apply alternating_zero_of_rankOne (ev.compAlternatingMap
    (oneFormProductMultilinear Θ d).alternatization) b U u hu
  intro i
  change ((oneFormProductMultilinear Θ d).alternatization (Function.update b i u)) x = 0
  rw [MultilinearMap.alternatization_apply]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro σ _
  rw [MultilinearMap.domDomCongr_apply, oneFormProductMultilinear_apply,
    oneFormProduct_zero_of_factor_at d _ (σ.symm i) x]
  · exact smul_zero _
  · simpa using hΘ

/-- Actual component form of the initial vanishing, with the exact unit and
orthogonality identities on a fiber and no dimension enumeration. -/
theorem pureTheta_sum_zero_of_unit (d : ℕ)
    (u : Fin d → ℝ) (θ : Fin d → Form 𝓘(ℝ,E) P 1) (x : P)
    (hu : ∑ i, u i ^ 2 = 1) (hθ : ∑ i, u i • θ i x = 0) :
    (∑ σ : Equiv.Perm (Fin d), (↑(Equiv.Perm.sign σ) : ℝ) •
      oneFormProduct d (fun i ↦ θ (σ i))) x = 0 := by
  let b := Pi.basisFun ℝ (Fin d)
  let Θ := b.constr ℝ θ
  let U : (Fin d → ℝ) →ₗ[ℝ] ℝ := ∑ i, u i • LinearMap.proj i
  have hU : U u = 1 := by simpa [U, pow_two] using hu
  have hΘ : Θ u x = 0 := by
    simpa [Θ, b, Basis.constr_apply_fintype] using hθ
  have h := pureTheta_alternatization_zero_at d Θ b U u x hU hΘ
  rw [MultilinearMap.alternatization_apply] at h
  simp only [MultilinearMap.domDomCongr_apply, oneFormProductMultilinear_apply,
    Function.comp_def, Θ, Basis.constr_basis] at h
  convert h using 1
  apply congrFun
  apply Finset.sum_congr rfl
  intro σ _
  funext y
  ext v
  simp [Units.smul_def, zsmul_eq_mul]

end VerticalVanishing

section RecurrencePolynomials
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

/-- Uniform recurrence polynomial `Y_k = Alt[θ^(2n-2k) B^k]`, including both
endpoints. Moving one curvature pair to the front has even frame sign and
even form degree, so this is the shifted Chern `Ψ` convention. -/
def recurrencePolynomial (n : ℕ) (k : Fin (n+1))
    (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2) : Form 𝓘(ℝ,E) P (2*n) :=
  ∑ σ : Equiv.Perm (Fin (2*n)), (↑(Equiv.Perm.sign σ) : ℝ) •
    degreeCastForm (show (2*n-2*k.val)+2*k.val = 2*n by have := k.isLt; omega)
      (wedge
        (oneFormProduct (2*n-2*k.val)
          (fun i ↦ θ (σ ⟨i.val, by have := i.isLt; omega⟩)))
        (twoFormProduct k.val (fun j ↦ B
          (σ ⟨2*n-2*k.val+2*j.val, by have := j.isLt; have := k.isLt; omega⟩)
          (σ ⟨2*n-2*k.val+2*j.val+1, by have := j.isLt; have := k.isLt; omega⟩))))

/-- The bottom polynomial is the actual fully alternated direction product. -/
theorem recurrencePolynomial_zero (n : ℕ)
    (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2) :
    recurrencePolynomial n ⟨0, by omega⟩ θ B =
      ∑ σ : Equiv.Perm (Fin (2*n)), (↑(Equiv.Perm.sign σ) : ℝ) •
        oneFormProduct (2*n) (fun i ↦ θ (σ i)) := by
  unfold recurrencePolynomial
  simp only [Fin.val_mk, mul_zero, Nat.sub_zero, twoFormProduct, wedge_one_right]
  rfl

/-- The unit-sphere constraints force the initial recurrence polynomial to
vanish, pointwise and in every dimension. -/
theorem recurrencePolynomial_zero_of_unit (n : ℕ)
    (u : Fin (2*n) → ℝ) (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2) (x : P)
    (hu : ∑ i, u i ^ 2 = 1) (hθ : ∑ i, u i • θ i x = 0) :
    recurrencePolynomial n ⟨0, by omega⟩ θ B x = 0 := by
  rw [recurrencePolynomial_zero]
  exact pureTheta_sum_zero_of_unit (2*n) u θ x hu hθ

/-- The terminal recurrence polynomial is exactly the unnormalized Pfaffian
sum of actual curvature two-forms, without an extra factorial. -/
theorem recurrencePolynomial_top (n : ℕ)
    (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (B : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2) :
    recurrencePolynomial n ⟨n, by omega⟩ θ B =
      ∑ σ : Equiv.Perm (Fin (2*n)), (↑(Equiv.Perm.sign σ) : ℝ) •
        twoFormProduct n (fun j ↦ B (σ (pairFirst j)) (σ (pairSecond j))) := by
  unfold recurrencePolynomial
  simp only [Fin.val_mk, Nat.sub_self, oneFormProduct, zero_add]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  have hi : (fun j : Fin n ↦ B (σ ⟨2*j.val, by have := j.isLt; omega⟩)
      (σ ⟨2*j.val+1, by have := j.isLt; omega⟩)) =
      (fun j : Fin n ↦ B (σ (pairFirst j)) (σ (pairSecond j))) := by rfl
  rw [hi]
  have hz (r : ℕ) (hr : r = 0) (η : Fin r → Form 𝓘(ℝ,E) P 1)
      (β : Form 𝓘(ℝ,E) P (2*n)) (h : r+2*n=2*n) :
      degreeCastForm h (wedge (oneFormProduct r η) β) = β := by
    subst r
    exact wedge_one_left β
  exact hz _ (Nat.sub_self _) _ _ _

end RecurrencePolynomials

section MixedInsertion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Genuine mixed product before alternation: all direction factors followed
by paired curvature factors. -/
def mixedMultilinear (r k : ℕ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) :
    MultilinearMap ℝ (fun _ : Fin (r+2*k) ↦ W) (Form 𝓘(ℝ,E) P (r+2*k)) :=
  multilinearBlock (wedgeLinear r (2*k))
    (oneFormProductMultilinear Θ r) (twoFormProductMultilinear B k)

theorem mixedMultilinear_apply (r k : ℕ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) (w : Fin (r+2*k) → W) :
    mixedMultilinear r k Θ B w = wedge
      (oneFormProduct r (fun i ↦ Θ (w (Fin.castAdd (2*k) i))))
      (twoFormProduct k (fun j ↦ B (w (Fin.natAdd r (pairFirst j)))
        (w (Fin.natAdd r (pairSecond j))))) := by
  rw [mixedMultilinear, multilinearBlock_apply, wedgeLinear_apply,
    oneFormProductMultilinear_apply, twoFormProductMultilinear_apply]

/-- The actual unit-direction insertion into a direction-form slot vanishes. -/
theorem mixed_slotInsertion_theta_zero (r k : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (U : W →ₗ[ℝ] ℝ) (u : W) (hΘ : Θ u = 0) (i : Fin r) :
    slotInsertion (mixedMultilinear r k Θ B) (U.smulRight u) (Fin.castAdd (2*k) i) = 0 := by
  ext w x v
  rw [slotInsertion_apply, mixedMultilinear_apply]
  have hz : oneFormProduct r (fun j ↦ Θ
      ((Function.update w (Fin.castAdd (2*k) i)
        ((U.smulRight u) (w (Fin.castAdd (2*k) i)))) (Fin.castAdd (2*k) j))) = 0 := by
    apply oneFormProduct_zero_of_factor r _ i
    simp [hΘ]
  rw [hz]
  simp [wedge, wedgeFiber_apply_realSign]

/-- The unit-direction trace is exhausted by the genuine curvature slots;
there are precisely `2*k` of these slots, for arbitrary symbolic `k`. -/
theorem mixed_curvature_insertion_sum (r k : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (b : Basis (Fin (r+2*k)) ℝ W) (U : W →ₗ[ℝ] ℝ) (u : W)
    (hu : U u = 1) (hΘ : Θ u = 0) :
    (∑ j : Fin (2*k),
      (slotInsertion (mixedMultilinear r k Θ B) (U.smulRight u) (Fin.natAdd r j)).alternatization b) =
      (mixedMultilinear r k Θ B).alternatization b := by
  have h := alternatization_rankOne_sum (mixedMultilinear r k Θ B) b U u
  rw [hu, one_smul] at h
  rw [← Equiv.sum_comp (finSumFinEquiv : Fin r ⊕ Fin (2*k) ≃ Fin (r+2*k)),
    Fintype.sum_sum_type] at h
  simpa [mixed_slotInsertion_theta_zero r k Θ B U u hΘ] using h

/-- Fiberwise form of the vanishing direction-slot insertion. -/
theorem mixed_slotInsertion_theta_zero_at (r k : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (U : W →ₗ[ℝ] ℝ) (u : W) (x : P) (hΘ : Θ u x = 0) (i : Fin r)
    (w : Fin (r+2*k) → W) :
    slotInsertion (mixedMultilinear r k Θ B) (U.smulRight u) (Fin.castAdd (2*k) i) w x = 0 := by
  rw [slotInsertion_apply, mixedMultilinear_apply]
  have hz : oneFormProduct r (fun j ↦ Θ
      ((Function.update w (Fin.castAdd (2*k) i)
        ((U.smulRight u) (w (Fin.castAdd (2*k) i)))) (Fin.castAdd (2*k) j))) x = 0 := by
    apply oneFormProduct_zero_of_factor_at r _ i x
    simp [hΘ]
  change wedgeFiber _ _ = 0
  rw [hz]
  ext v
  simp [wedgeFiber_apply_realSign]

/-- The curvature-slot trace identity uses only the unit and orthogonality
relations in the actual fiber under consideration. -/
theorem mixed_curvature_insertion_sum_at (r k : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (b : Basis (Fin (r+2*k)) ℝ W) (U : W →ₗ[ℝ] ℝ) (u : W) (x : P)
    (hu : U u = 1) (hΘ : Θ u x = 0) :
    (∑ j : Fin (2*k),
      (slotInsertion (mixedMultilinear r k Θ B) (U.smulRight u) (Fin.natAdd r j)).alternatization b x) =
      (mixedMultilinear r k Θ B).alternatization b x := by
  have h := congrFun (alternatization_rankOne_sum (mixedMultilinear r k Θ B) b U u) x
  simp only [Finset.sum_apply, Pi.smul_apply, hu, one_smul] at h
  rw [← Equiv.sum_comp (finSumFinEquiv : Fin r ⊕ Fin (2*k) ≃ Fin (r+2*k)),
    Fintype.sum_sum_type] at h
  have hz (i : Fin r) :
      (slotInsertion (mixedMultilinear r k Θ B) (U.smulRight u)
        (Fin.castAdd (2*k) i)).alternatization b x = 0 := by
    rw [MultilinearMap.alternatization_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, MultilinearMap.domDomCongr_apply]
    apply Finset.sum_eq_zero
    intro σ _
    rw [mixed_slotInsertion_theta_zero_at r k Θ B U u x hΘ i, smul_zero]
  simpa only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    hz, Finset.sum_const_zero, zero_add] using h

end MixedInsertion

section AngularInfinitesimal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The actual Chern angular polynomial has the infinitesimal determinant
law. This is the algebraic cancellation used for skew connection matrices. -/
theorem angularTerm_endomorphism_insertion (n : ℕ) (k : Fin n)
    (U : W →ₗ[ℝ] P → ℝ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (b : Basis (Fin (2*n)) ℝ W) (T : W →ₗ[ℝ] W) :
    (∑ i, (slotInsertion (angularMultilinear n k U Θ B) T i).alternatization b) =
      (∑ i, b.repr (T (b i)) i) •
        angularTerm n k (fun i ↦ U (b i)) (fun i ↦ Θ (b i))
          (fun i j ↦ B (b i) (b j)) := by
  rw [alternatization_endomorphism_sum, angularMultilinear_alternatization]

/-- No connection-matrix hypothesis is hidden here: the vanishing diagonal
sum is an explicit actual linear-algebra input, later supplied by metric skew. -/
theorem angularTerm_endomorphism_insertion_zero (n : ℕ) (k : Fin n)
    (U : W →ₗ[ℝ] P → ℝ) (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (b : Basis (Fin (2*n)) ℝ W) (T : W →ₗ[ℝ] W)
    (hT : ∑ i, b.repr (T (b i)) i = 0) :
    (∑ i, (slotInsertion (angularMultilinear n k U Θ B) T i).alternatization b) = 0 := by
  rw [angularTerm_endomorphism_insertion, hT, zero_smul]

end AngularInfinitesimal

section SkewFrameVariation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]

/-- Skew frame matrices have no infinitesimal effect on the actual angular
polynomial. The coefficient trace is proved zero from genuine skew symmetry. -/
theorem angularTerm_skew_matrix_insertion (n : ℕ) (k : Fin n)
    (U : (Fin (2*n) → ℝ) →ₗ[ℝ] P → ℝ)
    (Θ : (Fin (2*n) → ℝ) →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : (Fin (2*n) → ℝ) →ₗ[ℝ] (Fin (2*n) → ℝ) →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (A : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hA : A.transpose = -A) :
    (∑ i, (slotInsertion (angularMultilinear n k U Θ B)
      (Matrix.toLin' A) i).alternatization (Pi.basisFun ℝ (Fin (2*n)))) = 0 := by
  apply angularTerm_endomorphism_insertion_zero
  apply Finset.sum_eq_zero
  intro i _
  have hi := congrArg (fun C : Matrix (Fin (2*n)) (Fin (2*n)) ℝ ↦ C i i) hA
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hi
  have hz : A i i = 0 := by linarith
  simpa [Matrix.toLin'_apply] using hz

end SkewFrameVariation

section CurvaturePairPermutations

/-- The existing consecutive-pair indexing, with a product domain. -/
def curvaturePairEquiv (k : ℕ) : Fin k × Fin 2 ≃ Fin (2*k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2))

@[simp] theorem curvaturePairEquiv_first {k : ℕ} (i : Fin k) :
    curvaturePairEquiv k (i, 0) = pairFirst i := by
  apply Fin.ext
  simp [curvaturePairEquiv, pairFirst, finProdFinEquiv, Nat.mul_comm]

@[simp] theorem curvaturePairEquiv_second {k : ℕ} (i : Fin k) :
    curvaturePairEquiv k (i, 1) = pairSecond i := by
  apply Fin.ext
  simp [curvaturePairEquiv, pairSecond, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- Permuting complete curvature pairs preserves the full frame sign. -/
def curvaturePairPerm (k : ℕ) (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (2*k)) :=
  (curvaturePairEquiv k).permCongr (Equiv.prodCongrLeft (fun _ : Fin 2 ↦ σ))

theorem sign_curvaturePairPerm (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm.sign (curvaturePairPerm k σ) = 1 := by
  simp [curvaturePairPerm, Equiv.Perm.sign_prodCongrLeft, Fin.prod_univ_two]

@[simp] theorem curvaturePairPerm_first {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    curvaturePairPerm k σ (pairFirst i) = pairFirst (σ i) := by
  rw [curvaturePairPerm, Equiv.permCongr_apply, ← curvaturePairEquiv_first i,
    Equiv.symm_apply_apply, Equiv.prodCongrLeft_apply, curvaturePairEquiv_first]

@[simp] theorem curvaturePairPerm_second {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    curvaturePairPerm k σ (pairSecond i) = pairSecond (σ i) := by
  rw [curvaturePairPerm, Equiv.permCongr_apply, ← curvaturePairEquiv_second i,
    Equiv.symm_apply_apply, Equiv.prodCongrLeft_apply, curvaturePairEquiv_second]

/-- Extend a permutation of curvature indices by the identity on direction slots. -/
def mixedCurvaturePerm (r k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (r+2*k)) :=
  (finSumFinEquiv : Fin r ⊕ Fin (2*k) ≃ Fin (r+2*k)).permCongr
    (Equiv.sumCongr (Equiv.refl _) (curvaturePairPerm k σ))

theorem sign_mixedCurvaturePerm (r k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm.sign (mixedCurvaturePerm r k σ) = 1 := by
  simp [mixedCurvaturePerm, sign_curvaturePairPerm]

@[simp] theorem mixedCurvaturePerm_theta (r k : ℕ) (σ : Equiv.Perm (Fin k)) (i : Fin r) :
    mixedCurvaturePerm r k σ (Fin.castAdd (2*k) i) = Fin.castAdd (2*k) i := by
  simp [mixedCurvaturePerm]

@[simp] theorem mixedCurvaturePerm_first (r k : ℕ) (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    mixedCurvaturePerm r k σ (Fin.natAdd r (pairFirst i)) = Fin.natAdd r (pairFirst (σ i)) := by
  simp [mixedCurvaturePerm]

@[simp] theorem mixedCurvaturePerm_second (r k : ℕ) (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    mixedCurvaturePerm r k σ (Fin.natAdd r (pairSecond i)) = Fin.natAdd r (pairSecond (σ i)) := by
  simp [mixedCurvaturePerm]

end CurvaturePairPermutations

end GaussBonnetChern.Chern














