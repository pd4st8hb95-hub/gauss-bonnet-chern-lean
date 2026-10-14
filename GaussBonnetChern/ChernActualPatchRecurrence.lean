import GaussBonnetChern.ChernOriginalRecurrence
import GaussBonnetChern.ChernPatchGeometry

/-! The original recurrence on the actual normalized tautological Cartan data.
Finite linear extensions only change the frame-slot presentation; the exterior
derivative remains the genuine derivative of the original smooth forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff BigOperators
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm

private def coordinateLift {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : Fin d → V) : (Fin d → ℝ) →ₗ[ℝ] V :=
  (Pi.basisFun ℝ (Fin d)).constr ℝ f

private theorem coordinateLift_apply {d : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] (f : Fin d → V) (v : Fin d → ℝ) :
    coordinateLift f v = ∑ i, v i • f i := by
  simp [coordinateLift, Basis.constr_apply_fintype, Basis.equivFun_apply]

private theorem coordinateLift_basis {d : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] (f : Fin d → V) (i : Fin d) :
    coordinateLift f ((Pi.basisFun ℝ (Fin d)) i) = f i := by
  simp [coordinateLift]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  [IsManifold 𝓘(ℝ,E) ∞ P]

private theorem isSmooth_coordinateLift {d p : ℕ}
    (α : Fin d → Form 𝓘(ℝ,E) P p) (hα : ∀ i, IsSmooth (α i))
    (v : Fin d → ℝ) : IsSmooth (coordinateLift α v) := by
  rw [coordinateLift_apply]
  exact IsSmooth.sum Finset.univ _ (fun i _ ↦ (hα i).const_smul (v i))

private theorem exteriorDerivative_coordinateLift {d p : ℕ}
    (α : Fin d → Form 𝓘(ℝ,E) P p) (hα : ∀ i, IsSmooth (α i))
    (v : Fin d → ℝ) :
    exteriorDerivative (coordinateLift α v) =
      coordinateLift (fun i ↦ exteriorDerivative (α i)) v := by
  simp only [coordinateLift_apply]
  rw [exteriorDerivative_sum Finset.univ _ (fun i _ ↦ (hα i).const_smul (v i))]
  simp only [exteriorDerivative_smul]

private theorem contMDiff_coordinateLift {d : ℕ} (f : Fin d → P → ℝ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (f i)) (v : Fin d → ℝ) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (coordinateLift f v) := by
  rw [coordinateLift_apply]
  have heq : (∑ i, v i • f i) = (fun x ↦ ∑ i, v i * f i x) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact contMDiff_finsetSum (fun i _ ↦ contMDiff_const.mul (hf i))

private theorem ofFunction_coordinateLift {d : ℕ}
    (f : Fin d → P → ℝ) (v : Fin d → ℝ) :
    ofFunction (I := 𝓘(ℝ,E)) (coordinateLift f v) =
      coordinateLift (fun i ↦ ofFunction (I := 𝓘(ℝ,E)) (f i)) v := by
  funext x
  ext w
  simp [coordinateLift_apply, ofFunction, Finset.sum_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]

private theorem wedge_two_one_comm (α : Form 𝓘(ℝ,E) P 2)
    (β : Form 𝓘(ℝ,E) P 1) : wedge α β = wedge β α := by
  funext x
  ext v
  have hv : (fun i : Fin (1+2) ↦ v (finCongr (Nat.add_comm 1 2) i)) = v := by
    funext i
    congr 1
  have h := wedge_graded_comm α β x v
  rw [hv] at h
  simpa using h.symm

private theorem actualWedge_neg_left {p q : ℕ}
    (α : Form 𝓘(ℝ,E) P p) (β : Form 𝓘(ℝ,E) P q) :
    wedge (-α) β = -wedge α β := by
  funext x
  ext v
  simp [wedge, wedgeFiber_apply_realSign, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

/-- Component Cartan/Bianchi equations suffice to instantiate the complete
original recurrence. All derivative hypotheses are primitive actual equations,
not a recurrence, transgression, or replacement derivative assumption. -/
theorem exteriorDerivative_angularTerm_recurrence_of_components (n : ℕ) (k : Fin n)
    (u : Fin (2*n) → P → ℝ)
    (θ : Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (A : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 1)
    (Ω : Fin (2*n) → Fin (2*n) → Form 𝓘(ℝ,E) P 2)
    (hu : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (u i))
    (hθ : ∀ i, IsSmooth (θ i)) (hΩ : ∀ i j, IsSmooth (Ω i j))
    (hA : ∀ i j, A i j = -A j i) (hΩskew : ∀ i j, Ω i j = -Ω j i)
    (hscalar : ∀ i, exteriorDerivative (ofFunction (u i)) = θ i -
      ∑ j, functionSmul (u j) (A i j))
    (hcartan : ∀ i, exteriorDerivative (θ i) =
      (∑ j, functionSmul (u j) (Ω i j)) - ∑ j, wedge (A i j) (θ j))
    (hbianchi : ∀ i j, exteriorDerivative (Ω i j) =
      ∑ a, (wedge (Ω i a) (A a j) - wedge (A i a) (Ω a j)))
    (hunit : ∀ x, ∑ i, u i x ^ 2 = 1)
    (horth : ∀ x, (∑ i, u i x • θ i x) = 0) :
    degreeCastForm (show (2*n-1)+1=2*n by have := k.isLt; omega)
      (exteriorDerivative (angularTerm n k u θ Ω)) =
      recurrencePolynomial n k.castSucc θ Ω - recurrenceCoefficient n k.val •
        recurrencePolynomial n k.succ θ Ω := by
  let b := Pi.basisFun ℝ (Fin (2*n))
  let U := coordinateLift u
  let Θ := coordinateLift θ
  let B := coordinateLift (fun i ↦ coordinateLift (Ω i))
  let Γ : Fin (2*n) → (Fin (2*n) → ℝ) →ₗ[ℝ] Form 𝓘(ℝ,E) P 1 :=
    fun j ↦ -coordinateLift (fun i ↦ A i j)
  let unitVector : P → (Fin (2*n) → ℝ) := fun x i ↦ u i x
  have hUb (i) : U (b i) = u i := coordinateLift_basis u i
  have hΘb (i) : Θ (b i) = θ i := coordinateLift_basis θ i
  have hBb (i j) : B (b i) (b j) = Ω i j := by
    simp only [B, b, coordinateLift_basis]
  have hΓb (i j) : Γ j (b i) = -A i j := by
    simp only [Γ, b, LinearMap.neg_apply, coordinateLift_basis]
  have hΓskew : ∀ i j, Γ i (b j) = -Γ j (b i) := by
    intro i j
    rw [hΓb, hΓb, neg_neg, hA j i, neg_neg]
  have hBskew : ∀ v z, B v z = -B z v := by
    intro v z
    simp only [B, coordinateLift_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.smul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hΩskew j i]
    simp only [smul_neg, smul_smul]
    rw [mul_comm]
  have hUsmooth (v) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (U v) :=
    contMDiff_coordinateLift u hu v
  have hΘsmooth (v) : IsSmooth (Θ v) := isSmooth_coordinateLift θ hθ v
  have hBsmooth (v z) : IsSmooth (B v z) := by
    change IsSmooth ((coordinateLift (fun i ↦ coordinateLift (Ω i)) v) z)
    rw [coordinateLift_apply]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact IsSmooth.sum Finset.univ _ (fun i _ ↦
      (isSmooth_coordinateLift (Ω i) (hΩ i) z).const_smul (v i))
  let DScalar : (Fin (2*n) → ℝ) →ₗ[ℝ] Form 𝓘(ℝ,E) P 1 :=
    coordinateLift (fun i ↦ exteriorDerivative (ofFunction (I := 𝓘(ℝ,E)) (u i)))
  have hScalarMap : DScalar = Θ + ∑ j,
      (functionSmulLinear 1 (U (b j))).comp (Γ j) := by
    apply b.ext
    intro i
    simp only [DScalar, b, coordinateLift_basis, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.comp_apply, hUb, hΘb, hΓb, map_neg]
    rw [hscalar i]
    funext x
    ext w
    simp [functionSmulLinear, LinearMap.mk₂_apply, functionSmul,
      sub_eq_add_neg, Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply]
  have hScalar (v) : exteriorDerivative (ofFunction (U v)) =
      Θ v + ∑ j, functionSmulLinear 1 (U (b j)) (Γ j v) := by
    rw [show U = coordinateLift u from rfl,
      ofFunction_coordinateLift (E := E) (P := P),
      exteriorDerivative_coordinateLift (E := E) (P := P) _
        (fun i ↦ (show IsSmooth (ofFunction (I := 𝓘(ℝ,E)) (u i)) from
          IsSmooth.ofFunction (hu i)))]
    change DScalar v = _
    rw [hScalarMap]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  let DTheta := coordinateLift (fun i ↦ exteriorDerivative (θ i))
  let Bu := ∑ j, (functionSmulLinear 2 (u j)).comp (B.flip (b j))
  have hBu (v) : Bu v = (fun x ↦ B v (unitVector x) x) := by
    funext x
    simp only [Bu, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.flip_apply]
    have hrepr : unitVector x = ∑ j, u j x • b j := by
      simpa only [b, Basis.equivFun_apply, Pi.basisFun_repr, unitVector]
        using (b.sum_repr (unitVector x)).symm
    rw [hrepr, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply,
      functionSmulLinear, LinearMap.mk₂_apply]
  have hCartanMap : DTheta = Bu + ∑ j,
      ((wedgeLinear 1 1).flip (Θ (b j))).comp (Γ j) := by
    apply b.ext
    intro i
    simp only [DTheta, b, coordinateLift_basis, Bu, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.flip_apply,
      hBb, hΘb, hΓb, map_neg, wedgeLinear_apply, actualWedge_neg_left]
    rw [hcartan i]
    funext x
    ext w
    simp [functionSmulLinear, LinearMap.mk₂_apply, functionSmul,
      sub_eq_add_neg, Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply]
  have hCartan (v) : exteriorDerivative (Θ v) =
      (fun x ↦ B v (unitVector x) x) + ∑ j, wedge (Γ j v) (Θ (b j)) := by
    rw [show Θ = coordinateLift θ from rfl, exteriorDerivative_coordinateLift θ hθ]
    change DTheta v = _
    rw [hCartanMap]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.flip_apply, wedgeLinear_apply, hBu]
    rfl
  let DB := coordinateLift (fun i ↦ coordinateLift (fun j ↦ exteriorDerivative (Ω i j)))
  let RB := ∑ a,
    ((wedgeLinear 1 2).compl₁₂ (Γ a) (B (b a)) +
      ((wedgeLinear 1 2).compl₁₂ (Γ a) (B.flip (b a))).flip)
  have hBianchiMap : DB = RB := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    simp only [DB, b, coordinateLift_basis, RB, LinearMap.sum_apply,
      LinearMap.add_apply, LinearMap.flip_apply, LinearMap.compl₁₂_apply,
      hΓb, hBb, wedgeLinear_apply]
    rw [hbianchi i j]
    apply Finset.sum_congr rfl
    intro a _
    rw [wedge_two_one_comm, hA a j]
    change wedgeLinear 1 2 (-A j a) (Ω i a) - wedgeLinear 1 2 (A i a) (Ω a j) =
      wedgeLinear 1 2 (-A i a) (Ω a j) + wedgeLinear 1 2 (-A j a) (Ω i a)
    rw [map_neg, map_neg]
    funext x
    ext w
    simp only [LinearMap.smul_apply, LinearMap.neg_apply,
      Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
      ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  have hDB (v z) : exteriorDerivative (B v z) = DB v z := by
    change exteriorDerivative ((coordinateLift (fun i ↦ coordinateLift (Ω i)) v) z) = _
    rw [coordinateLift_apply]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    rw [exteriorDerivative_sum Finset.univ _ (fun i _ ↦
      (isSmooth_coordinateLift (Ω i) (hΩ i) z).const_smul (v i))]
    simp only [exteriorDerivative_smul, exteriorDerivative_coordinateLift _ (hΩ _),
      DB, coordinateLift_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [exteriorDerivative_sum Finset.univ _ (fun j _ ↦ (hΩ i j).const_smul (z j))]
    simp only [exteriorDerivative_smul]
  have hBianchi (v z) : exteriorDerivative (B v z) =
      (∑ j, wedge (Γ j v) (B (b j) z)) + ∑ j, wedge (Γ j z) (B v (b j)) := by
    rw [hDB, hBianchiMap]
    simp only [RB, LinearMap.sum_apply, LinearMap.add_apply,
      LinearMap.compl₁₂_apply, LinearMap.flip_apply, wedgeLinear_apply,
      Finset.sum_add_distrib]
  have hunitVector (x) : U (unitVector x) x = 1 := by
    simpa only [U, coordinateLift_apply, Finset.sum_apply, Pi.smul_apply,
      unitVector, smul_eq_mul, pow_two] using hunit x
  have horthVector (x) : Θ (unitVector x) x = 0 := by
    simpa only [Θ, coordinateLift_apply, Finset.sum_apply, Pi.smul_apply,
      unitVector] using horth x
  have h := exteriorDerivative_angularTerm_recurrence n k b (fun j ↦ Γ j)
    U Θ B unitVector hΓskew hBskew hUsmooth hΘsmooth hBsmooth
    hScalar hCartan hBianchi hunitVector horthVector
  simpa only [hUb, hΘb, hBb] using h

end GaussBonnetChern.Chern

namespace GaussBonnetChern
open DifferentialForm
open Bundle
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]
variable (b : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x))
  (s : TopologicalSpace.Opens M)
  (hb : ∀ i, ContMDiffOn (model n) (model n).tangent ∞
    (T% (fun x ↦ b x i)) s)

include hb in
/-- The genuine dPhi recurrence on every actual frame patch. The only
regularity premise is smoothness of the chosen frame on its base domain. -/
theorem exteriorDerivative_framePatch_angularTerm_recurrence (k : Fin n) :
    degreeCastForm (show (2*n-1)+1=2*n by have := k.isLt; omega)
      (exteriorDerivative (Chern.angularTerm n k
        (framePatchDirectionCoordinate n M b s) (framePatchDirectionForm n M b s)
        (framePatchCurvatureForm n M b s))) =
      Chern.recurrencePolynomial n k.castSucc (framePatchDirectionForm n M b s)
        (framePatchCurvatureForm n M b s) - Chern.recurrenceCoefficient n k.val •
      Chern.recurrencePolynomial n k.succ (framePatchDirectionForm n M b s)
        (framePatchCurvatureForm n M b s) := by
  apply Chern.exteriorDerivative_angularTerm_recurrence_of_components n k
    (framePatchDirectionCoordinate n M b s) (framePatchDirectionForm n M b s)
    (framePatchConnectionForm n M b s) (framePatchCurvatureForm n M b s)
  · intro i
    simpa only [modelWithCornersSelf_prod] using
      contMDiff_framePatchDirectionCoordinate n M b s hb i
  · exact isSmooth_framePatchDirectionForm n M b s hb
  · exact isSmooth_framePatchCurvatureForm n M b s hb
  · exact framePatchConnectionForm_skew n M b s hb
  · exact framePatchCurvatureForm_skew n M b s
  · intro i
    rw [exteriorDerivative_ofFunction (by
      simpa only [modelWithCornersSelf_prod] using
        (contMDiff_framePatchDirectionCoordinate n M b s hb i).mdifferentiable (by simp))]
    exact scalarDifferential_framePatchDirectionCoordinate n M b s i
  · exact exteriorDerivative_framePatchDirectionForm n M b s hb
  · exact framePatchBianchi n M b s hb
  · exact framePatchDirectionCoordinate_unit n M b s
  · exact framePatchDirectionForm_orthogonal n M b s hb

end GaussBonnetChern
