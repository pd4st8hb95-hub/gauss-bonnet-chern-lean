import GaussBonnetChern.SingularSubdivision
import Mathlib.GroupTheory.Perm.Fin

/-! # Boundary compatibility of geometric singular subdivision

All generators and maps below belong to the project's actual singular-chain
complex. External faces are indexed by the omitted original vertex and a
permutation of the remaining vertices.
-/

noncomputable section

universe u

namespace GaussBonnetChern

open CategoryTheory Convexity
open scoped BigOperators Simplicial

/-- The usual continuous inclusion of a face of the topological standard simplex. -/
def standardSimplexFace {n : ℕ} (i : Fin (n + 2)) :
    C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 2))) :=
  ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ i.succAbove⟩

/-- The actual `i`th face of a singular simplex. -/
def singularSimplexFace {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    C(StdSimplex ℝ (Fin (n + 1)), X) :=
  s.comp (standardSimplexFace i)

theorem singularSimplexFace_toSSet {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).symm (singularSimplexFace s i) =
      (TopCat.toSSet.obj (TopCat.of X)).δ i
        ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n + 1⦌)).symm s) := by
  rfl

/-- The project singular-chain differential is the signed geometric face sum. -/
theorem singularSimplexGenerator_boundary {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X)) :
    singularSimplexGenerator s ≫ (singularChains X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • singularSimplexGenerator (singularSimplexFace s i) := by
  exact (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d
      (R := ModuleCat.of ℝ (ULift.{u} ℝ))
      ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n + 1⦌)).symm s)

/-- An injective relabelling takes the barycenter of a face to the barycenter
of its image face. -/
theorem subBarycenter_map_injective {I J : Type*} [DecidableEq J] (f : I → J) (hf : Function.Injective f)
    (s : Finset I) (hs : s.Nonempty) :
    (StdSimplex.subBarycenter (K := ℝ) s hs).map f =
      StdSimplex.subBarycenter (s.image f) (hs.image f) := by
  classical
  apply StdSimplex.ext
  simp only [StdSimplex.weights_map, StdSimplex.weights_subBarycenter,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single,
    Finset.card_image_of_injective _ hf]
  rw [Finset.sum_image]
  exact fun _ _ _ _ h ↦ hf h

/-- Reconstruct a flag with omitted last vertex `j` from a flag of that face. -/
def externalFacePermutation {n : ℕ} (j : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) :=
  Equiv.Perm.decomposeFin'Symm j τ * finRotate (n + 2)

@[simp]
theorem externalFacePermutation_last {n : ℕ}
    (j : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    externalFacePermutation j τ (Fin.last (n + 1)) = j := by
  simp [externalFacePermutation, Equiv.Perm.mul_apply]

@[simp]
theorem externalFacePermutation_castSucc {n : ℕ}
    (j : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    externalFacePermutation j τ k.castSucc = j.succAbove (τ k) := by
  have h : finRotate (n + 2) k.castSucc = k.succ := finRotate_of_lt k.isLt
  rw [externalFacePermutation, Equiv.Perm.mul_apply, h]
  rfl

/-- Every full flag has a unique external face and a flag of that face. -/
def externalFacePermutationEquiv (n : ℕ) :
    (Fin (n + 2) × Equiv.Perm (Fin (n + 1))) ≃ Equiv.Perm (Fin (n + 2)) :=
  (Equiv.Perm.decomposeFin' (n := n)).symm.trans
    { toFun := fun σ ↦ σ * finRotate (n + 2)
      invFun := fun σ ↦ σ * (finRotate (n + 2))⁻¹
      left_inv := fun σ ↦ by simp [mul_assoc]
      right_inv := fun σ ↦ by simp [mul_assoc] }

@[simp]
theorem externalFacePermutationEquiv_apply (n : ℕ)
    (j : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    externalFacePermutationEquiv n (j, τ) = externalFacePermutation j τ := rfl

/-- The external-face boundary coefficient is the usual face coefficient
times the lower-dimensional subdivision coefficient. -/
theorem externalFacePermutation_sign {n : ℕ}
    (j : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign (externalFacePermutation j τ) : ℤ) * (-1 : ℤ) ^ (n + 1) =
      (-1 : ℤ) ^ j.val * (Equiv.Perm.sign τ : ℤ) := by
  have hpow : (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1) = 1 := by
    rw [← mul_pow]
    simp
  have hrotate : (Equiv.Perm.sign (finRotate (n + 2)) : ℤ) = (-1 : ℤ) ^ (n + 1) := by
    simp
  simp only [externalFacePermutation, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_decomposeFin'Symm,
    Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hrotate]
  rw [mul_assoc, mul_assoc, hpow, mul_one]

theorem externalFacePermutation_flagFace {n : ℕ}
    (j : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    barycentricFlagFace (externalFacePermutation j τ) k.castSucc =
      (barycentricFlagFace τ k).image j.succAbove := by
  unfold barycentricFlagFace
  rw [← Fin.finsetImage_castSucc_Iic, Finset.image_image, Finset.image_image]
  congr 1
  funext l
  exact externalFacePermutation_castSucc j τ l

theorem externalFacePermutation_flagVertex {n : ℕ}
    (j : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    barycentricFlagVertex (externalFacePermutation j τ) k.castSucc =
      (barycentricFlagVertex τ k).map j.succAbove := by
  rw [barycentricFlagVertex, barycentricFlagVertex,
    subBarycenter_map_injective j.succAbove Fin.succAbove_right_injective]
  simp only [externalFacePermutation_flagFace]

/-- The last face of the reconstructed barycentric simplex is the barycentric
simplex inside the specified original face. -/
theorem barycentricSimplex_externalFace {n : ℕ}
    (j : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    (barycentricSimplex (externalFacePermutation j τ)).comp
        (standardSimplexFace (Fin.last (n + 1))) =
      (standardSimplexFace j).comp (barycentricSimplex τ) := by
  have h : (StdSimplex.affineMapMk (R := ℝ)
        (barycentricFlagVertex (externalFacePermutation j τ))).comp
          (StdSimplex.affineMap (R := ℝ) (Fin.last (n + 1)).succAbove) =
      (StdSimplex.affineMap (R := ℝ) j.succAbove).comp
        (StdSimplex.affineMapMk (R := ℝ) (barycentricFlagVertex τ)) := by
    apply StdSimplex.affineMap_ext
    intro k
    simpa using externalFacePermutation_flagVertex j τ k
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1)))
    (StdSimplex ℝ (Fin (n + 2))) ↦ f x) h

theorem barycentricSingularFace_external {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X))
    (j : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    barycentricSingularFace s (externalFacePermutation j τ) (Fin.last (n + 1)) =
      barycentricSingularSimplex (singularSimplexFace s j) τ := by
  apply ContinuousMap.ext
  intro x
  exact congrArg s (congrArg
    (fun f : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 2))) ↦ f x)
    (barycentricSimplex_externalFace j τ))

/-- All flags cancel in pairs along any fixed internal-face position. -/
theorem sum_barycentric_internalFaces_eq_zero {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      singularSimplexGenerator (barycentricSingularFace s σ i.castSucc)) = 0 := by
  classical
  refine Finset.sum_ninvolution (fun σ ↦ σ * Equiv.swap i.castSucc i.succ) ?_ ?_ ?_ ?_
  · intro σ
    exact barycentric_internalFace_generator_cancel s σ i
  · intro σ _ h
    have he := congrArg (fun p : Equiv.Perm (Fin (n + 2)) ↦ p i.castSucc) h
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at he
    have hv := congrArg Fin.val (σ.injective he)
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  · intro σ
    exact Finset.mem_univ _
  · intro σ
    simp [mul_assoc]

/-- The double sum of all signed internal boundary faces vanishes. -/
theorem sum_barycentric_internal_boundary_eq_zero {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), ∑ i : Fin (n + 1),
      ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ i.val) •
        singularSimplexGenerator (barycentricSingularFace s σ i.castSucc)) = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  calc
    _ = (-1 : ℤ) ^ i.val •
        ∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
          singularSimplexGenerator (barycentricSingularFace s σ i.castSucc) := by
      simp only [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro σ _
      rw [mul_comm]
    _ = 0 := by rw [sum_barycentric_internalFaces_eq_zero]; simp

/-- Reindex the external boundary faces by omitted vertex and face flag. -/
theorem sum_barycentric_external_boundary {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
      ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (n + 1)) •
        singularSimplexGenerator (barycentricSingularFace s σ (Fin.last (n + 1)))) =
      ∑ j : Fin (n + 2), ∑ τ : Equiv.Perm (Fin (n + 1)),
        ((-1 : ℤ) ^ j.val * (Equiv.Perm.sign τ : ℤ)) •
          singularSimplexGenerator (barycentricSingularSimplex (singularSimplexFace s j) τ) := by
  rw [← (externalFacePermutationEquiv n).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro τ _
  rw [externalFacePermutationEquiv_apply, externalFacePermutation_sign,
    barycentricSingularFace_external]

/-- The entire boundary of the signed geometric subdivision is the signed
subdivision of the original boundary, at the generator-sum level. -/
theorem sum_barycentric_boundary {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), ∑ i : Fin (n + 2),
      ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ i.val) •
        singularSimplexGenerator (barycentricSingularFace s σ i)) =
      ∑ j : Fin (n + 2), ∑ τ : Equiv.Perm (Fin (n + 1)),
        ((-1 : ℤ) ^ j.val * (Equiv.Perm.sign τ : ℤ)) •
          singularSimplexGenerator (barycentricSingularSimplex (singularSimplexFace s j) τ) := by
  conv_lhs =>
    arg 2
    ext σ
    rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_add_distrib]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [sum_barycentric_internal_boundary_eq_zero, zero_add, sum_barycentric_external_boundary]

/-- Subdivision commutes with the boundary on every actual singular generator. -/
theorem singularSimplexGenerator_subdivision_comm {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X)) :
    (singularSimplexGenerator s ≫ barycentricSubdivisionDegree X (n + 1)) ≫
        (singularChains X).d (n + 1) n =
      (singularSimplexGenerator s ≫ (singularChains X).d (n + 1) n) ≫
        barycentricSubdivisionDegree X n := by
  rw [singularSimplexGenerator_comp_subdivision, singularSimplexGenerator_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
    singularSimplexGenerator_boundary, singularSimplexGenerator_comp_subdivision,
    Finset.smul_sum, smul_smul]
  exact sum_barycentric_boundary s

set_option backward.isDefEq.respectTransparency false in
/-- The actual degreewise operators commute with the singular-chain differential. -/
theorem barycentricSubdivisionDegree_comm (X : Type u) [TopologicalSpace X] (n : ℕ) :
    barycentricSubdivisionDegree X (n + 1) ≫ (singularChains X).d (n + 1) n =
      (singularChains X).d (n + 1) n ≫ barycentricSubdivisionDegree X n := by
  apply (TopCat.toSSet.obj (TopCat.of X)).chainComplex_hom_ext
    (R := ModuleCat.of ℝ (ULift.{u} ℝ))
  intro t
  have h := singularSimplexGenerator_subdivision_comm
    (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n + 1⦌) t)
  simpa only [singularSimplexGenerator, Equiv.symm_apply_apply, Category.assoc] using h

/-- There is no outgoing degree-zero boundary in this natural-number indexed
chain complex. This handles the bottom degree without a fictitious degree `-1`. -/
theorem singularChains_d_zero (X : Type u) [TopologicalSpace X] (k : ℕ) :
    (singularChains X).d 0 k = 0 :=
  (singularChains X).shape 0 k (by simp [ComplexShape.down_Rel])

/-- Geometric barycentric subdivision as an endomorphism of the actual
singular-chain complex, with the chain law proved above. -/
def barycentricSubdivision (X : Type u) [TopologicalSpace X] :
    singularChains X ⟶ singularChains X :=
  ChainComplex.ofHom (barycentricSubdivisionDegree X) (barycentricSubdivisionDegree_comm X)

@[simp]
theorem barycentricSubdivision_f (X : Type u) [TopologicalSpace X] (n : ℕ) :
    (barycentricSubdivision X).f n = barycentricSubdivisionDegree X n := rfl

end GaussBonnetChern
