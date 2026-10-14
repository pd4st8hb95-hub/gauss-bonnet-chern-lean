import GaussBonnetChern.Topology
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-! # Geometric barycentric subsimplices of actual singular simplices

The domains are Mathlib's `Convexity.StdSimplex`, exactly the standard simplices
used by `TopCat.toSSet`. A permutation determines the nested initial faces and
their barycenters. Their affine extension is a continuous self-map of the
standard simplex, so it can be precomposed with an actual singular simplex.

The geometric constructions below are not an assertion that the categorical
subdivision functor provides small-chain support control. The signed boundary
cancellation and the small-chain homotopy theorem are separate obligations.
-/

noncomputable section

universe u v

namespace GaussBonnetChern

open CategoryTheory Convexity
open scoped BigOperators Simplicial

section AffineExtension

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

omit [Fintype J] in
/-- Coordinates of the affine extension of any finite family of simplex points. -/
theorem simplexAffine_weights (v : I → StdSimplex ℝ J) (x : StdSimplex ℝ I) (j : J) :
    (StdSimplex.affineMapMk v x).weights j = ∑ i, x.weights i * (v i).weights j := by
  classical
  simp [StdSimplex.affineMapMk_apply, iConvexComb, StdSimplex.weights_sConvexComb,
    StdSimplex.weights_map, Finsupp.sum_mapDomain_index, Finsupp.sum_fintype,
    add_smul]

/-- The affine extension is continuous for the actual standard-simplex topology. -/
theorem continuous_simplexAffine (v : I → StdSimplex ℝ J) :
    Continuous (StdSimplex.affineMapMk (R := ℝ) v) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ J).continuous_iff]
  apply continuous_pi
  intro j
  change Continuous (fun x ↦ (StdSimplex.affineMapMk v x).weights j)
  simp only [simplexAffine_weights]
  fun_prop

/-- The continuous affine simplex specified by its vertices. -/
def simplexAffineContinuous (v : I → StdSimplex ℝ J) :
    C(StdSimplex ℝ I, StdSimplex ℝ J) :=
  ⟨StdSimplex.affineMapMk (R := ℝ) v, continuous_simplexAffine v⟩

@[simp]
theorem simplexAffineContinuous_single (v : I → StdSimplex ℝ J) (i : I) :
    simplexAffineContinuous v (.single i) = v i := by
  change StdSimplex.affineMapMk (R := ℝ) v (.single i) = v i
  exact StdSimplex.affineMapMk_single (R := ℝ) v i

/-- Restriction along a vertex map agrees with the affine extension of the
restricted vertex family. In particular this applies to every face inclusion. -/
theorem simplexAffineContinuous_comp_vertexMap (v : I → StdSimplex ℝ J) (f : K → I) :
    (simplexAffineContinuous v).comp ⟨StdSimplex.map f, StdSimplex.continuous_map ℝ f⟩ =
      simplexAffineContinuous (v ∘ f) := by
  have h : (StdSimplex.affineMapMk (R := ℝ) v).comp (StdSimplex.affineMap (R := ℝ) f) =
      StdSimplex.affineMapMk (R := ℝ) (v ∘ f) := by
    apply StdSimplex.affineMap_ext
    intro k
    simp
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun g : ConvexSpace.AffineMap ℝ (StdSimplex ℝ K) (StdSimplex ℝ J) ↦ g x) h

end AffineExtension

/-- Explicit coordinates of a face barycenter. -/
theorem subBarycenter_weights (I : Type*) [DecidableEq I]
    (s : Finset I) (hs : s.Nonempty) (j : I) :
    (StdSimplex.subBarycenter (K := ℝ) s hs).weights j =
      if j ∈ s then (s.card : ℝ)⁻¹ else 0 := by
  simp [StdSimplex.weights_subBarycenter, Finsupp.single_apply]

/-- Initial faces of a permutation flag. -/
def barycentricFlagFace {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    Finset (Fin (n + 1)) :=
  (Finset.Iic i).image σ

theorem barycentricFlagFace_nonempty {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (barycentricFlagFace σ i).Nonempty := by
  exact ⟨σ 0, Finset.mem_image.mpr ⟨0, Finset.mem_Iic.mpr (Fin.zero_le i), rfl⟩⟩

theorem barycentricFlagFace_card {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (barycentricFlagFace σ i).card = i.val + 1 := by
  rw [barycentricFlagFace, Finset.card_image_of_injective _ σ.injective, Fin.card_Iic]

theorem barycentricFlagFace_mono {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) {i j : Fin (n + 1)} (h : i ≤ j) :
    barycentricFlagFace σ i ⊆ barycentricFlagFace σ j :=
  Finset.image_subset_image (Finset.Iic_subset_Iic.mpr h)

/-- The vertex of a barycentric subsimplex indexed by a stage in the flag. -/
def barycentricFlagVertex {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) : StdSimplex ℝ (Fin (n + 1)) :=
  StdSimplex.subBarycenter (barycentricFlagFace σ i) (barycentricFlagFace_nonempty σ i)

theorem barycentricFlagVertex_weights {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    (barycentricFlagVertex σ i).weights j =
      if σ.symm j ≤ i then ((i.val + 1 : ℕ) : ℝ)⁻¹ else 0 := by
  rw [barycentricFlagVertex, subBarycenter_weights, barycentricFlagFace_card]
  congr 1
  simp only [barycentricFlagFace, Finset.mem_image, Finset.mem_Iic]
  apply propext
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨σ.symm j, h, by simp⟩

/-- The actual affine barycentric subsimplex associated with a permutation. -/
def barycentricSimplex {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 1))) :=
  simplexAffineContinuous (barycentricFlagVertex σ)

@[simp]
theorem barycentricSimplex_single {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    barycentricSimplex σ (.single i) = barycentricFlagVertex σ i :=
  simplexAffineContinuous_single _ _

/-- A genuine subsimplex of a continuous singular simplex. -/
def barycentricSingularSimplex {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 1)), X)) (σ : Equiv.Perm (Fin (n + 1))) :
    C(StdSimplex ℝ (Fin (n + 1)), X) :=
  s.comp (barycentricSimplex σ)

/-- Every barycentric subsimplex has image inside the original singular simplex. -/
theorem barycentricSingularSimplex_range_subset {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 1)), X)) (σ : Equiv.Perm (Fin (n + 1))) :
    Set.range (barycentricSingularSimplex s σ) ⊆ Set.range s := by
  rintro _ ⟨x, rfl⟩
  exact ⟨barycentricSimplex σ x, rfl⟩

/-- The coordinate `ℓ¹` distance on the finite standard simplex. -/
def simplexL1Distance {I : Type*} [Fintype I] (x y : StdSimplex ℝ I) : ℝ :=
  ∑ i, |x.weights i - y.weights i|

theorem simplexL1Distance_le_two {I : Type*} [Fintype I] (x y : StdSimplex ℝ I) :
    simplexL1Distance x y ≤ 2 := by
  calc
    _ ≤ ∑ i, (x.weights i + y.weights i) := by
      apply Finset.sum_le_sum
      intro i _
      exact abs_le.mpr ⟨by linarith [x.weights_nonneg i], by linarith [y.weights_nonneg i]⟩
    _ = 2 := by norm_num [Finset.sum_add_distrib]

/-- The library's product metric on simplex coordinates is bounded by the
coordinate `ℓ¹` distance. The simplex topology is induced by these coordinates. -/
theorem simplexCoordinateDist_le_l1 {I : Type*} [Fintype I] (x y : StdSimplex ℝ I) :
    dist (fun i ↦ x.weights i) (fun i ↦ y.weights i) ≤ simplexL1Distance x y := by
  apply (dist_pi_le_iff (show 0 ≤ simplexL1Distance x y from
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))).mpr
  intro i
  rw [Real.dist_eq]
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (x.weights j - y.weights j)) (Finset.mem_univ i)

/-- A common vertex weight yields an explicit contraction of coordinate `ℓ¹`
distance under affine extension. This is a finite stochastic-matrix estimate. -/
theorem simplexAffine_l1_contraction {I J : Type*} [Fintype I] [Fintype J]
    (v : I → StdSimplex ℝ J) (j₀ : J) (c : ℝ)
    (hcommon : ∀ i, c ≤ (v i).weights j₀) (x y : StdSimplex ℝ I) :
    simplexL1Distance (StdSimplex.affineMapMk v x) (StdSimplex.affineMapMk v y) ≤
      (1 - c) * simplexL1Distance x y := by
  classical
  let q (i : I) (j : J) : ℝ := (v i).weights j - if j = j₀ then c else 0
  have hq (i : I) (j : J) : 0 ≤ q i j := by
    dsimp [q]
    split_ifs with h
    · subst j
      exact sub_nonneg.mpr (hcommon i)
    · simp
  have htotal (i : I) : ∑ j, q i j = 1 - c := by
    simp [q, Finset.sum_sub_distrib]
  have hdiff (j : J) :
      (StdSimplex.affineMapMk v x).weights j - (StdSimplex.affineMapMk v y).weights j =
        ∑ i, (x.weights i - y.weights i) * q i j := by
    simp only [simplexAffine_weights, q, mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul, x.total_of_fintype, y.total_of_fintype]
    ring
  unfold simplexL1Distance
  simp_rw [hdiff]
  calc
    _ ≤ ∑ j, ∑ i, |x.weights i - y.weights i| * q i j := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ i, |(x.weights i - y.weights i) * q i j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_of_nonneg (hq i j)]
    _ = ∑ i, |x.weights i - y.weights i| * (1 - c) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, htotal]
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- Every vertex in a permutation flag gives its first vertex weight at least
`1/(n+1)`. This statement holds in symbolic dimension, including dimension zero. -/
theorem barycentricFlagVertex_commonWeight {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    ((n + 1 : ℕ) : ℝ)⁻¹ ≤ (barycentricFlagVertex σ i).weights (σ 0) := by
  rw [barycentricFlagVertex_weights]
  simp only [Equiv.symm_apply_apply, Fin.zero_le, ite_true]
  simpa only [one_div] using one_div_le_one_div_of_le
    (show (0 : ℝ) < ((i.val + 1 : ℕ) : ℝ) by positivity)
    (show ((i.val + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast i.isLt)

/-- Symbolic-dimensional mesh contraction for a genuine barycentric subsimplex. -/
theorem barycentricSimplex_l1_contraction {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (x y : StdSimplex ℝ (Fin (n + 1))) :
    simplexL1Distance (barycentricSimplex σ x) (barycentricSimplex σ y) ≤
      ((n : ℝ) / (n + 1)) * simplexL1Distance x y := by
  have hfactor : 1 - ((n + 1 : ℕ) : ℝ)⁻¹ = (n : ℝ) / (n + 1) := by
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  simpa only [barycentricSimplex, simplexAffineContinuous, ContinuousMap.coe_mk, hfactor] using
    simplexAffine_l1_contraction (barycentricFlagVertex σ) (σ 0) _
      (barycentricFlagVertex_commonWeight σ) x y

/-- Iterated geometric subdivision, composing a new subsimplex on the right.
Thus each successive image lies in the preceding image. -/
def iteratedBarycentricSimplex {n : ℕ}
    (σ : ℕ → Equiv.Perm (Fin (n + 1))) (k : ℕ) :
    C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 1))) := match k with
  | 0 => ContinuousMap.id _
  | k + 1 => (iteratedBarycentricSimplex σ k).comp (barycentricSimplex (σ k))

theorem iteratedBarycentricSimplex_l1_contraction {n : ℕ}
    (σ : ℕ → Equiv.Perm (Fin (n + 1))) (k : ℕ)
    (x y : StdSimplex ℝ (Fin (n + 1))) :
    simplexL1Distance (iteratedBarycentricSimplex σ k x) (iteratedBarycentricSimplex σ k y) ≤
      ((n : ℝ) / (n + 1)) ^ k * simplexL1Distance x y := by
  have hn : 0 ≤ (n : ℝ) / (n + 1) := by positivity
  induction k generalizing x y with
  | zero => simp [iteratedBarycentricSimplex]
  | succ k ih =>
      change simplexL1Distance
          (iteratedBarycentricSimplex σ k (barycentricSimplex (σ k) x))
          (iteratedBarycentricSimplex σ k (barycentricSimplex (σ k) y)) ≤ _
      calc
        _ ≤ ((n : ℝ) / (n + 1)) ^ k *
              simplexL1Distance (barycentricSimplex (σ k) x) (barycentricSimplex (σ k) y) := ih _ _
        _ ≤ ((n : ℝ) / (n + 1)) ^ k *
              (((n : ℝ) / (n + 1)) * simplexL1Distance x y) :=
          mul_le_mul_of_nonneg_left (barycentricSimplex_l1_contraction (σ k) x y) (pow_nonneg hn k)
        _ = _ := by rw [pow_succ, mul_assoc]

/-- A uniform geometric mesh bound after any sequence of `k` subdivisions. -/
theorem iteratedBarycentricSimplex_mesh_bound {n : ℕ}
    (σ : ℕ → Equiv.Perm (Fin (n + 1))) (k : ℕ)
    (x y : StdSimplex ℝ (Fin (n + 1))) :
    simplexL1Distance (iteratedBarycentricSimplex σ k x) (iteratedBarycentricSimplex σ k y) ≤
      2 * ((n : ℝ) / (n + 1)) ^ k := by
  calc
    _ ≤ ((n : ℝ) / (n + 1)) ^ k * simplexL1Distance x y :=
      iteratedBarycentricSimplex_l1_contraction σ k x y
    _ ≤ ((n : ℝ) / (n + 1)) ^ k * 2 :=
      mul_le_mul_of_nonneg_left (simplexL1Distance_le_two x y) (by positivity)
    _ = _ := mul_comm _ _

/-- The iterated mesh bound also holds in the actual product metric that
induces the topology of the finite standard simplex. -/
theorem iteratedBarycentricSimplex_coordinate_mesh_bound {n : ℕ}
    (σ : ℕ → Equiv.Perm (Fin (n + 1))) (k : ℕ)
    (x y : StdSimplex ℝ (Fin (n + 1))) :
    dist (fun i ↦ (iteratedBarycentricSimplex σ k x).weights i)
        (fun i ↦ (iteratedBarycentricSimplex σ k y).weights i) ≤
      2 * ((n : ℝ) / (n + 1)) ^ k :=
  (simplexCoordinateDist_le_l1 _ _).trans (iteratedBarycentricSimplex_mesh_bound σ k x y)

theorem barycentricContractionFactor_lt_one (n : ℕ) : (n : ℝ) / (n + 1) < 1 := by
  apply (div_lt_one (by positivity)).mpr
  linarith

/-- The corresponding generator in the actual project singular-chain complex,
using Mathlib's continuous-simplex/singular-set equivalence. -/
def singularSimplexGenerator {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 1)), X)) :
    ModuleCat.of ℝ (ULift.{u} ℝ) ⟶ (singularChains X).X n :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).symm s)

/-- The signed degreewise subdivision operator on the actual singular chains.
Commutation with the chain differential is not asserted by this definition. -/
def barycentricSubdivisionDegree (X : Type u) [TopologicalSpace X] (n : ℕ) :
    (singularChains X).X n ⟶ (singularChains X).X n :=
  Limits.Sigma.desc (fun t ↦
    ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
      singularSimplexGenerator (barycentricSingularSimplex
        (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌) t) σ))

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise operator sends an actual singular generator to the signed
sum of its geometric barycentric subsimplices. -/
theorem singularSimplexGenerator_comp_subdivision {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 1)), X)) :
    singularSimplexGenerator s ≫ barycentricSubdivisionDegree X n =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
        singularSimplexGenerator (barycentricSingularSimplex s σ) := by
  simp only [singularSimplexGenerator, barycentricSubdivisionDegree, SSet.ιChainComplex]
  rw [Limits.Sigma.ι_comp_desc]
  simp

/-- Adjacent transposition preserves every initial segment except the one
ending at the earlier of the two transposed indices. -/
theorem adjacentSwap_le_iff {n : ℕ} (i : Fin (n + 1))
    (k x : Fin (n + 2)) (hk : k ≠ i.castSucc) :
    Equiv.swap i.castSucc i.succ x ≤ k ↔ x ≤ k := by
  have hkval : k.val ≠ i.val := fun h ↦ hk (Fin.ext h)
  by_cases hxa : x = i.castSucc
  · subst x
    rw [Equiv.swap_apply_left]
    change i.val + 1 ≤ k.val ↔ i.val ≤ k.val
    omega
  by_cases hxb : x = i.succ
  · subst x
    rw [Equiv.swap_apply_right]
    change i.val ≤ k.val ↔ i.val + 1 ≤ k.val
    omega
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- The paired flags have identical barycenters away from the omitted
interior-face stage. This is the geometric input to internal-face cancellation. -/
theorem barycentricFlagVertex_adjacentSwap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ i.castSucc) :
    barycentricFlagVertex (σ * Equiv.swap i.castSucc i.succ) k =
      barycentricFlagVertex σ k := by
  ext j
  rw [barycentricFlagVertex_weights, barycentricFlagVertex_weights]
  change (if Equiv.swap i.castSucc i.succ (σ.symm j) ≤ k then _ else _) = _
  simp only [adjacentSwap_le_iff i k (σ.symm j) hk]

/-- Actual face restrictions of paired geometric subsimplices are identical.
Only the interior-face identification is asserted here, not the chain identity. -/
theorem barycentricSimplex_internalFace_pair {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    (barycentricSimplex (σ * Equiv.swap i.castSucc i.succ)).comp
        ⟨StdSimplex.map i.castSucc.succAbove,
          StdSimplex.continuous_map ℝ i.castSucc.succAbove⟩ =
      (barycentricSimplex σ).comp
        ⟨StdSimplex.map i.castSucc.succAbove,
          StdSimplex.continuous_map ℝ i.castSucc.succAbove⟩ := by
  change (simplexAffineContinuous _).comp _ = (simplexAffineContinuous _).comp _
  rw [simplexAffineContinuous_comp_vertexMap, simplexAffineContinuous_comp_vertexMap]
  congr 1
  funext k
  exact barycentricFlagVertex_adjacentSwap σ i _ (Fin.succAbove_ne _ _)

/-- Adjacent paired flags carry opposite subdivision coefficients. -/
theorem barycentric_internalFace_opposite_sign {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    (Equiv.Perm.sign (σ * Equiv.swap i.castSucc i.succ) : ℤ) =
      -(Equiv.Perm.sign σ : ℤ) := by
  have hi : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hi]

/-- The `i`th face of an actual barycentric singular subsimplex. -/
def barycentricSingularFace {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X))
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 2)) :
    C(StdSimplex ℝ (Fin (n + 1)), X) :=
  (barycentricSingularSimplex s σ).comp
    ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ i.succAbove⟩

theorem barycentricSingularFace_internal_pair {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X))
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    barycentricSingularFace s (σ * Equiv.swap i.castSucc i.succ) i.castSucc =
      barycentricSingularFace s σ i.castSucc := by
  apply ContinuousMap.ext
  intro x
  exact congrArg s (congrArg
    (fun f : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 2))) ↦ f x)
    (barycentricSimplex_internalFace_pair σ i))

/-- Paired internal faces cancel as morphisms into the actual singular-chain
group. This is local boundary cancellation, not yet the full subdivision chain map. -/
theorem barycentric_internalFace_generator_cancel {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : C(StdSimplex ℝ (Fin (n + 2)), X))
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    (Equiv.Perm.sign σ : ℤ) • singularSimplexGenerator (barycentricSingularFace s σ i.castSucc) +
        (Equiv.Perm.sign (σ * Equiv.swap i.castSucc i.succ) : ℤ) •
          singularSimplexGenerator
            (barycentricSingularFace s (σ * Equiv.swap i.castSucc i.succ) i.castSucc) = 0 := by
  rw [barycentricSingularFace_internal_pair, barycentric_internalFace_opposite_sign]
  simp

/-- Iteration preserves nested geometric supports. -/
theorem iteratedBarycentricSimplex_range_succ_subset {n : ℕ}
    (σ : ℕ → Equiv.Perm (Fin (n + 1))) (k : ℕ) :
    Set.range (iteratedBarycentricSimplex σ (k + 1)) ⊆
      Set.range (iteratedBarycentricSimplex σ k) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨barycentricSimplex (σ k) x, rfl⟩

end GaussBonnetChern
