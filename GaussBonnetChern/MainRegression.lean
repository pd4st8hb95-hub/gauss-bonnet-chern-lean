import GaussBonnetChern.MainTheorem
import GaussBonnetChern.EmptyManifold
import GaussBonnetChern.SingularDisjointUnion

/-! # Regressions for the exact Gauss–Bonnet–Chern statement

The empty example constructs its charted space, finite atlas and smooth metric.
Atlas and orientation regressions use the actual atlas compatibility relations.
Finite disjoint-union Euler additivity uses actual singular homology and obtains
all finite-dimensionality and vanishing hypotheses internally from actual Morse
functions. No finrank default value is used to stand in for finiteness.

The final geometric sigma regression takes an actual smooth metric and oriented
atlas on the sigma manifold. It does not assert that these are automatically
constructed from the component metrics and atlases. The missing construction
interface is a componentwise charted-space/metric/positive-atlas constructor on
the actual topological sigma, with smooth chart inclusion and metric restrictions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle CategoryTheory Module Set
open scoped Manifold ContDiff BigOperators DirectSum

namespace GaussBonnetChern.MainRegression
open DifferentialForm
universe u

section RegisteredMetric
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M] [CompactSpace M] [T2Space M]
  [SecondCountableTopology M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

theorem curvature_eq_chi (hn : 1 ≤ n) (a : FiniteOrientedAtlas n M)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source)) :
    curvatureIntegral n M a ρ = (topologicalEulerCharacteristic M : ℝ) := by
  cases n with
  | zero => omega
  | succ k => exact curvatureIntegral_eq_topologicalEulerCharacteristic k M a ρ hρ

/-- Two actual subordinate partitions on the same atlas give the same
original curvature integral, and both equal the actual Euler characteristic. -/
theorem partition_change (hn : 1 ≤ n) (a : FiniteOrientedAtlas n M)
    (ρ τ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (hτ : τ.IsSubordinate (fun i ↦ (a.chart i).source)) :
    curvatureIntegral n M a ρ = curvatureIntegral n M a τ ∧
      curvatureIntegral n M a τ = (topologicalEulerCharacteristic M : ℝ) := by
  exact ⟨(curvature_eq_chi n M hn a ρ hρ).trans (curvature_eq_chi n M hn a τ hτ).symm,
    curvature_eq_chi n M hn a τ hτ⟩

/-- A genuinely positively compatible replacement atlas preserves the
actual Euler form as well as the original numerical main formula. -/
theorem compatible_atlas_change (hn : 1 ≤ n) (a b : FiniteOrientedAtlas n M)
    (hab : a.Compatible b)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (τ : SmoothPartitionOfUnity (Fin b.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (hτ : τ.IsSubordinate (fun i ↦ (b.chart i).source)) :
    atlasEulerForm n M a (by omega) = atlasEulerForm n M b (by omega) ∧
      curvatureIntegral n M a ρ = curvatureIntegral n M b τ ∧
      curvatureIntegral n M b τ = (topologicalEulerCharacteristic M : ℝ) := by
  exact ⟨atlasEulerForm_eq_of_compatible n M a b hab (by omega),
    (curvature_eq_chi n M hn a ρ hρ).trans (curvature_eq_chi n M hn b τ hτ).symm,
    curvature_eq_chi n M hn b τ hτ⟩

/-- Opposite orientation is the negation of the actual tangent orientation.
The Euler form and the integral of a fixed top form reverse sign, while the
original scalar-curvature formula on either atlas still equals actual chi. -/
theorem opposite_orientation (hn : 1 ≤ n) (a b : FiniteOrientedAtlas n M)
    (hab : a.Opposite b)
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) M univ)
    (τ : SmoothPartitionOfUnity (Fin b.card) (model n) M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source))
    (hτ : τ.IsSubordinate (fun i ↦ (b.chart i).source)) :
    (∀ x, atlasOrientation n M b x = -atlasOrientation n M a x) ∧
      atlasEulerForm n M a (by omega) = -atlasEulerForm n M b (by omega) ∧
      (∀ α : Form (model n) M (2*n), IsSmooth α →
        integralTopForm a ρ α = -integralTopForm b τ α) ∧
      curvatureIntegral n M a ρ = (topologicalEulerCharacteristic M : ℝ) ∧
      curvatureIntegral n M b τ = (topologicalEulerCharacteristic M : ℝ) := by
  refine ⟨?_, atlasEulerForm_neg_of_opposite n M a b hab (by omega),
    fun α hα ↦ integralTopForm_neg_of_opposite n M a b hab ρ τ hρ hτ α hα,
    curvature_eq_chi n M hn a ρ hρ, curvature_eq_chi n M hn b τ hτ⟩
  intro x
  apply (Orientation.ne_iff_eq_neg _ _ ?_).mp
  · exact (atlasOrientation_ne_of_opposite n M a b hab x).symm
  · change Fintype.card (Fin (2*n)) = finrank ℝ (Model n)
    simp [Model]

end RegisteredMetric

section ConcreteEmpty
local instance emptyChartedSpace (n : ℕ) : ChartedSpace (Model n) PEmpty :=
  ChartedSpace.empty (Model n) PEmpty

def emptyAtlas (n : ℕ) : FiniteOrientedAtlas n PEmpty where
  card := 0
  chart := Fin.elim0
  smooth := fun i ↦ Fin.elim0 i
  covers := fun x ↦ isEmptyElim x
  positive_transition := fun i ↦ Fin.elim0 i

def emptyMetric (n : ℕ) : SmoothMetric n PEmpty where
  inner := fun x ↦ isEmptyElim x
  symm := fun x ↦ isEmptyElim x
  pos := fun x ↦ isEmptyElim x
  isVonNBounded := fun x ↦ isEmptyElim x
  contMDiff := by intro x; exact isEmptyElim x

/-- A concrete empty manifold inhabits the same exact all-partitions main
statement in every positive even dimension. -/
theorem empty_main (n : ℕ) (hn : 1 ≤ n) :
    StatementFor n PEmpty (emptyAtlas n) (emptyMetric n) :=
  gaussBonnetChern n hn PEmpty (emptyAtlas n) (emptyMetric n)

theorem empty_euler : topologicalEulerCharacteristic PEmpty = 0 :=
  topologicalEulerCharacteristic_of_isEmpty PEmpty

theorem empty_curvature (n : ℕ) :
    letI : RiemannianBundle (TangentSpace (model n) : PEmpty → Type _) :=
      ⟨(emptyMetric n).toRiemannianMetric⟩
    ∀ ρ : SmoothPartitionOfUnity (Fin (emptyAtlas n).card) (model n) PEmpty univ,
      curvatureIntegral n PEmpty (emptyAtlas n) ρ = 0 := by
  letI : RiemannianBundle (TangentSpace (model n) : PEmpty → Type _) :=
    ⟨(emptyMetric n).toRiemannianMetric⟩
  intro ρ
  exact curvatureIntegral_eq_zero_of_isEmpty n PEmpty (emptyAtlas n) ρ

end ConcreteEmpty

section FiniteDisjointUnion
variable (n : ℕ) {ι : Type u} [Fintype ι] (X : ι → Type u)
  [componentTopology : ∀ i, TopologicalSpace (X i)]
  [componentCharts : ∀ i, ChartedSpace (Model n) (X i)]
  [componentManifold : ∀ i, IsManifold (model n) ∞ (X i)]
  [componentCompact : ∀ i, CompactSpace (X i)]
  [componentHausdorff : ∀ i, T2Space (X i)]
  [componentMetric : ∀ i, RiemannianBundle (TangentSpace (model n) : X i → Type _)]
  [componentSmoothMetric : ∀ i, IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : X i → Type _)]

/-- Actual Morse theory supplies the finite and vanishing hypotheses
for every component; no finite-dimensionality hypothesis is an input. -/
theorem component_homology_bound (i : ι) : FiniteSingularHomologyBound (X i) (2*n) := by
  obtain ⟨f, hf, hfin, hb, hdet, he⟩ := exists_morse_gradient_topological_index n (X i)
  exact hb

include n componentCharts componentManifold componentCompact componentHausdorff
  componentMetric componentSmoothMetric in
private theorem sigma_homology_finrank (k : ℕ) :
    finrank ℝ (singularHomology (Σ i, X i) k) = ∑ i, finrank ℝ (singularHomology (X i) k) := by
  letI : ∀ i, FiniteDimensional ℝ (singularHomology (X i) k) :=
    fun i ↦ (component_homology_bound n X i).finite k
  rw [(singularHomologySigmaIso X k).toLinearEquiv.finrank_eq]
  change finrank ℝ (⨁ i, singularHomology (X i) k) = _
  exact Module.finrank_directSum (R := ℝ) (fun i ↦ singularHomology (X i) k)

theorem sigma_homology_bound : FiniteSingularHomologyBound (Σ i, X i) (2*n) := by
  have hfd (k : ℕ) : FiniteDimensional ℝ (singularHomology (Σ i, X i) k) := by
    letI : ∀ i, FiniteDimensional ℝ (singularHomology (X i) k) :=
      fun i ↦ (component_homology_bound n X i).finite k
    exact (singularHomologySigmaIso X k).toLinearEquiv.symm.finiteDimensional
  refine ⟨hfd, ?_⟩
  intro k hk
  letI := hfd k
  letI : Subsingleton (singularHomology (Σ i, X i) k) :=
    (Module.finrank_zero_iff (R := ℝ) (M := singularHomology (Σ i, X i) k)).mp (by
    rw [sigma_homology_finrank n X k]
    apply Finset.sum_eq_zero
    intro i _
    letI := ModuleCat.subsingleton_of_isZero ((component_homology_bound n X i).vanishing k hk)
    exact Module.finrank_eq_zero_of_subsingleton _ _)
  exact ModuleCat.isZero_of_subsingleton _

include n componentCharts componentManifold componentCompact componentHausdorff
  componentMetric componentSmoothMetric in
/-- Euler additivity for the actual topological finite sigma. The finite
homology and common vanishing bound are constructed before summation. This
includes empty components, an empty index type and disconnected unions. -/
theorem sigma_euler_additivity :
    topologicalEulerCharacteristic (Σ i, X i) = ∑ i, topologicalEulerCharacteristic (X i) := by
  have heσ := homologyEulerChar_eq_sum_range_of_vanishing (singularChains (Σ i, X i)) (2*n)
    (fun k hk ↦ ModuleCat.subsingleton_of_isZero ((sigma_homology_bound n X).vanishing k hk))
  have he (i : ι) := homologyEulerChar_eq_sum_range_of_vanishing (singularChains (X i)) (2*n)
    (fun k hk ↦ ModuleCat.subsingleton_of_isZero ((component_homology_bound n X i).vanishing k hk))
  unfold topologicalEulerCharacteristic
  rw [heσ]
  simp_rw [sigma_homology_finrank n X, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ ↦ (he i).symm)

variable [ChartedSpace (Model n) (Σ i, X i)] [IsManifold (model n) ∞ (Σ i, X i)]
  [CompactSpace (Σ i, X i)] [T2Space (Σ i, X i)] [SecondCountableTopology (Σ i, X i)]

/-- An actual metric and oriented atlas on the finite sigma receive the
original main statement. Componentwise construction of this geometric data
is not asserted by this regression. -/
theorem sigma_main (hn : 1 ≤ n) (a : FiniteOrientedAtlas n (Σ i, X i))
    (g : SmoothMetric n (Σ i, X i)) : StatementFor n (Σ i, X i) a g :=
  gaussBonnetChern n hn (Σ i, X i) a g

/-- The full original curvature integral on an actually equipped sigma
manifold equals the sum of the independently defined component Euler
characteristics; all component homology finiteness is proved internally. -/
theorem sigma_curvature_euler_additivity (hn : 1 ≤ n)
    [RiemannianBundle (TangentSpace (model n) : (Σ i, X i) → Type _)]
    [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
      (TangentSpace (model n) : (Σ i, X i) → Type _)]
    (a : FiniteOrientedAtlas n (Σ i, X i))
    (ρ : SmoothPartitionOfUnity (Fin a.card) (model n) (Σ i, X i) univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (a.chart i).source)) :
    curvatureIntegral n (Σ i, X i) a ρ = ∑ i, (topologicalEulerCharacteristic (X i) : ℝ) := by
  rw [curvature_eq_chi n (Σ i, X i) hn a ρ hρ, sigma_euler_additivity n X]
  push_cast
  rfl

end FiniteDisjointUnion
end GaussBonnetChern.MainRegression
