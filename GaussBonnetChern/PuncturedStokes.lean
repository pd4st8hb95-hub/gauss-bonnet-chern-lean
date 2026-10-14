import GaussBonnetChern.PuncturedAdaptedAtlas
import GaussBonnetChern.BoundarySphereTrace
import GaussBonnetChern.SphereChartIntegral
import GaussBonnetChern.LocalFormPullback

/-! # Stokes on the actual complement of finitely many coordinate balls

The finite adapted charts and the subordinate partition are constructed from
the closed punctured domain. Their boundary weights restrict to a genuine
partition on each deleted sphere, so the coordinate lower-face integrals fold
to the negative outward sphere integral.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory Module Filter
open scoped Manifold ContDiff BigOperators Topology
namespace GaussBonnetChern.PuncturedStokes
open DifferentialForm PuncturedManifold PuncturedAdaptedAtlas
  RadialBoundaryCharts BoundarySphereTrace FiniteChartStokes StokesLocalization
  ManifoldBoundaryStokes

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Model (n+1)) M] [IsManifold (model (n+1)) ∞ M]
  {ι : Type*} [Fintype ι]

local instance sphereDimension :
    Fact (finrank ℝ (Model (n+1)) = (2*n+1)+1) :=
  ⟨by simp [Model, Nat.mul_add, Nat.add_assoc]⟩

variable (a : FiniteOrientedAtlas (n+1) M) (j : ι → Fin a.card)
  (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
  (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (j i)).target)
  (hdis : Pairwise (fun i k ↦ Disjoint
    (coordinateClosedBall (a.chart (j i)) (center i) (r i))
    (coordinateClosedBall (a.chart (j k)) (center k) (r k))))

/-- The finite partition written in the explicit three-family index. -/
def familyWeight
    (ρ : SmoothPartitionOfUnity
      (Fin (adaptedAtlas a j center r hr hcover hdis).atlas.card)
      (model (n+1)) M univ) (q : FamilyIndex a ι) : M → ℝ :=
  ρ (Fintype.equivFin (FamilyIndex a ι) q)

include hr hcover hdis

/-- The sphere is part of the actual frontier, including its membership
in the closed integration domain. -/
theorem sphereEmbedding_mem_frontier (i : ι) (u : sphere (0 : Model (n+1)) 1) :
    sphereEmbedding (a.chart (j i)) (center i) (r i) u ∈
      frontier (puncturedDomain (deletedChartFamily a j) center r) := by
  rw [frontier_puncturedDomain _ _ _ (fun i ↦ (hr i).ne') hcover hdis]
  exact mem_iUnion.mpr ⟨i,
    sphereEmbedding_mem_coordinateSphere _ _ _ (hr i) (hcover i) u⟩

theorem sphereEmbedding_mem_domain (i : ι) (u : sphere (0 : Model (n+1)) 1) :
    sphereEmbedding (a.chart (j i)) (center i) (r i) u ∈
      puncturedDomain (deletedChartFamily a j) center r :=
  (isClosed_puncturedDomain _ _ _).frontier_subset
    (sphereEmbedding_mem_frontier a j center r hr hcover hdis i u)

/-- Along a fixed deleted sphere all partition pieces except its own radial
chart family vanish. This follows from actual chart sources and disjointness. -/
theorem familyWeight_eq_zero_on_other_families
    (ρ : SmoothPartitionOfUnity
      (Fin (adaptedAtlas a j center r hr hcover hdis).atlas.card)
      (model (n+1)) M univ)
    (hρ : ρ.IsSubordinate (fun k ↦
      ((adaptedAtlas a j center r hr hcover hdis).atlas.chart k).source))
    (i : ι) (u : sphere (0 : Model (n+1)) 1) (q : FamilyIndex a ι)
    (hq : ∀ l, q ≠ Sum.inr (Sum.inr (i,l))) :
    familyWeight a j center r hr hcover hdis ρ q
      (sphereEmbedding (a.chart (j i)) (center i) (r i) u) = 0 := by
  classical
  let x := sphereEmbedding (a.chart (j i)) (center i) (r i) u
  have hxf := sphereEmbedding_mem_frontier a j center r hr hcover hdis i u
  have hxΩ := sphereEmbedding_mem_domain a j center r hr hcover hdis i u
  by_contra hz
  have hx : x ∈ (familyChart a j center r hr hcover q).source := by
    rw [← adaptedAtlas_chart_reindex a j center r hr hcover hdis q]
    exact hρ _ (subset_tsupport _ hz)
  rcases q with k | (k | ⟨i',l⟩)
  · exact hx.2 hxΩ
  · exact hxf.2 hx.2
  · have hne : i ≠ i' := by
      intro heq
      subst i'
      exact hq l rfl
    have hxcb := sphereEmbedding_mem_coordinateClosedBall
      (a.chart (j i)) (center i) (r i) (hr i) (hcover i) u
    exact hx.2 (mem_iUnion.mpr ⟨⟨i,hne⟩, hxcb⟩)

/-- The ambient partition restricts to sum one on each deleted sphere. -/
theorem boundary_weights_sum_eq_one
    (ρ : SmoothPartitionOfUnity
      (Fin (adaptedAtlas a j center r hr hcover hdis).atlas.card)
      (model (n+1)) M univ)
    (hρ : ρ.IsSubordinate (fun k ↦
      ((adaptedAtlas a j center r hr hcover hdis).atlas.chart k).source))
    (i : ι) (u : sphere (0 : Model (n+1)) 1) :
    (∑ l, familyWeight a j center r hr hcover hdis ρ (Sum.inr (Sum.inr (i,l)))
      (sphereEmbedding (a.chart (j i)) (center i) (r i) u)) = 1 := by
  classical
  let x := sphereEmbedding (a.chart (j i)) (center i) (r i) u
  have hall : ∑ q : FamilyIndex a ι,
      familyWeight a j center r hr hcover hdis ρ q x = 1 := by
    let ρ' : SmoothPartitionOfUnity (Fin (Fintype.card (FamilyIndex a ι)))
      (model (n+1)) M univ := ρ
    calc
      _ = ∑ q : FamilyIndex a ι, ρ' (Fintype.equivFin (FamilyIndex a ι) q) x := rfl
      _ = ∑ k, ρ' k x := Fintype.sum_equiv (Fintype.equivFin (FamilyIndex a ι))
        (fun q ↦ ρ' (Fintype.equivFin (FamilyIndex a ι) q) x)
        (fun k ↦ ρ' k x) (fun _ ↦ rfl)
      _ = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ'.sum_eq_one (mem_univ x)
  have hzero (q : FamilyIndex a ι) (hq : ∀ l, q ≠ Sum.inr (Sum.inr (i,l))) :=
    familyWeight_eq_zero_on_other_families a j center r hr hcover hdis ρ hρ i u q hq
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type] at hall
  have ho : ∀ k, familyWeight a j center r hr hcover hdis ρ (Sum.inl k) x = 0 :=
    fun k ↦ hzero _ (by intro l h; cases h)
  have hi : ∀ k, familyWeight a j center r hr hcover hdis ρ (Sum.inr (Sum.inl k)) x = 0 :=
    fun k ↦ hzero _ (by intro l h; cases h)
  simp only [ho,hi,Finset.sum_const_zero,zero_add] at hall
  have hf : (∑ i', ∑ l,
      familyWeight a j center r hr hcover hdis ρ (Sum.inr (Sum.inr (i',l))) x) =
      ∑ l, familyWeight a j center r hr hcover hdis ρ (Sum.inr (Sum.inr (i,l))) x := by
    apply Finset.sum_eq_single i
    · intro i' _ hne
      apply Finset.sum_eq_zero
      intro l _
      exact hzero _ (fun l' h ↦ hne
        (congrArg Prod.fst (Sum.inr.inj (Sum.inr.inj h))))
    · intro h
      exact False.elim (h (Finset.mem_univ i))
  rwa [hf] at hall

theorem boundary_weight_support
    (ρ : SmoothPartitionOfUnity
      (Fin (adaptedAtlas a j center r hr hcover hdis).atlas.card)
      (model (n+1)) M univ)
    (hρ : ρ.IsSubordinate (fun k ↦
      ((adaptedAtlas a j center r hr hcover hdis).atlas.chart k).source))
    (i : ι) (l : Fin (boundarySphereAtlas n).card) :
    Function.support (fun u ↦
      familyWeight a j center r hr hcover hdis ρ (Sum.inr (Sum.inr (i,l)))
        (sphereEmbedding (a.chart (j i)) (center i) (r i) u)) ⊆
      ((boundarySphereAtlas n).chart l).source := by
  intro u hu
  apply (sphereEmbedding_mem_puncturedBoundaryChart_source_iff
    (deletedChartFamily a j) center r hr hcover hdis i (sphereWitness n)
    ((boundarySphereAtlas n).chart l) u).mp
  change sphereEmbedding (a.chart (j i)) (center i) (r i) u ∈
    (familyChart a j center r hr hcover (Sum.inr (Sum.inr (i,l)))).source
  rw [← adaptedAtlas_chart_reindex a j center r hr hcover hdis]
  exact hρ _ (subset_tsupport _ hu)

/-- The entire radial chart family of one deleted sphere folds to its true
outward sphere integral, with the punctured domain's inner-boundary sign. -/
theorem lowerFace_integrals_on_one_sphere
    (ρ : SmoothPartitionOfUnity
      (Fin (adaptedAtlas a j center r hr hcover hdis).atlas.card)
      (model (n+1)) M univ)
    (hρ : ρ.IsSubordinate (fun k ↦
      ((adaptedAtlas a j center r hr hcover hdis).atlas.chart k).source))
    (β : Form (model (n+1)) M (2*n+1)) (hβ : IsSmooth β) (i : ι) :
    (∑ l, lowerFaceIntegral
      (familyChart a j center r hr hcover (Sum.inr (Sum.inr (i,l))))
      (weightForm (familyWeight a j center r hr hcover hdis ρ (Sum.inr (Sum.inr (i,l)))) β)) =
      -sphereFormIntegral (EuclideanSpace.basisFun (Fin (2*(n+1))) ℝ)
        (pullback (I := 𝓡 (2*n+1)) (I' := model (n+1))
          (sphereEmbedding (a.chart (j i)) (center i) (r i)) β) := by
  classical
  let F := sphereEmbedding (a.chart (j i)) (center i) (r i)
  have hF := contMDiff_sphereEmbedding (a.chart (j i)) (a.smooth (j i))
    (center i) (r i) (hr i) (hcover i)
  let τ : Fin (boundarySphereAtlas n).card → sphere (0 : Model (n+1)) 1 → ℝ :=
    fun l u ↦ familyWeight a j center r hr hcover hdis ρ (Sum.inr (Sum.inr (i,l))) (F u)
  have ht (l : Fin (boundarySphereAtlas n).card) : Continuous (τ l) :=
    (ρ (Fintype.equivFin (FamilyIndex a ι) (Sum.inr (Sum.inr (i,l))))).contMDiff.continuous.comp
      hF.continuous
  calc
    _ = -GenericFormIntegration.integral (boundarySphereAtlas n).chart τ
        (pullback (I := 𝓡 (2*n+1)) (I' := model (n+1)) F β) := by
      unfold GenericFormIntegration.integral
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro l _
      exact lowerFaceIntegral_puncturedBoundaryChart (deletedChartFamily a j)
        (fun i ↦ a.smooth (j i)) center r hr hcover hdis i (sphereWitness n)
        ((boundarySphereAtlas n).chart l) ((boundarySphereAtlas n).smooth l)
        (familyWeight a j center r hr hcover hdis ρ (Sum.inr (Sum.inr (i,l)))) β
    _ = _ := congrArg Neg.neg (sphereFormIntegral_eq_finite_chart_integral
      (EuclideanSpace.basisFun (Fin (2*(n+1))) ℝ)
      (boundarySphereAtlas n).chart (boundarySphereAtlas n).smooth
      (boundarySphereAtlas n).positive_density τ ht
      (boundary_weight_support a j center r hr hcover hdis ρ hρ i)
      (boundary_weights_sum_eq_one a j center r hr hcover hdis ρ hρ i)
      _ (hβ.pullback F hF))

/-- Stokes on the actual compact punctured domain, for a smooth form.
The original ambient orientation and integral are preserved by the internally
constructed positive adapted atlas and partition. -/
theorem stokes_puncturedDomain_smooth [CompactSpace M]
    (σ : SmoothPartitionOfUnity (Fin a.card) (model (n+1)) M univ)
    (hσ : σ.IsSubordinate (fun k ↦ (a.chart k).source))
    (β : Form (model (n+1)) M (2*n+1)) (hβ : IsSmooth β) :
    integralTopFormOn a σ (puncturedDomain (deletedChartFamily a j) center r)
      (exteriorDerivative β) =
      -(∑ i, sphereFormIntegral (EuclideanSpace.basisFun (Fin (2*(n+1))) ℝ)
        (pullback (I := 𝓡 (2*n+1)) (I' := model (n+1))
          (sphereEmbedding (a.chart (j i)) (center i) (r i)) β)) := by
  classical
  let A := adaptedAtlas a j center r hr hcover hdis
  obtain ⟨ρ,hρ⟩ := adaptedAtlas_exists_partition a j center r hr hcover hdis
  rw [integralTopFormOn_independent a A.atlas
    (adaptedAtlas_compatible a j center r hr hcover hdis) σ ρ hσ hρ
    _ (isClosed_puncturedDomain _ _ _) _ hβ.exteriorDerivative]
  rw [stokes_finite_adapted_atlas _ (isClosed_puncturedDomain _ _ _) A ρ hρ β hβ]
  have hreindex :
      (∑ k, match A.position k with
        | .outside => 0
        | .interior => 0
        | .boundary => lowerFaceIntegral (A.atlas.chart k) (weightForm (ρ k) β)) =
      ∑ q : FamilyIndex a ι, match familyPosition a q with
        | .outside => 0
        | .interior => 0
        | .boundary => lowerFaceIntegral (familyChart a j center r hr hcover q)
            (weightForm (familyWeight a j center r hr hcover hdis ρ q) β) := by
    symm
    apply Fintype.sum_equiv (Fintype.equivFin (FamilyIndex a ι))
    intro q
    rw [adaptedAtlas_position_reindex a j center r hr hcover hdis,
      adaptedAtlas_chart_reindex a j center r hr hcover hdis]
    rfl
  calc
    _ = ∑ q : FamilyIndex a ι, match familyPosition a q with
        | .outside => 0
        | .interior => 0
        | .boundary => lowerFaceIntegral (familyChart a j center r hr hcover q)
            (weightForm (familyWeight a j center r hr hcover hdis ρ q) β) := hreindex
    _ = _ := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [familyPosition,Finset.sum_const_zero,zero_add]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact lowerFace_integrals_on_one_sphere a j center r hr hcover hdis ρ hρ β hβ i

/-- The full punctured-domain formula requires smoothness only on an open
neighborhood of the actual closed domain. A cutoff supported in that smooth
locus constructs the global representative inside the proof. In particular,
the form may be totalized arbitrarily at the removed vector-field zeros. -/
theorem stokes_puncturedDomain [CompactSpace M]
    (σ : SmoothPartitionOfUnity (Fin a.card) (model (n+1)) M univ)
    (hσ : σ.IsSubordinate (fun k ↦ (a.chart k).source))
    (U : Set M) (hU : IsOpen U)
    (hΩU : puncturedDomain (deletedChartFamily a j) center r ⊆ U)
    (α : Form (model (n+1)) M (2*n+1))
    (hα : ∀ x ∈ U, IsSmoothAtInCharts α x) :
    integralTopFormOn a σ (puncturedDomain (deletedChartFamily a j) center r)
      (exteriorDerivative α) =
      -(∑ i, sphereFormIntegral (EuclideanSpace.basisFun (Fin (2*(n+1))) ℝ)
        (pullback (I := 𝓡 (2*n+1)) (I' := model (n+1))
          (sphereEmbedding (a.chart (j i)) (center i) (r i)) α)) := by
  classical
  obtain ⟨β,hβ,hgerm,hderiv⟩ := exists_global_smooth_form_eq_near_closed_domain
    (puncturedDomain (deletedChartFamily a j) center r) U
    (isClosed_puncturedDomain _ _ _) hU hΩU α hα
  rw [← integralTopFormOn_congr a σ _ (isClosed_puncturedDomain _ _ _)
    (exteriorDerivative β) (exteriorDerivative α) hderiv,
    stokes_puncturedDomain_smooth a j center r hr hcover hdis σ hσ β hβ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext u
  ext v
  simp only [pullback_apply]
  rw [(hgerm _ (sphereEmbedding_mem_domain a j center r hr hcover hdis i u)).self_of_nhds]

end GaussBonnetChern.PuncturedStokes
