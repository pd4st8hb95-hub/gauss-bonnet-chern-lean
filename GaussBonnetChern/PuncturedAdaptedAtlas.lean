import GaussBonnetChern.FiniteChartStokes
import GaussBonnetChern.PuncturedBoundaryCharts
import GaussBonnetChern.PuncturedBoundaryRegularity
import GaussBonnetChern.SphereOrientedAtlas

/-! # Actual finite adapted atlases for disjoint coordinate balls

The three finite chart families are restrictions of the original positive
atlas outside and inside the closed punctured domain, and height-first radial
charts near the deleted spheres. The radial charts use the actual positive
outward sphere atlas. No local Stokes formula is part of the construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Module
open scoped Manifold ContDiff Topology

namespace GaussBonnetChern.PuncturedAdaptedAtlas
open PuncturedManifold RadialBoundaryCharts FiniteChartStokes

section PositiveCharts
variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Model m) M] [IsManifold (model m) ∞ M]

/-- Restriction preserves genuine smooth chart membership. -/
theorem restrOpen_mem_maximalAtlas
    (e : OpenPartialHomeomorph M (Model m))
    (he : e ∈ IsManifold.maximalAtlas (model m) ∞ M)
    (U : Set M) (hU : IsOpen U) :
    e.restrOpen U hU ∈ IsManifold.maximalAtlas (model m) ∞ M := by
  apply (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).mpr
  exact ⟨(contMDiffOn_of_mem_maximalAtlas he).mono inter_subset_left,
    (contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left⟩

/-- The actual coordinate basis, independent of a choice of Riemannian metric. -/
def chartBasis (e : OpenPartialHomeomorph M (Model m))
    (he : e ∈ IsManifold.maximalAtlas (model m) ∞ M) (x : M) (hx : x ∈ e.source) :
    Basis (Fin (2*m)) ℝ (TangentSpace (model m) x) :=
  let hd : e.MDifferentiable (model m) (model m) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  (EuclideanSpace.basisFun (Fin (2*m)) ℝ).toBasis.map (hd.mfderiv hx).symm.toLinearEquiv

theorem chartBasis_det_transition
    (e f : OpenPartialHomeomorph M (Model m))
    (he : e ∈ IsManifold.maximalAtlas (model m) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas (model m) ∞ M)
    (x : M) (hx : x ∈ e.source) (hxf : x ∈ f.source) :
    (chartBasis f hf x hxf).det (chartBasis e he x hx) =
      LinearMap.det (fderiv ℝ (f ∘ e.symm) (e x)).toLinearMap := by
  dsimp only [chartBasis]
  simp only [Basis.det_map]
  let b := (EuclideanSpace.basisFun (Fin (2*m)) ℝ).toBasis
  let T := (fderiv ℝ (f ∘ e.symm) (e x)).toLinearMap
  have hv : (fun i ↦ mfderiv (model m) (model m) f x
      (mfderiv (model m) (model m) e.symm (e x) (b i))) = T ∘ b := by
    funext i
    have h := congrArg (fun L ↦ L (b i))
      (DifferentialForm.transition_fderiv e f he hf (e x) (e.map_source hx)
        (by simpa only [e.left_inv hx] using hxf))
    change fderiv ℝ (f ∘ e.symm) (e x) (b i) =
      mfderiv (model m) (model m) f (e.symm (e x))
        (mfderiv (model m) (model m) e.symm (e x) (b i)) at h
    rw [e.left_inv hx] at h
    exact h.symm
  change b.det (fun i ↦ mfderiv (model m) (model m) f x
      (mfderiv (model m) (model m) e.symm (e x) (b i))) = LinearMap.det T
  rw [hv, Basis.det_comp, Basis.det_self, mul_one]

/-- Two charts positive relative to the same original chart are mutually positive. -/
theorem positive_transition_of_common_chart
    (e f g : OpenPartialHomeomorph M (Model m))
    (he : e ∈ IsManifold.maximalAtlas (model m) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas (model m) ∞ M)
    (hg : g ∈ IsManifold.maximalAtlas (model m) ∞ M)
    (x : M) (hxe : x ∈ e.source) (hxf : x ∈ f.source) (hxg : x ∈ g.source)
    (hge : 0 < LinearMap.det (fderiv ℝ (e ∘ g.symm) (g x)).toLinearMap)
    (hgf : 0 < LinearMap.det (fderiv ℝ (f ∘ g.symm) (g x)).toLinearMap) :
    0 < LinearMap.det (fderiv ℝ (f ∘ e.symm) (e x)).toLinearMap := by
  rw [← chartBasis_det_transition e f he hf x hxe hxf]
  apply (Basis.orientation_eq_iff_det_pos _ _).mp
  have h1 : (chartBasis e he x hxe).orientation = (chartBasis g hg x hxg).orientation := by
    apply (Basis.orientation_eq_iff_det_pos _ _).mpr
    rwa [chartBasis_det_transition g e hg he x hxg hxe]
  have h2 : (chartBasis f hf x hxf).orientation = (chartBasis g hg x hxg).orientation := by
    apply (Basis.orientation_eq_iff_det_pos _ _).mpr
    rwa [chartBasis_det_transition g f hg hf x hxg hxf]
  exact h2.trans h1.symm

end PositiveCharts

/-- The chart's arbitrary totalization witness does not constrain its actual source. -/
theorem radialEuclideanChart_mem_source_of_direction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (r : ℝ) (hr : 0 < r) (u₀ v : sphere (0:E) 1)
    (c : OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin d)))
    (hv : v ∈ c.source) : r • (v:E) ∈ (radialEuclideanChart r hr u₀ c).source := by
  rw [radialEuclideanChart_source]
  have hy : (c v, (0:ℝ)) ∈ (radialProductChart r hr u₀ c).target := by
    rw [radialProductChart_target]
    exact ⟨c.map_source hv, by simpa using hr⟩
  have hs := (radialProductChart r hr u₀ c).map_target hy
  rw [radialProductChart_symm r hr u₀ c (c v) 0 (by simpa using hr), c.left_inv hv] at hs
  simpa [radialCollar] using hs

section Construction
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Model (n+1)) M] [IsManifold (model (n+1)) ∞ M]
  [T2Space M] {ι : Type*} [Fintype ι]

local instance sphereDimension :
    Fact (finrank ℝ (Model (n+1)) = (2*n+1)+1) := ⟨by simp [Model, Nat.mul_add, Nat.add_assoc]⟩

/-- A fixed unit vector is used only to totalize inverse maps outside chart domains. -/
def sphereWitness (n : ℕ) : sphere (0 : Model (n+1)) 1 :=
  ⟨EuclideanSpace.basisFun (Fin (2*(n+1))) ℝ 0, by
    simpa using (EuclideanSpace.basisFun (Fin (2*(n+1))) ℝ).norm_eq_one 0⟩

def boundarySphereAtlas (n : ℕ) :
    FiniteSphereOrientedAtlas (d := 2*n+1)
      (EuclideanSpace.basisFun (Fin (2*(n+1))) ℝ) :=
  sphereOrientedAtlas (EuclideanSpace.basisFun (Fin (2*(n+1))) ℝ) (by omega)

abbrev deletedChartFamily (a : FiniteOrientedAtlas (n+1) M) (j : ι → Fin a.card) :=
  fun i ↦ a.chart (j i)

abbrev FamilyIndex (a : FiniteOrientedAtlas (n+1) M) (ι : Type*) :=
  Fin a.card ⊕ (Fin a.card ⊕ (ι × Fin (boundarySphereAtlas n).card))

/-- The full finite family, before reindexing by a single finite ordinal. -/
def familyChart (a : FiniteOrientedAtlas (n+1) M) (j : ι → Fin a.card)
    (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (j i)).target) :
    FamilyIndex a ι → OpenPartialHomeomorph M (Model (n+1))
  | .inl k => (a.chart k).restrOpen (puncturedDomain (deletedChartFamily a j) center r)ᶜ
      (isClosed_puncturedDomain _ _ _).isOpen_compl
  | .inr (.inl k) => (a.chart k).restrOpen
      (interior (puncturedDomain (deletedChartFamily a j) center r)) isOpen_interior
  | .inr (.inr p) => puncturedBoundaryChart (deletedChartFamily a j) center r hr hcover
      p.1 (sphereWitness n) ((boundarySphereAtlas n).chart p.2)

def familyPosition (a : FiniteOrientedAtlas (n+1) M) : FamilyIndex a ι → ChartPosition
  | .inl _ => .outside
  | .inr (.inl _) => .interior
  | .inr (.inr _) => .boundary

theorem familyChart_smooth (a : FiniteOrientedAtlas (n+1) M) (j : ι → Fin a.card)
    (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (j i)).target)
    (q : FamilyIndex a ι) :
    familyChart a j center r hr hcover q ∈ IsManifold.maximalAtlas (model (n+1)) ∞ M := by
  rcases q with k | (k | ⟨i,l⟩)
  · exact restrOpen_mem_maximalAtlas (a.chart k) (a.smooth k)
      (puncturedDomain (deletedChartFamily a j) center r)ᶜ
      (isClosed_puncturedDomain (deletedChartFamily a j) center r).isOpen_compl
  · exact restrOpen_mem_maximalAtlas (a.chart k) (a.smooth k)
      (interior (puncturedDomain (deletedChartFamily a j) center r)) isOpen_interior
  · exact puncturedBoundaryChart_mem_maximalAtlas (deletedChartFamily a j)
      (fun i ↦ a.smooth (j i)) center r hr hcover i (sphereWitness n) _ ((boundarySphereAtlas n).smooth l)

theorem familyChart_domain (a : FiniteOrientedAtlas (n+1) M) (j : ι → Fin a.card)
    (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (j i)).target)
    (q : FamilyIndex a ι) (x : M) (hx : x ∈ (familyChart a j center r hr hcover q).source) :
    match familyPosition a q with
    | .outside => x ∉ puncturedDomain (deletedChartFamily a j) center r
    | .interior => x ∈ puncturedDomain (deletedChartFamily a j) center r
    | .boundary => x ∈ puncturedDomain (deletedChartFamily a j) center r ↔
        0 ≤ familyChart a j center r hr hcover q x 0 := by
  rcases q with k | (k | ⟨i,l⟩)
  · exact hx.2
  · exact interior_subset hx.2
  · exact puncturedBoundaryChart_domain (deletedChartFamily a j) center r hr hcover
      i (sphereWitness n) _ x hx

theorem familyChart_covers (a : FiniteOrientedAtlas (n+1) M) (j : ι → Fin a.card)
    (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (j i)).target)
    (hdis : Pairwise (fun i k ↦ Disjoint
      (coordinateClosedBall (a.chart (j i)) (center i) (r i))
      (coordinateClosedBall (a.chart (j k)) (center k) (r k))))
    (x : M) : ∃ q : FamilyIndex a ι, x ∈ (familyChart a j center r hr hcover q).source := by
  classical
  let e := deletedChartFamily a j
  let Ω := puncturedDomain e center r
  obtain ⟨k,hk⟩ := a.covers x
  by_cases hx : x ∈ Ω
  · by_cases hxi : x ∈ interior Ω
    · exact ⟨.inr (.inl k), hk, hxi⟩
    · have hxf : x ∈ frontier Ω := (mem_frontier_iff_notMem_interior hx).mpr hxi
      rw [frontier_puncturedDomain e center r (fun i ↦ (hr i).ne') hcover hdis] at hxf
      obtain ⟨i,hi⟩ := mem_iUnion.mp hxf
      let v := e i x - center i
      have hvnorm : ‖v‖ = r i := by simpa [v, dist_eq_norm] using hi.2
      have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvnorm]; exact (hr i).ne')
      let u : sphere (0 : Model (n+1)) 1 :=
        ⟨radialDirection v, by simpa using norm_radialDirection v hv0⟩
      obtain ⟨l,hl⟩ := (boundarySphereAtlas n).covers u
      have hrad := radialEuclideanChart_mem_source_of_direction
        (r i) (hr i) (sphereWitness n) u ((boundarySphereAtlas n).chart l) hl
      have hru : r i • (u : Model (n+1)) = v := by
        change r i • radialDirection v = v
        rw [← hvnorm]
        exact radial_reconstruct v hv0
      rw [hru] at hrad
      refine ⟨.inr (.inr (i,l)), ?_⟩
      change x ∈ (puncturedBoundaryChart e center r hr hcover i (sphereWitness n)
        ((boundarySphereAtlas n).chart l)).source
      constructor
      · exact ⟨hi.1, mem_univ _, hrad⟩
      · exact coordinateClosedBall_subset_otherBallExterior e center r hdis i
          ⟨hi.1, le_of_eq hi.2⟩
  · exact ⟨.inl k, hk, hx⟩

theorem familyChart_positive_from_base (a : FiniteOrientedAtlas (n+1) M)
    (j : ι → Fin a.card) (center : ι → Model (n+1)) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (j i)).target)
    (k : Fin a.card) (q : FamilyIndex a ι) (x : M)
    (hk : x ∈ (a.chart k).source) (hq : x ∈ (familyChart a j center r hr hcover q).source) :
    0 < LinearMap.det (fderiv ℝ
      (familyChart a j center r hr hcover q ∘ (a.chart k).symm) ((a.chart k) x)).toLinearMap := by
  rcases q with l | (l | ⟨i,l⟩)
  · exact a.positive_transition k l x hk hq.1
  · exact a.positive_transition k l x hk hq.1
  · exact puncturedBoundaryChart_positive_cross a j center r hr hcover i (sphereWitness n)
      ((boundarySphereAtlas n).chart l) ((boundarySphereAtlas n).smooth l)
      ((boundarySphereAtlas n).positive_density l) k x hk hq

/-- A concrete finite adapted atlas built from the three chart families. -/
def adaptedAtlas (a : FiniteOrientedAtlas (n+1) M) (j : ι → Fin a.card)
    (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (j i)).target)
    (hdis : Pairwise (fun i k ↦ Disjoint
      (coordinateClosedBall (a.chart (j i)) (center i) (r i))
      (coordinateClosedBall (a.chart (j k)) (center k) (r k)))) :
    AdaptedAtlas (n := n) (puncturedDomain (deletedChartFamily a j) center r) := by
  classical
  let reindex := (Fintype.equivFin (FamilyIndex a ι)).symm
  let f := familyChart a j center r hr hcover
  let af : FiniteOrientedAtlas (n+1) M :=
    { card := Fintype.card (FamilyIndex a ι)
      chart := fun q ↦ f (reindex q)
      smooth := fun q ↦ familyChart_smooth a j center r hr hcover (reindex q)
      covers := by
        intro x
        obtain ⟨q,hq⟩ := familyChart_covers a j center r hr hcover hdis x
        refine ⟨Fintype.equivFin (FamilyIndex a ι) q, ?_⟩
        simpa only [reindex, Equiv.symm_apply_apply] using hq
      positive_transition := by
        intro q q' x hx hx'
        obtain ⟨k,hk⟩ := a.covers x
        exact positive_transition_of_common_chart (f (reindex q)) (f (reindex q')) (a.chart k)
          (familyChart_smooth a j center r hr hcover _) (familyChart_smooth a j center r hr hcover _)
          (a.smooth k) x hx hx' hk
          (familyChart_positive_from_base a j center r hr hcover k _ x hk hx)
          (familyChart_positive_from_base a j center r hr hcover k _ x hk hx') }
  exact { atlas := af
          position := fun q ↦ familyPosition a (reindex q)
          domain := fun q x hx ↦ familyChart_domain a j center r hr hcover (reindex q) x hx }

/-- The finite-ordinal indexing retains the explicit three-family charts. -/
theorem adaptedAtlas_chart_reindex (a : FiniteOrientedAtlas (n+1) M) (j : ι → Fin a.card)
    (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (j i)).target)
    (hdis : Pairwise (fun i k ↦ Disjoint
      (coordinateClosedBall (a.chart (j i)) (center i) (r i))
      (coordinateClosedBall (a.chart (j k)) (center k) (r k))))
    (q : FamilyIndex a ι) :
    (adaptedAtlas a j center r hr hcover hdis).atlas.chart
      (Fintype.equivFin (FamilyIndex a ι) q) = familyChart a j center r hr hcover q := by
  classical
  change familyChart a j center r hr hcover
    ((Fintype.equivFin (FamilyIndex a ι)).symm (Fintype.equivFin (FamilyIndex a ι) q)) = _
  rw [Equiv.symm_apply_apply]

theorem adaptedAtlas_position_reindex (a : FiniteOrientedAtlas (n+1) M) (j : ι → Fin a.card)
    (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (j i)).target)
    (hdis : Pairwise (fun i k ↦ Disjoint
      (coordinateClosedBall (a.chart (j i)) (center i) (r i))
      (coordinateClosedBall (a.chart (j k)) (center k) (r k))))
    (q : FamilyIndex a ι) :
    (adaptedAtlas a j center r hr hcover hdis).position
      (Fintype.equivFin (FamilyIndex a ι) q) = familyPosition a q := by
  classical
  change familyPosition a
    ((Fintype.equivFin (FamilyIndex a ι)).symm (Fintype.equivFin (FamilyIndex a ι) q)) = _
  rw [Equiv.symm_apply_apply]

/-- The adapted atlas preserves the originally chosen ambient orientation. -/
theorem adaptedAtlas_compatible (a : FiniteOrientedAtlas (n+1) M) (j : ι → Fin a.card)
    (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (j i)).target)
    (hdis : Pairwise (fun i k ↦ Disjoint
      (coordinateClosedBall (a.chart (j i)) (center i) (r i))
      (coordinateClosedBall (a.chart (j k)) (center k) (r k)))) :
    a.Compatible (adaptedAtlas a j center r hr hcover hdis).atlas := by
  classical
  intro k q x hk hq
  exact familyChart_positive_from_base a j center r hr hcover k
    ((Fintype.equivFin (FamilyIndex a ι)).symm q) x hk hq
theorem adaptedAtlas_exists_partition [CompactSpace M]
    (a : FiniteOrientedAtlas (n+1) M) (j : ι → Fin a.card)
    (center : ι → Model (n+1)) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hcover : ∀ i, closedBall (center i) (r i) ⊆ (a.chart (j i)).target)
    (hdis : Pairwise (fun i k ↦ Disjoint
      (coordinateClosedBall (a.chart (j i)) (center i) (r i))
      (coordinateClosedBall (a.chart (j k)) (center k) (r k)))) :
    ∃ ρ : SmoothPartitionOfUnity (Fin (adaptedAtlas a j center r hr hcover hdis).atlas.card)
      (model (n+1)) M univ,
      ρ.IsSubordinate (fun k ↦ ((adaptedAtlas a j center r hr hcover hdis).atlas.chart k).source) := by
  let A := (adaptedAtlas a j center r hr hcover hdis).atlas
  apply SmoothPartitionOfUnity.exists_isSubordinate (model (n+1)) isClosed_univ
    (fun k ↦ (A.chart k).source) (fun k ↦ (A.chart k).open_source)
  intro x _
  obtain ⟨k,hk⟩ := A.covers x
  exact mem_iUnion.mpr ⟨k,hk⟩

/-- Every finite set of distinct points admits actual disjoint deleted balls,
with a genuine adapted positive atlas and a subordinate smooth partition. -/
theorem exists_punctured_adaptedAtlas_partition [CompactSpace M]
    (a : FiniteOrientedAtlas (n+1) M) (p : ι → M) (hp : Function.Injective p) :
    ∃ (j : ι → Fin a.card) (r : ι → ℝ),
      (∀ i, p i ∈ (a.chart (j i)).source) ∧ (∀ i, 0 < r i) ∧
      (∀ i, closedBall (a.chart (j i) (p i)) (r i) ⊆ (a.chart (j i)).target) ∧
      Pairwise (fun i k ↦ Disjoint
        (coordinateClosedBall (a.chart (j i)) (a.chart (j i) (p i)) (r i))
        (coordinateClosedBall (a.chart (j k)) (a.chart (j k) (p k)) (r k))) ∧
      ∃ A : AdaptedAtlas (n := n)
          (puncturedDomain (deletedChartFamily a j) (fun i ↦ a.chart (j i) (p i)) r),
        a.Compatible A.atlas ∧ ∃ ρ : SmoothPartitionOfUnity (Fin A.atlas.card) (model (n+1)) M univ,
          ρ.IsSubordinate (fun k ↦ (A.atlas.chart k).source) := by
  classical
  choose j hj using fun i ↦ a.covers (p i)
  obtain ⟨r,hr,hcover,hdis⟩ := exists_disjoint_coordinateBalls p hp (deletedChartFamily a j) hj
  refine ⟨j,r,hj,hr,hcover,hdis,adaptedAtlas a j _ r hr hcover hdis,
    adaptedAtlas_compatible a j _ r hr hcover hdis, ?_⟩
  exact adaptedAtlas_exists_partition a j _ r hr hcover hdis

end Construction
end GaussBonnetChern.PuncturedAdaptedAtlas
