import GaussBonnetChern.ScalarDifferential
import GaussBonnetChern.ChernAngularAlgebra
import GaussBonnetChern.ChernFrameGeometry
import GaussBonnetChern.LocalFormPullback

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff Topology BigOperators
namespace GaussBonnetChern.DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℝ,E) ∞ P]

def functionSmul {k : ℕ} (f : P → ℝ) (α : Form 𝓘(ℝ,E) P k) : Form 𝓘(ℝ,E) P k :=
  fun x ↦ f x • α x

theorem IsSmooth.functionSmul {k : ℕ} {f : P → ℝ} {α : Form 𝓘(ℝ,E) P k}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ f) (hα : IsSmooth α) : IsSmooth (functionSmul f α) := by
  change IsSmooth (fun x ↦ f x • α x)
  rw [← wedge_ofFunction_right]
  exact hα.wedge (IsSmooth.ofFunction hf)

theorem exteriorDerivative_functionSmul_one {f : P → ℝ} {α : Form 𝓘(ℝ,E) P 1}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ f) (hα : IsSmooth α) :
    exteriorDerivative (functionSmul f α) = functionSmul f (exteriorDerivative α) -
      wedge α (scalarDifferential (E := E) f) := by
  have h := exteriorDerivative_wedge α (ofFunction f) hα (IsSmooth.ofFunction hf)
  rw [exteriorDerivative_ofFunction (hf.mdifferentiable (by simp))] at h
  have hneg {r : ℕ} (β : Form 𝓘(ℝ,E) P r) : (-1 : ℝ) • β = -β := by
    funext x
    ext v
    change (-1 : ℝ) * β x v = -(β x v)
    ring
  change exteriorDerivative (fun x ↦ f x • α x) =
    (fun x ↦ f x • exteriorDerivative α x) - wedge α (scalarDifferential (E := E) f)
  simpa [degreeCastForm, wedge_ofFunction_right, sub_eq_add_neg, hneg] using h

theorem wedge_functionSmul_right {k l : ℕ}
    (α : Form 𝓘(ℝ,E) P k) (f : P → ℝ) (β : Form 𝓘(ℝ,E) P l) :
    wedge α (functionSmul f β) = functionSmul f (wedge α β) := by
  funext x
  ext v
  simp [functionSmul, wedge, wedgeFiber_apply_realSign, mul_assoc, mul_left_comm,
    ← Finset.mul_sum]

theorem functionSmul_sub {k : ℕ} (f : P → ℝ) (α β : Form 𝓘(ℝ,E) P k) :
    functionSmul f (α-β) = functionSmul f α - functionSmul f β := by
  funext x
  exact smul_sub _ _ _

theorem functionSmul_sum {k : ℕ} {ι : Type*} (s : Finset ι) (f : P → ℝ)
    (α : ι → Form 𝓘(ℝ,E) P k) :
    functionSmul f (∑ i ∈ s, α i) = ∑ i ∈ s, functionSmul f (α i) := by
  funext x
  simp [functionSmul, Finset.smul_sum]

/-- Covariant direction defined from a function vector and connection
matrix, rather than assumed as an independent differential form. -/
def covariantDirection {ι : Type*} [Fintype ι]
    (u : ι → P → ℝ) (A : ι → ι → Form 𝓘(ℝ,E) P 1) (i : ι) : Form 𝓘(ℝ,E) P 1 :=
  scalarDifferential (E := E) (u i) + ∑ j, functionSmul (u j) (A i j)

/-- Genuine exterior differentiation of `du+A u`. The sole Cartan input
is a stated equation for actual forms, discharged by Levi-Civita geometry.
The resulting direction equation is proved by the actual d/wedge calculus. -/
theorem exteriorDerivative_covariantDirection {ι : Type*} [Fintype ι]
    (u : ι → P → ℝ) (A : ι → ι → Form 𝓘(ℝ,E) P 1)
    (B : ι → ι → Form 𝓘(ℝ,E) P 2)
    (hu : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ (u i))
    (hA : ∀ i j, IsSmooth (A i j))
    (hCartan : ∀ i j, B i j = exteriorDerivative (A i j) + ∑ a, wedge (A i a) (A a j))
    (i : ι) :
    exteriorDerivative (covariantDirection u A i) =
      (∑ j, functionSmul (u j) (B i j)) - ∑ j, wedge (A i j) (covariantDirection u A j) := by
  classical
  have hcoef (j : ι) : IsSmooth (functionSmul (u j) (A i j)) :=
    IsSmooth.functionSmul (hu j) (hA i j)
  have hdA (j : ι) : exteriorDerivative (A i j) = B i j - ∑ a, wedge (A i a) (A a j) := by
    rw [hCartan i j]
    abel
  have hw : (∑ j, wedge (A i j) (covariantDirection u A j)) =
      (∑ j, wedge (A i j) (scalarDifferential (E := E) (u j))) +
        ∑ a, ∑ j, functionSmul (u j) (wedge (A i a) (A a j)) := by
    simp only [covariantDirection]
    change (∑ j, Chern.wedgeLinear 1 1 (A i j)
      (scalarDifferential (E := E) (u j) + ∑ a, functionSmul (u a) (A j a))) = _
    simp only [map_add, map_sum, Chern.wedgeLinear_apply, Finset.sum_add_distrib,
      wedge_functionSmul_right]
  unfold covariantDirection
  rw [exteriorDerivative_add _ _ (IsSmooth.scalarDifferential (hu i))
    (IsSmooth.sum Finset.univ _ (fun j _ ↦ hcoef j)),
    exteriorDerivative_scalarDifferential (hu i), zero_add,
    exteriorDerivative_sum Finset.univ _ (fun j _ ↦ hcoef j)]
  simp only [exteriorDerivative_functionSmul_one (hu _) (hA _ _), hdA,
    functionSmul_sub, functionSmul_sum, Finset.sum_sub_distrib]
  change _ = (∑ j, functionSmul (u j) (B i j)) -
    ∑ j, wedge (A i j) (covariantDirection u A j)
  rw [hw]
  rw [Finset.sum_comm (f := fun j a ↦ functionSmul (u j) (wedge (A i a) (A a j)))]
  abel

end GaussBonnetChern.DifferentialForm

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

/-- The actual base projection of the nonzero tangent patch. -/
def framePatchProjection : frameNonzeroDomain n M s → M := fun v ↦ v.1.1

@[simp] theorem framePatchProjection_apply (v : frameNonzeroDomain n M s) :
    framePatchProjection n M s v = v.1.1 := rfl

theorem contMDiff_framePatchProjection :
    ContMDiff 𝓘(ℝ, Model n × Model n) (model n) ∞ (framePatchProjection n M s) := by
  have hπ : ContMDiff (model n).tangent (model n) ∞
      (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) :=
    contMDiff_proj (F := Model n) (IB := model n) (n := ∞)
      (TangentSpace (model n) : M → Type _)
  have hπ' : ContMDiff 𝓘(ℝ, Model n × Model n) (model n) ∞
      (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) := by
    simpa only [modelWithCornersSelf_prod] using hπ
  exact hπ'.comp contMDiff_subtype_val

/-- The original Levi-Civita connection pulled back to a genuine open patch. -/
def framePatchConnectionForm (i j : Fin (2*n)) :
    Form 𝓘(ℝ, Model n × Model n) (frameNonzeroDomain n M s) 1 :=
  pullback (framePatchProjection n M s) (smoothFrameConnectionOneForm n M b i j)

/-- The original curvature pulled back to the same genuine open patch. -/
def framePatchCurvatureForm (i j : Fin (2*n)) :
    Form 𝓘(ℝ, Model n × Model n) (frameNonzeroDomain n M s) 2 :=
  pullback (framePatchProjection n M s) (smoothFrameCurvatureTwoForm n M b i j)

/-- Covariant derivative of the actual normalized tautological coordinates. -/
def framePatchDirectionForm (i : Fin (2*n)) :
    Form 𝓘(ℝ, Model n × Model n) (frameNonzeroDomain n M s) 1 :=
  covariantDirection (framePatchDirectionCoordinate n M b s)
    (framePatchConnectionForm n M b s) i

variable (hb : ∀ i, ContMDiffOn (model n) (model n).tangent ∞
  (T% (fun x ↦ b x i)) s)

include hb in
theorem isSmooth_framePatchConnectionForm (i j : Fin (2*n)) :
    IsSmooth (framePatchConnectionForm n M b s i j) := by
  apply isSmooth_pullback_of_chartSmoothAt _ (contMDiff_framePatchProjection n M s)
  intro v
  change ContDiffAt ℝ ∞
    (chartRepresentation (chartAt (Model n) v.1.1) (smoothFrameConnectionOneForm n M b i j))
    ((chartAt (Model n) v.1.1) v.1.1)
  exact contDiffAt_chartRepresentation_smoothFrameConnection n M b i j
    (chartAt (Model n) v.1.1) (IsManifold.chart_mem_maximalAtlas v.1.1)
    ((chartAt (Model n) v.1.1).map_source (mem_chart_source (Model n) v.1.1))
    (by
      simpa only [(chartAt (Model n) v.1.1).left_inv (mem_chart_source (Model n) v.1.1)] using
        fun i ↦ (hb i).contMDiffAt (s.isOpen.mem_nhds v.2.1))

include hb in
theorem isSmooth_framePatchCurvatureForm (i j : Fin (2*n)) :
    IsSmooth (framePatchCurvatureForm n M b s i j) := by
  apply isSmooth_pullback_of_chartSmoothAt _ (contMDiff_framePatchProjection n M s)
  intro v
  change ContDiffAt ℝ ∞
    (chartRepresentation (chartAt (Model n) v.1.1) (smoothFrameCurvatureTwoForm n M b i j))
    ((chartAt (Model n) v.1.1) v.1.1)
  exact contDiffAt_smoothFrameCoordinateCurvature n M b s.isOpen hb
    (chartAt (Model n) v.1.1) (IsManifold.chart_mem_maximalAtlas v.1.1) i j
    ((chartAt (Model n) v.1.1).map_source (mem_chart_source (Model n) v.1.1))
    (by
      rw [(chartAt (Model n) v.1.1).left_inv (mem_chart_source (Model n) v.1.1)]
      exact v.2.1)

include hb in
theorem isSmooth_framePatchDirectionForm (i : Fin (2*n)) :
    IsSmooth (framePatchDirectionForm n M b s i) := by
  apply IsSmooth.add
  · exact IsSmooth.scalarDifferential (by
      simpa only [modelWithCornersSelf_prod] using
        contMDiff_framePatchDirectionCoordinate n M b s hb i)
  · apply IsSmooth.sum Finset.univ
    intro j _
    exact IsSmooth.functionSmul
      (by simpa only [modelWithCornersSelf_prod] using
        contMDiff_framePatchDirectionCoordinate n M b s hb j)
      (isSmooth_framePatchConnectionForm n M b s hb i j)

include hb in
/-- Cartan's equation on an actual patch is obtained by local naturality,
not by assuming a globally smooth extension of the chosen frame. -/
theorem framePatchCartan (i j : Fin (2*n)) :
    framePatchCurvatureForm n M b s i j =
      exteriorDerivative (framePatchConnectionForm n M b s i j) +
        ∑ a, wedge (framePatchConnectionForm n M b s i a)
          (framePatchConnectionForm n M b s a j) := by
  funext v
  have hbase : ∀ a, ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun x ↦ b x a)) v.1.1 :=
    fun a ↦ (hb a).contMDiffAt (s.isOpen.mem_nhds v.2.1)
  have hs := contDiffAt_chartRepresentation_smoothFrameConnection n M b i j
    (chartAt (Model n) v.1.1) (IsManifold.chart_mem_maximalAtlas v.1.1)
    ((chartAt (Model n) v.1.1).map_source (mem_chart_source (Model n) v.1.1))
    (by simpa only [(chartAt (Model n) v.1.1).left_inv (mem_chart_source (Model n) v.1.1)] using hbase)
  have hd := pullback_exteriorDerivative_at (framePatchProjection n M s)
    (contMDiff_framePatchProjection n M s) (smoothFrameConnectionOneForm n M b i j) v hs
  change pullback (framePatchProjection n M s) (smoothFrameCurvatureTwoForm n M b i j) v =
    exteriorDerivative (pullback (framePatchProjection n M s)
      (smoothFrameConnectionOneForm n M b i j)) v + _
  rw [← hd]
  ext w
  have hc := congrArg (fun α ↦ α (fun k ↦ mfderiv 𝓘(ℝ, Model n × Model n) (model n)
    (framePatchProjection n M s) v (w k))) (smoothFrameCartan n M b i j hbase)
  simp only [pullback_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sum_apply, Finset.sum_apply, Pi.add_apply,
    framePatchProjection_apply] at hc ⊢
  rw [hc]
  congr 1

include hb in
/-- Bianchi's equation on the genuine open tangent patch, with all
regularity supplied by the chosen frame on its actual base domain. -/
theorem framePatchBianchi (i j : Fin (2*n)) :
    exteriorDerivative (framePatchCurvatureForm n M b s i j) =
      ∑ a, (wedge (framePatchCurvatureForm n M b s i a)
        (framePatchConnectionForm n M b s a j) -
        wedge (framePatchConnectionForm n M b s i a)
          (framePatchCurvatureForm n M b s a j)) := by
  funext v
  have hs := contDiffAt_smoothFrameCoordinateCurvature n M b s.isOpen hb
    (chartAt (Model n) v.1.1) (IsManifold.chart_mem_maximalAtlas v.1.1) i j
    ((chartAt (Model n) v.1.1).map_source (mem_chart_source (Model n) v.1.1))
    (by
      rw [(chartAt (Model n) v.1.1).left_inv (mem_chart_source (Model n) v.1.1)]
      exact v.2.1)
  have hd := pullback_exteriorDerivative_at (framePatchProjection n M s)
    (contMDiff_framePatchProjection n M s) (smoothFrameCurvatureTwoForm n M b i j) v hs
  change exteriorDerivative (pullback (framePatchProjection n M s)
    (smoothFrameCurvatureTwoForm n M b i j)) v = _
  rw [← hd]
  ext w
  have hc := congrArg (fun α ↦ α (fun k ↦ mfderiv 𝓘(ℝ, Model n × Model n) (model n)
    (framePatchProjection n M s) v (w k)))
    (smoothFrame_bianchi n M b s.isOpen hb i j v.2.1)
  simp only [pullback_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.sum_apply, Finset.sum_apply, Pi.sub_apply,
    framePatchProjection_apply] at hc ⊢
  rw [hc]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg₂ (· - ·)
    (congrArg (fun α ↦ α v w)
      (pullback_wedge (framePatchProjection n M s)
        (smoothFrameCurvatureTwoForm n M b i a) (smoothFrameConnectionOneForm n M b a j)))
    (congrArg (fun α ↦ α v w)
      (pullback_wedge (framePatchProjection n M s)
        (smoothFrameConnectionOneForm n M b i a) (smoothFrameCurvatureTwoForm n M b a j)))

include hb in
theorem exteriorDerivative_framePatchDirectionForm (i : Fin (2*n)) :
    exteriorDerivative (framePatchDirectionForm n M b s i) =
      (∑ j, functionSmul (framePatchDirectionCoordinate n M b s j)
        (framePatchCurvatureForm n M b s i j)) -
      ∑ j, wedge (framePatchConnectionForm n M b s i j) (framePatchDirectionForm n M b s j) :=
  exteriorDerivative_covariantDirection _ _ _
    (fun j ↦ by simpa only [modelWithCornersSelf_prod] using
      contMDiff_framePatchDirectionCoordinate n M b s hb j)
    (isSmooth_framePatchConnectionForm n M b s hb)
    (framePatchCartan n M b s hb) i

theorem framePatchDirectionCoordinate_unit (v : frameNonzeroDomain n M s) :
    ∑ i, framePatchDirectionCoordinate n M b s i v ^ 2 = 1 :=
  sum_sq_frameDirectionCoordinate n M b v.1 v.2.2

include hb in
theorem framePatchConnectionForm_skew (i j : Fin (2*n)) :
    framePatchConnectionForm n M b s i j = -framePatchConnectionForm n M b s j i := by
  funext v
  ext w
  have h := congrArg (fun α ↦ α (fun k ↦ mfderiv 𝓘(ℝ, Model n × Model n) (model n)
    (framePatchProjection n M s) v (w k)))
    (smoothFrameConnectionOneForm_skew n M b i j
      (fun a ↦ (hb a).contMDiffAt (s.isOpen.mem_nhds v.2.1)))
  simpa only [framePatchConnectionForm, pullback_apply,
    Pi.neg_apply, ContinuousAlternatingMap.neg_apply, framePatchProjection_apply] using h

theorem framePatchCurvatureForm_skew (i j : Fin (2*n)) :
    framePatchCurvatureForm n M b s i j = -framePatchCurvatureForm n M b s j i := by
  funext v
  ext w
  have h := congrArg (fun α ↦ α (fun k ↦ mfderiv 𝓘(ℝ, Model n × Model n) (model n)
    (framePatchProjection n M s) v (w k)))
    (smoothFrameCurvatureTwoForm_skew n M b i j v.1.1)
  simpa only [framePatchCurvatureForm, pullback_apply,
    Pi.neg_apply, ContinuousAlternatingMap.neg_apply, framePatchProjection_apply] using h

include hb in
/-- The open-patch direction form is the genuine restriction of the
ambient frame direction, by the actual chain rule. -/
theorem framePatchDirectionForm_eq_restrict (i : Fin (2*n)) :
    framePatchDirectionForm n M b s i =
      pullback (I := 𝓘(ℝ, Model n × Model n))
        ((↑) : frameNonzeroDomain n M s → TangentBundle (model n) M)
        (frameTangentDirectionForm n M b i) := by
  let inc : frameNonzeroDomain n M s → TangentBundle (model n) M := (↑)
  have hinc : ContMDiff 𝓘(ℝ, Model n × Model n) (model n).tangent ∞ inc := by
    simpa only [modelWithCornersSelf_prod] using
      (contMDiff_subtype_val (I := 𝓘(ℝ, Model n × Model n)) (U := frameNonzeroDomain n M s))
  have hπ : MDifferentiable (model n).tangent (model n)
      (Bundle.TotalSpace.proj : TangentBundle (model n) M → M) :=
    (contMDiff_proj (F := Model n) (IB := model n) (n := ∞)
      (TangentSpace (model n) : M → Type _)).mdifferentiable (by simp)
  have hconn (j : Fin (2*n)) :
      framePatchConnectionForm n M b s i j =
        pullback (I := 𝓘(ℝ, Model n × Model n)) inc (frameTangentConnectionForm n M b i j) :=
    pullback_comp inc (Bundle.TotalSpace.proj : TangentBundle (model n) M → M)
      (smoothFrameConnectionOneForm n M b i j) (hinc.mdifferentiable (by simp)) hπ
  funext v
  have hbase : ∀ a, ContMDiffAt (model n) (model n).tangent ∞
      (T% (fun x ↦ b x a)) v.1.1 := fun a ↦ (hb a).contMDiffAt (s.isOpen.mem_nhds v.2.1)
  have hu := (contMDiffAt_frameDirectionCoordinate n M b i v.1 hbase v.2.2).mdifferentiableAt (by simp)
  ext w
  have hdu : mvfderiv 𝓘(ℝ, Model n × Model n)
      (framePatchDirectionCoordinate n M b s i) v (w 0) =
      mvfderiv (model n).tangent (frameDirectionCoordinate n M b i) v.1
        (mfderiv 𝓘(ℝ, Model n × Model n) (model n).tangent inc v (w 0)) := by
    change mvfderiv 𝓘(ℝ, Model n × Model n) ((frameDirectionCoordinate n M b i) ∘ inc) v (w 0) = _
    unfold mvfderiv
    rw [mfderiv_comp v hu ((hinc v).mdifferentiableAt (by simp))]
    rfl
  simp only [framePatchDirectionForm, covariantDirection, functionSmul,
    Pi.add_apply, Finset.sum_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    scalarDifferential_apply, pullback_apply, frameTangentDirectionForm_apply,
    smul_eq_mul, hdu, hconn]
  rfl

include hb in
theorem framePatchDirectionForm_orthogonal (v : frameNonzeroDomain n M s) :
    (∑ i, framePatchDirectionCoordinate n M b s i v • framePatchDirectionForm n M b s i v) = 0 := by
  ext w
  have h := congrArg (fun α ↦ α (fun k ↦ mfderiv 𝓘(ℝ, Model n × Model n) (model n).tangent
    ((↑) : frameNonzeroDomain n M s → TangentBundle (model n) M) v (w k)))
    (frameTangentDirectionForm_orthogonal n M b v.1
      (fun a ↦ (hb a).contMDiffAt (s.isOpen.mem_nhds v.2.1)) v.2.2)
  simp only [framePatchDirectionForm_eq_restrict n M b s hb, pullback_apply,
    framePatchDirectionCoordinate, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, zero_apply] at h ⊢
  exact h

theorem scalarDifferential_framePatchDirectionCoordinate (i : Fin (2*n)) :
    scalarDifferential (framePatchDirectionCoordinate n M b s i) =
      framePatchDirectionForm n M b s i -
        ∑ j, functionSmul (framePatchDirectionCoordinate n M b s j)
          (framePatchConnectionForm n M b s i j) := by
  unfold framePatchDirectionForm covariantDirection
  abel

end GaussBonnetChern
