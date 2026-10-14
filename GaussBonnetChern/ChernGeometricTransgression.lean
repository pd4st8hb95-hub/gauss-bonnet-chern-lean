import GaussBonnetChern.ChernActualPatchRecurrence
import GaussBonnetChern.ChernSmoothTelescope
import GaussBonnetChern.ChernEulerEndpoint
import GaussBonnetChern.ChernOpenRestriction
import GaussBonnetChern.ChernTransgressionAssembly

/-! Actual patch geometry discharges the original recurrence, so the final
Euler transgression has no local-equation premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle Filter
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern
open DifferentialForm
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] [Fact (0<n)]
variable (b : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x))
  (s : TopologicalSpace.Opens M)
  (hb : ∀ i, ContMDiffOn (model n) (model n).tangent ∞ (T% (fun x ↦ b x i)) s)

include hb in
theorem exteriorDerivative_framePatchAngularForm :
    degreeCastForm (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
      (exteriorDerivative (framePatchAngularForm n M b s)) =
      -(Chern.angularCoefficient n n •
        Chern.recurrencePolynomial n (Fin.last n) (framePatchDirectionForm n M b s)
          (framePatchCurvatureForm n M b s)) := by
  unfold framePatchAngularForm
  refine Chern.exteriorDerivative_angularForm_of_recurrence
    (E := Model n × Model n) (P := frameNonzeroDomain n M s) n Fact.out
    (framePatchDirectionCoordinate n M b s) (framePatchDirectionForm n M b s)
    (framePatchCurvatureForm n M b s) ?_ ?_ ?_
    (fun k ↦ Chern.recurrencePolynomial n k (framePatchDirectionForm n M b s)
      (framePatchCurvatureForm n M b s)) ?_ ?_
  · intro i
    simpa only [modelWithCornersSelf_prod] using
      contMDiff_framePatchDirectionCoordinate n M b s hb i
  · exact isSmooth_framePatchDirectionForm n M b s hb
  · exact isSmooth_framePatchCurvatureForm n M b s hb
  · funext v
    exact Chern.recurrencePolynomial_zero_of_unit n
      (fun i ↦ framePatchDirectionCoordinate n M b s i v)
      (framePatchDirectionForm n M b s) (framePatchCurvatureForm n M b s) v
      (framePatchDirectionCoordinate_unit n M b s v)
      (framePatchDirectionForm_orthogonal n M b s hb v)
  · exact exteriorDerivative_framePatch_angularTerm_recurrence n M b s hb

include hb in
/-- Actual geometric local transgression, with no recurrence, structure
equation, unit constraint or local-transgression premise supplied by the caller. -/
theorem framePatch_transgression :
    degreeCastForm (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
      (exteriorDerivative (framePatchAngularForm n M b s)) =
      -pullback (framePatchProjection n M s) (fun x ↦ frameEulerForm n M x (b x)) := by
  rw [exteriorDerivative_framePatchAngularForm n M b s hb]
  congr 1
  have htop :
      Chern.recurrencePolynomial n (Fin.last n) (framePatchDirectionForm n M b s)
        (framePatchCurvatureForm n M b s) =
      ∑ σ : Equiv.Perm (Fin (2*n)), (↑(Equiv.Perm.sign σ) : ℝ) •
        Chern.twoFormProduct n (fun j ↦ framePatchCurvatureForm n M b s
          (σ (pairFirst j)) (σ (pairSecond j))) :=
    Chern.recurrencePolynomial_top (E := Model n × Model n)
      (P := frameNonzeroDomain n M s) n (framePatchDirectionForm n M b s)
      (framePatchCurvatureForm n M b s)
  have htop_smul := congrArg
    (fun η : Form 𝓘(ℝ,Model n × Model n) (frameNonzeroDomain n M s) (2*n) ↦
      Chern.angularCoefficient n n • η) htop
  have hend :
      pullback (I := 𝓘(ℝ,Model n × Model n)) (I' := model n)
        (framePatchProjection n M s)
        (Chern.angularCoefficient n n • Chern.recurrencePolynomial n ⟨n,by omega⟩
          (fun _ ↦ (0 : Form (model n) M 1)) (smoothFrameCurvatureTwoForm n M b)) =
      pullback (I := 𝓘(ℝ,Model n × Model n)) (I' := model n)
        (framePatchProjection n M s) (fun x ↦ frameEulerForm n M x (b x)) :=
    congrArg (fun η : Form (model n) M (2*n) ↦
      pullback (I := 𝓘(ℝ,Model n × Model n)) (I' := model n)
        (framePatchProjection n M s) η)
      (recurrencePolynomial_smoothFrame_top_euler n M b
        (fun _ ↦ (0 : Form (model n) M 1)))
  have hbase_top := Chern.recurrencePolynomial_top (E := Model n) (P := M) n
    (fun _ ↦ (0 : Form (model n) M 1)) (smoothFrameCurvatureTwoForm n M b)
  rw [hbase_top] at hend
  simp only [Chern.angularPullback_smul, Chern.angularPullback_sum,
    Chern.pullback_twoFormProduct] at hend
  exact htop_smul.trans hend

/-- The global Chern angular form built from the actual positive chart
frames satisfies the exact Euler transgression equation in every even dimension. -/
theorem sphereAngularDerivative_eq_neg_euler (a : FiniteOrientedAtlas n M) :
    sphereAngularDerivative n M a = -sphereEulerForm n M a Fact.out := by
  apply sphereAngularDerivative_eq_neg_euler_of_local_transgression n M a
  intro i v hi hv
  exact framePatch_transgression_to_ambient n M (chartOrthonormalBasis n M (a.chart i))
    ⟨(a.chart i).source,(a.chart i).open_source⟩
    (contMDiffOn_chartOrthonormalBasis n M (a.chart i) (a.smooth i))
    (framePatch_transgression n M (chartOrthonormalBasis n M (a.chart i))
      ⟨(a.chart i).source,(a.chart i).open_source⟩
      (contMDiffOn_chartOrthonormalBasis n M (a.chart i) (a.smooth i))) v hi hv

end GaussBonnetChern
