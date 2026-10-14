import GaussBonnetChern.ChernGlobalTransgression

/-! Recovery of a genuine local form identity from its open restriction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Bundle Filter
open scoped Manifold ContDiff Topology BigOperators

namespace GaussBonnetChern.DifferentialForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℝ,E) ∞ P]
  {k : ℕ}

/-- Restriction to an actual open submanifold loses no information at a
point of that submanifold. Surjectivity of the inclusion derivative is
proved by a genuine smooth local inverse, using the actual chain rule. -/
theorem pullback_open_inclusion_at_injective (U : TopologicalSpace.Opens P)
    (α β : Form 𝓘(ℝ,E) P k) (x : P) (hx : x ∈ U)
    (h : pullback (I := 𝓘(ℝ,E)) ((↑) : U → P) α ⟨x,hx⟩ =
      pullback (I := 𝓘(ℝ,E)) ((↑) : U → P) β ⟨x,hx⟩) : α x = β x := by
  classical
  let z : U := ⟨x,hx⟩
  let g : P → U := fun y ↦ if hy : y ∈ U then ⟨y,hy⟩ else z
  let inc : U → P := (↑)
  have hgerm : inc ∘ g =ᶠ[𝓝 x] id := by
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    change y ∈ U at hy
    have hgy : g y = ⟨y,hy⟩ := by
      change (if hy : y ∈ U then ⟨y,hy⟩ else z) = ⟨y,hy⟩
      rw [dif_pos hy]
    exact congrArg Subtype.val hgy
  have hg : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) g x := by
    have hs : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ g x := by
      apply (ContMDiffAt.subtypeVal_comp_iff U g x).mp
      exact contMDiffAt_id.congr_of_eventuallyEq hgerm
    exact hs.mdifferentiableAt (by simp)
  have hz : g x = z := by
    change (if hx : x ∈ U then ⟨x,hx⟩ else z) = ⟨x,hx⟩
    rw [dif_pos hx]
  have hinc : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) inc (g x) :=
    (contMDiff_subtype_val (I := 𝓘(ℝ,E)) (n := ∞) (U := U)).mdifferentiable (by simp) _
  have hchain := mfderiv_comp x hinc hg
  have hright (v : TangentSpace 𝓘(ℝ,E) x) :
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) inc z (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) g x v) = v := by
    have hc := congrArg (fun L ↦ L v) hchain
    have hi : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (inc ∘ g) x v = v := by
      calc
        _ = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) id x v :=
          congrArg (fun L ↦ L v) (hgerm.mfderiv_eq (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)))
        _ = v := by rw [mfderiv_id]; rfl
    rw [hi] at hc
    rw [← hz]
    change ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) inc (g x)).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) g x)) v = v
    exact hc.symm
  ext v
  have heval := congrArg (fun η ↦ η (fun j ↦ mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) g x (v j))) h
  simp only [pullback_apply] at heval
  have hvec : (fun j ↦ mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) inc z
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) g x (v j))) = v := funext fun j ↦ hright (v j)
  exact hvec ▸ heval

end GaussBonnetChern.DifferentialForm

namespace GaussBonnetChern
open DifferentialForm
universe u
variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] [Fact (0<n)]

/-- A true transgression identity on the actual nonzero tangent patch
implies the ambient pointwise identity needed for global assembly. The
patch identity is explicit input and is not supplied as a geometry axiom. -/
theorem framePatch_transgression_to_ambient
    (b : (x : M) → OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace (model n) x))
    (s : TopologicalSpace.Opens M)
    (hb : ∀ i, ContMDiffOn (model n) (model n).tangent ∞ (T% (fun x ↦ b x i)) s)
    (hpatch : degreeCastForm (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
      (exteriorDerivative (framePatchAngularForm n M b s)) =
      -pullback (framePatchProjection n M s) (fun x ↦ frameEulerForm n M x (b x)))
    (v : TangentBundle (model n) M) (hvs : v.1 ∈ s) (hv0 : v.2 ≠ 0) :
    degreeCastForm (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
      (exteriorDerivative (frameTangentAngularForm n M b)) v =
      -pullback (I := 𝓘(ℝ,Model n × Model n))
        (Bundle.TotalSpace.proj : TangentBundle (model n) M → M)
        (fun x ↦ frameEulerForm n M x (b x)) v := by
  let U := frameNonzeroDomain n M s
  let inc : U → TangentBundle (model n) M := (↑)
  let projection : TangentBundle (model n) M → M := Bundle.TotalSpace.proj
  let α : Form (model n) M (2*n) := fun x ↦ frameEulerForm n M x (b x)
  have hd := restrict_exteriorDerivative_of_chartSmoothAt U
    (frameTangentAngularForm n M b) (fun w hw ↦
      contDiffAt_chartRepresentation_frameTangentAngularForm n M b s hb w hw.1 hw.2)
  have hinc : MDifferentiable 𝓘(ℝ,Model n × Model n) (model n).tangent inc := by
    simpa only [modelWithCornersSelf_prod] using
      (contMDiff_subtype_val (I := 𝓘(ℝ,Model n × Model n)) (n := ∞)
        (U := U)).mdifferentiable (by simp)
  have hπ := (contMDiff_proj (F := Model n) (IB := model n) (n := ∞)
    (TangentSpace (model n) : M → Type _)).mdifferentiable (by simp)
  have heuler : pullback (I := 𝓘(ℝ,Model n × Model n)) inc
      (-pullback (I := 𝓘(ℝ,Model n × Model n)) projection α) =
      -pullback (framePatchProjection n M s) α := by
    funext w
    ext z
    have hc := pullback_comp_at (I := 𝓘(ℝ,Model n × Model n))
      (I' := (model n).tangent) inc projection α w (hinc w) (hπ (inc w))
    exact congrArg (fun η ↦ -(η z)) hc.symm
  apply pullback_open_inclusion_at_injective U _ _ v ⟨hvs,hv0⟩
  have hrestricted : pullback (I := 𝓘(ℝ,Model n × Model n)) inc
      (degreeCastForm (show (2*n-1)+1=2*n by have hn : 0<n := Fact.out; omega)
        (exteriorDerivative (frameTangentAngularForm n M b))) =
      pullback (I := 𝓘(ℝ,Model n × Model n)) inc
        (-pullback (I := 𝓘(ℝ,Model n × Model n)) projection α) := by
    rw [Chern.angularPullback_degreeCast, hd,
      ← framePatchAngularForm_eq_restrict n M b s hb, hpatch, heuler]
  exact congrFun hrestricted ⟨v,⟨hvs,hv0⟩⟩

end GaussBonnetChern
