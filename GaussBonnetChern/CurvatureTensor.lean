import GaussBonnetChern.ConnectionSmoothness

/-! # Tensorial properties of the curvature used in the statement

All curvature expressions here use `GaussBonnetChern.connection` and the
original `GaussBonnetChern.curvature`; no independent curvature is assumed.
-/

noncomputable section

open Bundle FiberBundle Filter Module
open scoped Manifold Topology ContDiff

namespace GaussBonnetChern

universe u

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

omit [IsManifold (model n) ∞ M] in
theorem mvfderiv_mpullback_scalar {f : M → ℝ} {g : Model n → M}
    (V : (x : M) → TangentSpace (model n) x) (y : Model n)
    (hf : MDifferentiableAt (model n) 𝓘(ℝ) f (g y))
    (hg : MDifferentiableAt (model n) (model n) g y)
    (hgi : (mfderiv (model n) (model n) g y).IsInvertible) :
    mvfderiv (model n) (f ∘ g) y (VectorField.mpullback (model n) (model n) g V y) =
      mvfderiv (model n) f (g y) (V (g y)) := by
  rw [mvfderiv_comp_apply y hf hg]
  exact congrArg (mvfderiv (model n) f (g y))
    (hgi.self_apply_inverse _)

theorem mvfderiv_scalar_eventuallyEq {f g : Model n → ℝ} {x : Model n}
    (h : f =ᶠ[𝓝 x] g) : mvfderiv (model n) f x = mvfderiv (model n) g x := by
  exact h.mfderiv_eq

set_option backward.isDefEq.respectTransparency false in
theorem mvfderiv_mlieBracket_scalar
    {X Y : (x : M) → TangentSpace (model n) x} {f : M → ℝ} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) :
    mvfderiv (model n) f x (VectorField.mlieBracket (model n) X Y x) =
      mvfderiv (model n) (fun y ↦ mvfderiv (model n) f y (Y y)) x (X x) -
        mvfderiv (model n) (fun y ↦ mvfderiv (model n) f y (X y)) x (Y x) := by
  let : IsManifold (model n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (model n) 2 M)
  let e := chartAt (Model n) x
  let g : Model n → M := e.symm
  let q := e x
  have hq : q ∈ e.target := e.map_source (mem_chart_source (Model n) x)
  have hqx : g q = x := e.left_inv (mem_chart_source (Model n) x)
  have hge (z : Model n) (hz : z ∈ e.target) :
      ContMDiffAt (model n) (model n) ∞ g z :=
    (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I := model n) x)).contMDiffAt
      (e.open_target.mem_nhds hz)
  have hgi (z : Model n) (hz : z ∈ e.target) :
      (mfderiv (model n) (model n) g z).IsInvertible :=
    ⟨(mdifferentiable_chart (I := model n) x).symm.mfderiv hz, rfl⟩
  have hfg : ContMDiffAt (model n) 𝓘(ℝ) ∞ (f ∘ g) q := hf.comp_of_eq (hge q hq) hqx
  have hXg : ContMDiffAt (model n) (model n).tangent ∞ (T% X) (g q) := by simpa [hqx] using hX
  have hYg : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) (g q) := by simpa [hqx] using hY
  have hXP := hXg.mpullback_vectorField_preimage (hge q hq) (hgi q hq) (by simp)
  have hYP := hYg.mpullback_vectorField_preimage (hge q hq) (hgi q hq) (by simp)
  have heq (V : (x : M) → TangentSpace (model n) x) :
      (fun z ↦ mvfderiv (model n) (f ∘ g) z (VectorField.mpullback (model n) (model n) g V z))
        =ᶠ[𝓝 q] (fun z ↦ mvfderiv (model n) f (g z) (V (g z))) := by
    have hf1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
      (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
    have hgt : Tendsto g (𝓝 q) (𝓝 x) := by
      simpa only [hqx] using (hge q hq).continuousAt.tendsto
    have hf1g : ∀ᶠ z in 𝓝 q, ContMDiffAt (model n) 𝓘(ℝ) 1 f (g z) := hgt.eventually hf1
    filter_upwards [e.open_target.mem_nhds hq, hf1g] with z hz hfz
    exact mvfderiv_mpullback_scalar n M V z (hfz.mdifferentiableAt (by simp))
      ((hge z hz).mdifferentiableAt (by simp)) (hgi z hz)
  have H := VectorField.fderiv_apply_lieBracket hfg.contDiffAt (by simp)
    ((contMDiffAt_vectorSpace_iff_contDiffAt.mp hYP).differentiableAt (by simp))
    ((contMDiffAt_vectorSpace_iff_contDiffAt.mp hXP).differentiableAt (by simp))
  have H' : mvfderiv (model n) (f ∘ g) q
        (VectorField.mlieBracket (model n)
          (VectorField.mpullback (model n) (model n) g X)
          (VectorField.mpullback (model n) (model n) g Y) q) =
      mvfderiv (model n) (fun z ↦ mvfderiv (model n) (f ∘ g) z
        (VectorField.mpullback (model n) (model n) g Y z)) q
          (VectorField.mpullback (model n) (model n) g X q) -
      mvfderiv (model n) (fun z ↦ mvfderiv (model n) (f ∘ g) z
        (VectorField.mpullback (model n) (model n) g X z)) q
          (VectorField.mpullback (model n) (model n) g Y q) := by
    simp only [model, mvfderiv_eq_fderiv, VectorField.mlieBracket,
      VectorField.mlieBracketWithin_eq_lieBracketWithin, VectorField.lieBracketWithin,
      VectorField.lieBracket, fderivWithin_univ] at H ⊢
    convert! H using 1
  rw [← VectorField.mpullback_mlieBracket (hXg.mdifferentiableAt (by simp))
    (hYg.mdifferentiableAt (by simp)) (hge q hq) (by simp)] at H'
  rw [mvfderiv_scalar_eventuallyEq n (heq Y), mvfderiv_scalar_eventuallyEq n (heq X)] at H'
  have hfq : MDifferentiableAt (model n) 𝓘(ℝ) f (g q) := by
    simpa [hqx] using hf.mdifferentiableAt (by simp)
  have hdY : MDifferentiableAt (model n) 𝓘(ℝ)
      (fun y ↦ mvfderiv (model n) f y (Y y)) (g q) := by
    simpa [hqx] using (contMDiffAt_directionalDerivative n M hf hY).mdifferentiableAt (by simp)
  have hdX : MDifferentiableAt (model n) 𝓘(ℝ)
      (fun y ↦ mvfderiv (model n) f y (X y)) (g q) := by
    simpa [hqx] using (contMDiffAt_directionalDerivative n M hf hX).mdifferentiableAt (by simp)
  have hpY := mvfderiv_mpullback_scalar n M X q hdY
    ((hge q hq).mdifferentiableAt (by simp)) (hgi q hq)
  have hpX := mvfderiv_mpullback_scalar n M Y q hdX
    ((hge q hq).mdifferentiableAt (by simp)) (hgi q hq)
  simp only [Function.comp_def] at hpY hpX
  rw [mvfderiv_mpullback_scalar n M _ q hfq ((hge q hq).mdifferentiableAt (by simp)) (hgi q hq),
    hpY, hpX] at H'
  exact hqx ▸ H'


/-- Module linearity on smooth germs forces an operation to depend only on
the value at the point. This criterion does not require the operation to
act tensorially on merely differentiable germs. -/
theorem pointwise_of_smooth_linearity {A : Type*} [AddCommGroup A] [Module ℝ A]
    {Φ : ((y : M) → TangentSpace (model n) y) → A} {x : M}
    (hsmul : ∀ {f : M → ℝ} {Z : (y : M) → TangentSpace (model n) y},
      ContMDiffAt (model n) 𝓘(ℝ) ∞ f x →
      ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x → Φ (f • Z) = f x • Φ Z)
    (hadd : ∀ {Z Z' : (y : M) → TangentSpace (model n) y},
      ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x →
      ContMDiffAt (model n) (model n).tangent ∞ (T% Z') x → Φ (Z + Z') = Φ Z + Φ Z')
    {Z Z' : (y : M) → TangentSpace (model n) y}
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hZ' : ContMDiffAt (model n) (model n).tangent ∞ (T% Z') x)
    (hZZ' : Z x = Z' x) : Φ Z = Φ Z' := by
  classical
  have hlocal {σ σ' : (y : M) → TangentSpace (model n) y}
      (hσ : ContMDiffAt (model n) (model n).tangent ∞ (T% σ) x)
      (hσ' : ContMDiffAt (model n) (model n).tangent ∞ (T% σ') x)
      (heq : ∀ᶠ y in 𝓝 x, σ y = σ' y) : Φ σ = Φ σ' := by
    let ψ (y : M) : ℝ := if σ y = σ' y then 1 else 0
    have hψ : ContMDiffAt (model n) 𝓘(ℝ) ∞ ψ x :=
      (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
        (heq.mono fun y hy ↦ by simp [ψ, hy])
    have hψx : ψ x = 1 := by simp [ψ, heq.self_of_nhds]
    have hp : ψ • σ = ψ • σ' := by
      funext y
      dsimp [ψ]
      split_ifs with hy <;> simp [hy]
    calc
      Φ σ = Φ (ψ • σ) := by rw [hsmul hψ hσ, hψx, one_smul]
      _ = Φ (ψ • σ') := congrArg Φ hp
      _ = Φ σ' := by rw [hsmul hψ hσ', hψx, one_smul]
  have hz : Φ 0 = 0 := by
    have h := hsmul (f := (0 : M → ℝ)) (Z := 0) contMDiffAt_const
      (contMDiffAt_zeroSection ℝ _)
    simpa using h
  have hsum {ι : Type} (s : Finset ι) (σ : ι → (y : M) → TangentSpace (model n) y)
      (hσ : ∀ i ∈ s, ContMDiffAt (model n) (model n).tangent ∞ (T% (σ i)) x) :
      Φ (fun y ↦ ∑ i ∈ s, σ i y) = ∑ i ∈ s, Φ (σ i) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty, ← Pi.zero_def] using hz
    | @insert i s hi ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
      simp only [Finset.sum_insert hi, ← ih hσ.2]
      exact hadd hσ.1 (.sum_section hσ.2)
  let t := trivializationAt (Model n) (TangentSpace (model n) : M → Type _) x
  have hx : x ∈ t.baseSet := mem_baseSet_trivializationAt' x
  let b := Basis.ofVectorSpace ℝ (Model n)
  let s := t.localFrame b
  let c := t.localFrameCoeff (model n) b
  have hs (i) : ContMDiffAt (model n) (model n).tangent ∞ (T% (s i)) x :=
    contMDiffAt_localFrame_of_mem ∞ _ b i hx
  have hc {σ : (y : M) → TangentSpace (model n) y}
      (hσ : ContMDiffAt (model n) (model n).tangent ∞ (T% σ) x) (i) :
      ContMDiffAt (model n) 𝓘(ℝ) ∞ (LinearMap.piApply (c i) σ) x :=
    contMDiffAt_localFrameCoeff b hx hσ i
  have hexp {σ : (y : M) → TangentSpace (model n) y}
      (hσ : ContMDiffAt (model n) (model n).tangent ∞ (T% σ) x) :
      Φ σ = Φ (fun y ↦ ∑ i, c i y (σ y) • s i y) :=
    hlocal hσ (.sum_section fun i _ ↦ (hc hσ i).smul_section (hs i))
      (t.eventually_eq_localFrame_sum_coeff_smul b hx)
  rw [hexp hZ, hexp hZ', hsum, hsum]
  · congr! 1 with i
    calc
      Φ ((LinearMap.piApply (c i) Z) • s i) = c i x (Z x) • Φ (s i) :=
        hsmul (hc hZ i) (hs i)
      _ = c i x (Z' x) • Φ (s i) := by rw [hZZ']
      _ = Φ ((LinearMap.piApply (c i) Z') • s i) := (hsmul (hc hZ' i) (hs i)).symm
  · exact fun i _ ↦ (hc hZ' i).smul_section (hs i)
  · exact fun i _ ↦ (hc hZ i).smul_section (hs i)


variable
  [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)]

/-- The connection commutator on vector fields, with the same convention as
the original curvature definition. -/
def curvatureOnFields (X Y Z : (x : M) → TangentSpace (model n) x)
    (x : M) : TangentSpace (model n) x :=
  connection n M (fun y ↦ connection n M Z y (Y y)) x (X x) -
    connection n M (fun y ↦ connection n M Z y (X y)) x (Y x) -
    connection n M Z x (VectorField.mlieBracket (model n) X Y x)

/-- Swapping the two directions negates the connection commutator. -/
theorem curvatureOnFields_swap (X Y Z : (x : M) → TangentSpace (model n) x) (x : M) :
    curvatureOnFields n M X Y Z x = -curvatureOnFields n M Y X Z x := by
  simp only [curvatureOnFields, VectorField.mlieBracket_swap (V := Y) (W := X), Pi.neg_apply, map_neg]
  module

/-- The original curvature is the commutator applied to the library's
local extensions at exactly the given base point. -/
theorem curvature_eq_curvatureOnFields_extend (x : M)
    (u v w : TangentSpace (model n) x) :
    curvature n M x u v w = curvatureOnFields n M
      (extend (Model n) (x := x) u) (extend (Model n) (x := x) v)
      (extend (Model n) (x := x) w) x := by
  simp only [curvature, curvatureOnFields, extend_apply_self]

/-- Antisymmetry of the two tangent direction slots of the original curvature. -/
theorem curvature_swap (x : M) (u v w : TangentSpace (model n) x) :
    curvature n M x u v w = -curvature n M x v u w := by
  simpa only [curvature_eq_curvatureOnFields_extend] using
    curvatureOnFields_swap n M (extend (Model n) u) (extend (Model n) v)
      (extend (Model n) w) x

/-- A smooth differentiated field and a differentiable direction give a
differentiable covariant derivative at the point. -/
theorem mdifferentiableAt_connection_apply
    {X Z : (x : M) → TangentSpace (model n) x} {x : M}
    (hX : MDifferentiableAt (model n) (model n).tangent (T% X) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x) :
    MDifferentiableAt (model n) (model n).tangent
      (T% (fun y ↦ connection n M Z y (X y))) x := by
  exact ((contMDiffAt_connection_section n M hZ).mdifferentiableAt (by simp)).clm_bundle_apply hX

/-- With the differentiated field smooth, the commutator is tensorial in
its first direction in the library's genuine `TensorialAt` sense. -/
theorem curvatureOnFields_tensorial_first
    (Y Z : (x : M) → TangentSpace (model n) x) (x : M)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x) :
    TensorialAt (model n) (Model n) (fun X ↦ curvatureOnFields n M X Y Z x) x where
  smul {f} {X} hf hX := by
    have hXZ := mdifferentiableAt_connection_apply n M hX hZ
    have hc := (connection n M).isCovariantDerivativeOnUniv
    have heq : connection n M (fun y ↦ f y • connection n M Z y (X y)) x =
        f x • connection n M (fun y ↦ connection n M Z y (X y)) x +
          (mvfderiv (model n) f x).smulRight (connection n M Z x (X x)) :=
      hc.leibniz hXZ hf
    simp [curvatureOnFields, heq,
      VectorField.mlieBracket_smul_left hf hX]
    module
  add {X} {X'} hX hX' := by
    have hXZ := mdifferentiableAt_connection_apply n M hX hZ
    have hX'Z := mdifferentiableAt_connection_apply n M hX' hZ
    have hc := (connection n M).isCovariantDerivativeOnUniv
    have heq : connection n M
        (fun y ↦ connection n M Z y (X y) + connection n M Z y (X' y)) x =
      connection n M (fun y ↦ connection n M Z y (X y)) x +
        connection n M (fun y ↦ connection n M Z y (X' y)) x := hc.add hXZ hX'Z
    simp [curvatureOnFields, heq,
      VectorField.mlieBracket_add_left hX hX']
    module

/-- Tensoriality in the second direction follows from antisymmetry. -/
theorem curvatureOnFields_tensorial_second
    (X Z : (x : M) → TangentSpace (model n) x) (x : M)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x) :
    TensorialAt (model n) (Model n) (fun Y ↦ curvatureOnFields n M X Y Z x) x where
  smul hf hY := by
    rw [curvatureOnFields_swap,
      (curvatureOnFields_tensorial_first n M X Z x hZ).smul hf hY,
      curvatureOnFields_swap n M X]
    simp
  add hY hY' := by
    rw [curvatureOnFields_swap,
      (curvatureOnFields_tensorial_first n M X Z x hZ).add hY hY',
      curvatureOnFields_swap n M X, curvatureOnFields_swap n M X]
    module

/-- The commutator depends only on the values of its first two fields. -/
theorem curvatureOnFields_pointwise_directions
    {X X' Y Y' Z : (x : M) → TangentSpace (model n) x} {x : M}
    (hX : MDifferentiableAt (model n) (model n).tangent (T% X) x)
    (hX' : MDifferentiableAt (model n) (model n).tangent (T% X') x)
    (hY : MDifferentiableAt (model n) (model n).tangent (T% Y) x)
    (hY' : MDifferentiableAt (model n) (model n).tangent (T% Y') x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hXX' : X x = X' x) (hYY' : Y x = Y' x) :
    curvatureOnFields n M X Y Z x = curvatureOnFields n M X' Y' Z x := by
  exact TensorialAt.pointwise₂
    (fun Y _ ↦ curvatureOnFields_tensorial_first n M Y Z x hZ)
    (fun X _ ↦ curvatureOnFields_tensorial_second n M X Z x hZ)
    hX hX' hY hY' hXX' hYY'

/-- The raw tangent-vector curvature may be evaluated using any differentiable
first two direction fields; the differentiated field is still its canonical extension. -/
theorem curvature_apply_directions
    {X Y : (x : M) → TangentSpace (model n) x} {x : M}
    (hX : MDifferentiableAt (model n) (model n).tangent (T% X) x)
    (hY : MDifferentiableAt (model n) (model n).tangent (T% Y) x)
    (w : TangentSpace (model n) x) :
    curvature n M x (X x) (Y x) w =
      curvatureOnFields n M X Y (extend (Model n) (x := x) w) x := by
  rw [curvature_eq_curvatureOnFields_extend]
  exact curvatureOnFields_pointwise_directions n M
    (mdifferentiableAt_extend ..) hX (mdifferentiableAt_extend ..) hY
    (contMDiffAt_extend ..) (by simp) (by simp)

/-- The connection commutator of locally smooth fields is locally smooth. -/
theorem contMDiffAt_curvatureOnFields
    {X Y Z : (x : M) → TangentSpace (model n) x} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x) :
    ContMDiffAt (model n) (model n).tangent ∞ (T% (curvatureOnFields n M X Y Z)) x := by
  let : IsManifold (model n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (model n) 2 M)
  let : IsManifold (model n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (model n) ∞ M)
  have h1 := contMDiffAt_connection_apply n M hX (contMDiffAt_connection_apply n M hY hZ)
  have h2 := contMDiffAt_connection_apply n M hY (contMDiffAt_connection_apply n M hX hZ)
  have hXY := hX.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hY (by simp)
  have h3 := contMDiffAt_connection_apply n M hXY hZ
  exact (h1.sub_section h2).sub_section h3

omit [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] in
theorem eventually_mdifferentiableAt_field
    {Z : (y : M) → TangentSpace (model n) y} {x : M}
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt (model n) (model n).tangent (T% Z) y := by
  have h := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
    (hZ.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  exact h.mono fun y hy ↦ hy.mdifferentiableAt (by simp)

theorem connection_smul_germ
    (Y : (y : M) → TangentSpace (model n) y)
    {Z : (y : M) → TangentSpace (model n) y} {f : M → ℝ} {x : M}
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) :
    (fun y ↦ connection n M (f • Z) y (Y y)) =ᶠ[𝓝 x]
      (fun y ↦ f y • connection n M Z y (Y y) +
        mvfderiv (model n) f y (Y y) • Z y) := by
  have hf1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
    (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  filter_upwards [eventually_mdifferentiableAt_field n M hZ, hf1] with y hzy hfy
  have h := (connection n M).isCovariantDerivativeOnUniv.leibniz hzy
    (hfy.mdifferentiableAt (by simp))
  convert! congrArg (fun L : TangentSpace (model n) y →L[ℝ] TangentSpace (model n) y ↦ L (Y y)) h using 1

theorem connection_twice_smul
    {X Y Z : (y : M) → TangentSpace (model n) y} {f : M → ℝ} {x : M}
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) :
    connection n M (fun y ↦ connection n M (f • Z) y (Y y)) x (X x) =
      f x • connection n M (fun y ↦ connection n M Z y (Y y)) x (X x) +
      mvfderiv (model n) f x (X x) • connection n M Z x (Y x) +
      mvfderiv (model n) f x (Y x) • connection n M Z x (X x) +
      mvfderiv (model n) (fun y ↦ mvfderiv (model n) f y (Y y)) x (X x) • Z x := by
  let A := fun y ↦ connection n M Z y (Y y)
  let D := fun y ↦ mvfderiv (model n) f y (Y y)
  have hA := contMDiffAt_connection_apply n M hY hZ
  have hD := contMDiffAt_directionalDerivative n M hf hY
  have hL := contMDiffAt_connection_apply n M hY (hf.smul_section hZ)
  have hR := (hf.smul_section hA).add_section (hD.smul_section hZ)
  have hc := (connection n M).isCovariantDerivativeOnUniv
  have heq := hc.congr_of_eventuallyEq (hL.mdifferentiableAt (by simp))
    (hR.mdifferentiableAt (by simp)) Filter.univ_mem (connection_smul_germ n M Y hZ hf)
  calc
    _ = connection n M (f • A + D • Z) x (X x) :=
      congrArg (fun L : TangentSpace (model n) x →L[ℝ] TangentSpace (model n) x ↦ L (X x)) heq
    _ = _ := by
      rw [hc.add ((hf.smul_section hA).mdifferentiableAt (by simp))
        ((hD.smul_section hZ).mdifferentiableAt (by simp)),
        hc.leibniz (hA.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)),
        hc.leibniz (hZ.mdifferentiableAt (by simp)) (hD.mdifferentiableAt (by simp))]
      simp
      module

theorem curvatureOnFields_smul_third
    {X Y Z : (y : M) → TangentSpace (model n) y} {f : M → ℝ} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ f x) :
    curvatureOnFields n M X Y (f • Z) x = f x • curvatureOnFields n M X Y Z x := by
  unfold curvatureOnFields
  rw [connection_twice_smul n M (X := X) hY hZ hf,
    connection_twice_smul n M (X := Y) hX hZ hf,
    (connection n M).isCovariantDerivativeOnUniv.leibniz
      (hZ.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  simp
  rw [mvfderiv_mlieBracket_scalar n M hX hY hf]
  module

theorem connection_add_germ
    (Y : (y : M) → TangentSpace (model n) y)
    {Z Z' : (y : M) → TangentSpace (model n) y} {x : M}
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hZ' : ContMDiffAt (model n) (model n).tangent ∞ (T% Z') x) :
    (fun y ↦ connection n M (Z + Z') y (Y y)) =ᶠ[𝓝 x]
      (fun y ↦ connection n M Z y (Y y) + connection n M Z' y (Y y)) := by
  filter_upwards [eventually_mdifferentiableAt_field n M hZ,
    eventually_mdifferentiableAt_field n M hZ'] with y hzy hzy'
  have h := (connection n M).isCovariantDerivativeOnUniv.add hzy hzy'
  convert! congrArg (fun L : TangentSpace (model n) y →L[ℝ] TangentSpace (model n) y ↦ L (Y y)) h using 1

theorem connection_twice_add
    {X Y Z Z' : (y : M) → TangentSpace (model n) y} {x : M}
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hZ' : ContMDiffAt (model n) (model n).tangent ∞ (T% Z') x) :
    connection n M (fun y ↦ connection n M (Z + Z') y (Y y)) x (X x) =
      connection n M (fun y ↦ connection n M Z y (Y y)) x (X x) +
        connection n M (fun y ↦ connection n M Z' y (Y y)) x (X x) := by
  let A := fun y ↦ connection n M Z y (Y y)
  let B := fun y ↦ connection n M Z' y (Y y)
  have hA := contMDiffAt_connection_apply n M hY hZ
  have hB := contMDiffAt_connection_apply n M hY hZ'
  have hL := contMDiffAt_connection_apply n M hY (hZ.add_section hZ')
  have hc := (connection n M).isCovariantDerivativeOnUniv
  have heq := hc.congr_of_eventuallyEq (hL.mdifferentiableAt (by simp))
    ((hA.add_section hB).mdifferentiableAt (by simp)) Filter.univ_mem
    (connection_add_germ n M Y hZ hZ')
  calc
    _ = connection n M (A + B) x (X x) :=
      congrArg (fun L : TangentSpace (model n) x →L[ℝ] TangentSpace (model n) x ↦ L (X x)) heq
    _ = _ := by
      rw [hc.add (hA.mdifferentiableAt (by simp)) (hB.mdifferentiableAt (by simp))]
      rfl

theorem curvatureOnFields_add_third
    {X Y Z Z' : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hZ' : ContMDiffAt (model n) (model n).tangent ∞ (T% Z') x) :
    curvatureOnFields n M X Y (Z + Z') x =
      curvatureOnFields n M X Y Z x + curvatureOnFields n M X Y Z' x := by
  unfold curvatureOnFields
  rw [connection_twice_add n M (X := X) hY hZ hZ',
    connection_twice_add n M (X := Y) hX hZ hZ',
    (connection n M).isCovariantDerivativeOnUniv.add
      (hZ.mdifferentiableAt (by simp)) (hZ'.mdifferentiableAt (by simp))]
  simp
  module


/-- For smooth direction fields, the connection commutator depends only on
the value of the smooth differentiated field at the point. -/
theorem curvatureOnFields_pointwise_third
    {X Y Z Z' : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hZ' : ContMDiffAt (model n) (model n).tangent ∞ (T% Z') x)
    (hZZ' : Z x = Z' x) :
    curvatureOnFields n M X Y Z x = curvatureOnFields n M X Y Z' x := by
  exact pointwise_of_smooth_linearity n M (Φ := fun W ↦ curvatureOnFields n M X Y W x)
    (fun hf hW ↦ curvatureOnFields_smul_third n M hX hY hW hf)
    (fun hW hW' ↦ curvatureOnFields_add_third n M hX hY hW hW') hZ hZ' hZZ'

/-- The original raw-extension curvature agrees with the connection
commutator on every triple of locally smooth vector fields. -/
theorem curvature_apply
    {X Y Z : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x) :
    curvature n M x (X x) (Y x) (Z x) = curvatureOnFields n M X Y Z x := by
  rw [curvature_apply_directions n M (hX.mdifferentiableAt (by simp))
    (hY.mdifferentiableAt (by simp))]
  exact curvatureOnFields_pointwise_third n M hX hY (contMDiffAt_extend ..) hZ (by simp)

/-- Additivity in the first tangent direction of the original curvature. -/
theorem curvature_add_first (x : M) (u u' v w : TangentSpace (model n) x) :
    curvature n M x (u + u') v w = curvature n M x u v w + curvature n M x u' v w := by
  let U := extend (Model n) (x := x) u
  let U' := extend (Model n) (x := x) u'
  let V := extend (Model n) (x := x) v
  let W := extend (Model n) (x := x) w
  have hU : ContMDiffAt (model n) (model n).tangent ∞ (T% U) x := contMDiffAt_extend ..
  have hU' : ContMDiffAt (model n) (model n).tangent ∞ (T% U') x := contMDiffAt_extend ..
  have hV : ContMDiffAt (model n) (model n).tangent ∞ (T% V) x := contMDiffAt_extend ..
  have hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x := contMDiffAt_extend ..
  have h := (curvature_apply n M (hU.add_section hU') hV hW).trans
    ((curvatureOnFields_tensorial_first n M V W x hW).add
      (hU.mdifferentiableAt (by simp)) (hU'.mdifferentiableAt (by simp)))
  simpa only [U, U', V, W, Pi.add_apply, extend_apply_self,
    ← curvature_eq_curvatureOnFields_extend] using h

/-- Real scalar linearity in the first tangent direction. -/
theorem curvature_smul_first (x : M) (c : ℝ) (u v w : TangentSpace (model n) x) :
    curvature n M x (c • u) v w = c • curvature n M x u v w := by
  let U := extend (Model n) (x := x) u
  let V := extend (Model n) (x := x) v
  let W := extend (Model n) (x := x) w
  have hU : ContMDiffAt (model n) (model n).tangent ∞ (T% U) x := contMDiffAt_extend ..
  have hV : ContMDiffAt (model n) (model n).tangent ∞ (T% V) x := contMDiffAt_extend ..
  have hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x := contMDiffAt_extend ..
  have hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ (fun _ : M ↦ c) x := contMDiffAt_const
  have h := (curvature_apply n M (hf.smul_section hU) hV hW).trans
    ((curvatureOnFields_tensorial_first n M V W x hW).smul
      (hf.mdifferentiableAt (by simp)) (hU.mdifferentiableAt (by simp)))
  change curvature n M x (c • U x) (V x) (W x) = c • curvatureOnFields n M U V W x at h
  simpa only [U, V, W, Pi.smul_apply, extend_apply_self,
    ← curvature_eq_curvatureOnFields_extend] using h

theorem curvature_add_second (x : M) (u v v' w : TangentSpace (model n) x) :
    curvature n M x u (v + v') w = curvature n M x u v w + curvature n M x u v' w := by
  rw [curvature_swap n M x u (v + v') w, curvature_add_first,
    curvature_swap n M x v u w, curvature_swap n M x v' u w]
  module

theorem curvature_smul_second (x : M) (c : ℝ) (u v w : TangentSpace (model n) x) :
    curvature n M x u (c • v) w = c • curvature n M x u v w := by
  rw [curvature_swap n M x u (c • v) w, curvature_smul_first,
    curvature_swap n M x v u w]
  module

/-- Additivity in the differentiated tangent vector. -/
theorem curvature_add_third (x : M) (u v w w' : TangentSpace (model n) x) :
    curvature n M x u v (w + w') = curvature n M x u v w + curvature n M x u v w' := by
  let U := extend (Model n) (x := x) u
  let V := extend (Model n) (x := x) v
  let W := extend (Model n) (x := x) w
  let W' := extend (Model n) (x := x) w'
  have hU : ContMDiffAt (model n) (model n).tangent ∞ (T% U) x := contMDiffAt_extend ..
  have hV : ContMDiffAt (model n) (model n).tangent ∞ (T% V) x := contMDiffAt_extend ..
  have hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x := contMDiffAt_extend ..
  have hW' : ContMDiffAt (model n) (model n).tangent ∞ (T% W') x := contMDiffAt_extend ..
  have h := (curvature_apply n M hU hV (hW.add_section hW')).trans
    (curvatureOnFields_add_third n M hU hV hW hW')
  simpa only [U, V, W, W', Pi.add_apply, extend_apply_self,
    ← curvature_eq_curvatureOnFields_extend] using h

/-- Real scalar linearity in the differentiated tangent vector. -/
theorem curvature_smul_third (x : M) (c : ℝ) (u v w : TangentSpace (model n) x) :
    curvature n M x u v (c • w) = c • curvature n M x u v w := by
  let U := extend (Model n) (x := x) u
  let V := extend (Model n) (x := x) v
  let W := extend (Model n) (x := x) w
  have hU : ContMDiffAt (model n) (model n).tangent ∞ (T% U) x := contMDiffAt_extend ..
  have hV : ContMDiffAt (model n) (model n).tangent ∞ (T% V) x := contMDiffAt_extend ..
  have hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x := contMDiffAt_extend ..
  have hf : ContMDiffAt (model n) 𝓘(ℝ) ∞ (fun _ : M ↦ c) x := contMDiffAt_const
  have h := (curvature_apply n M hU hV (hf.smul_section hW)).trans
    (curvatureOnFields_smul_third n M hU hV hW hf)
  change curvature n M x (U x) (V x) (c • W x) = c • curvatureOnFields n M U V W x at h
  simpa only [U, V, W, Pi.smul_apply, extend_apply_self,
    ← curvature_eq_curvatureOnFields_extend] using h

set_option synthInstance.maxHeartbeats 80000 in
/-- The original curvature, bundled as a continuous trilinear map. -/
def curvatureTensor (x : M) :
    TangentSpace (model n) x →L[ℝ] TangentSpace (model n) x →L[ℝ]
      TangentSpace (model n) x →L[ℝ] TangentSpace (model n) x :=
  LinearMap.toContinuousLinearMap {
    toFun u := LinearMap.toContinuousLinearMap {
      toFun v := LinearMap.toContinuousLinearMap {
        toFun w := curvature n M x u v w
        map_add' w w' := curvature_add_third n M x u v w w'
        map_smul' c w := curvature_smul_third n M x c u v w }
      map_add' v v' := by ext w; exact curvature_add_second n M x u v v' w
      map_smul' c v := by ext w; exact curvature_smul_second n M x c u v w }
    map_add' u u' := by ext v w; exact curvature_add_first n M x u u' v w
    map_smul' c u := by ext v w; exact curvature_smul_first n M x c u v w }

@[simp] theorem curvatureTensor_apply (x : M) (u v w : TangentSpace (model n) x) :
    curvatureTensor n M x u v w = curvature n M x u v w := rfl

/-- The original curvature evaluated on smooth local fields is smooth. -/
theorem contMDiffOn_curvature_apply
    {X Y Z : (y : M) → TangentSpace (model n) y} {s : Set M}
    (hs : IsOpen s)
    (hX : ContMDiffOn (model n) (model n).tangent ∞ (T% X) s)
    (hY : ContMDiffOn (model n) (model n).tangent ∞ (T% Y) s)
    (hZ : ContMDiffOn (model n) (model n).tangent ∞ (T% Z) s) :
    ContMDiffOn (model n) (model n).tangent ∞
      (T% (fun y ↦ curvature n M y (X y) (Y y) (Z y))) s := by
  intro x hx
  have h := contMDiffAt_curvatureOnFields n M (hX.contMDiffAt (hs.mem_nhds hx))
    (hY.contMDiffAt (hs.mem_nhds hx)) (hZ.contMDiffAt (hs.mem_nhds hx))
  apply (h.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hs.mem_nhds hx] with y hy
  congr 1
  exact curvature_apply n M (hX.contMDiffAt (hs.mem_nhds hy))
    (hY.contMDiffAt (hs.mem_nhds hy)) (hZ.contMDiffAt (hs.mem_nhds hy))

local instance curvatureMetricOne : IsContMDiffRiemannianBundle (model n) 1 (Model n)
    (TangentSpace (model n) : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)

theorem connection_isMetricCompatible : (connection n M).IsMetricCompatible := by
  exact CovariantDerivative.isMetricCompatible_leviCivitaConnection (model n)

theorem connection_inner_germ
    (X : (y : M) → TangentSpace (model n) y)
    {Z W : (y : M) → TangentSpace (model n) y} {x : M}
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x) :
    (fun y ↦ mvfderiv (model n) (fun z ↦ inner ℝ (Z z) (W z)) y (X y)) =ᶠ[𝓝 x]
      (fun y ↦ inner ℝ (connection n M Z y (X y)) (W y) +
        inner ℝ (Z y) (connection n M W y (X y))) := by
  filter_upwards [eventually_mdifferentiableAt_field n M hZ,
    eventually_mdifferentiableAt_field n M hW] with y hzy hwy
  exact (connection_isMetricCompatible n M).mvfderiv_inner_eq X hzy hwy

theorem connection_twice_inner
    (X : (y : M) → TangentSpace (model n) y)
    {Y Z W : (y : M) → TangentSpace (model n) y} {x : M}
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x) :
    mvfderiv (model n)
      (fun y ↦ mvfderiv (model n) (fun z ↦ inner ℝ (Z z) (W z)) y (Y y)) x (X x) =
      inner ℝ (connection n M (fun y ↦ connection n M Z y (Y y)) x (X x)) (W x) +
      inner ℝ (connection n M Z x (Y x)) (connection n M W x (X x)) +
      inner ℝ (connection n M Z x (X x)) (connection n M W x (Y x)) +
      inner ℝ (Z x) (connection n M (fun y ↦ connection n M W y (Y y)) x (X x)) := by
  have hA := contMDiffAt_connection_apply n M hY hZ
  have hB := contMDiffAt_connection_apply n M hY hW
  have heq : mvfderiv (model n)
      (fun y ↦ mvfderiv (model n) (fun z ↦ inner ℝ (Z z) (W z)) y (Y y)) x =
      mvfderiv (model n) (fun y ↦ inner ℝ (connection n M Z y (Y y)) (W y) +
        inner ℝ (Z y) (connection n M W y (Y y))) x := by
    exact (connection_inner_germ n M Y hZ hW).mfderiv_eq
  rw [heq, mvfderiv_fun_add ((hA.inner_bundle hW).mdifferentiableAt (by simp))
    ((hZ.inner_bundle hB).mdifferentiableAt (by simp))]
  simp
  rw [(connection_isMetricCompatible n M).mvfderiv_inner_eq X
      (hA.mdifferentiableAt (by simp)) (hW.mdifferentiableAt (by simp)),
    (connection_isMetricCompatible n M).mvfderiv_inner_eq X
      (hZ.mdifferentiableAt (by simp)) (hB.mdifferentiableAt (by simp))]
  ring

theorem curvatureOnFields_inner_skew
    {X Y Z W : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x)
    (hW : ContMDiffAt (model n) (model n).tangent ∞ (T% W) x) :
    inner ℝ (curvatureOnFields n M X Y Z x) (W x) +
      inner ℝ (Z x) (curvatureOnFields n M X Y W x) = 0 := by
  have h := mvfderiv_mlieBracket_scalar n M hX hY (hZ.inner_bundle hW)
  rw [(connection_isMetricCompatible n M).mvfderiv_inner_eq
      (VectorField.mlieBracket (model n) X Y) (hZ.mdifferentiableAt (by simp))
      (hW.mdifferentiableAt (by simp)),
    connection_twice_inner n M X hY hZ hW,
    connection_twice_inner n M Y hX hZ hW] at h
  simp only [curvatureOnFields, inner_sub_left, inner_sub_right]
  linear_combination -h

theorem curvature_inner_skew (x : M) (u v w z : TangentSpace (model n) x) :
    inner ℝ (curvature n M x u v w) z + inner ℝ w (curvature n M x u v z) = 0 := by
  have h := curvatureOnFields_inner_skew n M
    (X := extend (Model n) (x := x) u) (Y := extend (Model n) (x := x) v)
    (Z := extend (Model n) (x := x) w) (W := extend (Model n) (x := x) z)
    (contMDiffAt_extend ..) (contMDiffAt_extend ..) (contMDiffAt_extend ..) (contMDiffAt_extend ..)
  simpa only [extend_apply_self, ← curvature_eq_curvatureOnFields_extend] using h


theorem connection_torsion_eq_zero : (connection n M).torsion = 0 := by
  let : IsContMDiffRiemannianBundle (model n) 1 (Model n)
      (TangentSpace (model n) : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  exact CovariantDerivative.torsion_leviCivitaConnection_eq_zero (model n)

theorem connection_torsion_apply
    {X Y : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : MDifferentiableAt (model n) (model n).tangent (T% X) x)
    (hY : MDifferentiableAt (model n) (model n).tangent (T% Y) x) :
    connection n M Y x (X x) - connection n M X x (Y x) =
      VectorField.mlieBracket (model n) X Y x :=
  (CovariantDerivative.torsion_eq_zero_iff (connection n M)).mp
    (connection_torsion_eq_zero n M) hX hY

omit [RiemannianBundle (TangentSpace (model n) : M → Type _)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (TangentSpace (model n) : M → Type _)] in
theorem contMDiffAt_mlieBracket_smooth
    {X Y : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x) :
    ContMDiffAt (model n) (model n).tangent ∞ (T% (VectorField.mlieBracket (model n) X Y)) x := by
  let : IsManifold (model n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (model n) 2 M)
  let : IsManifold (model n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (model n) ∞ M)
  exact hX.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hY (by simp)

theorem connection_sub
    {A B : (y : M) → TangentSpace (model n) y} {x : M}
    (hA : ContMDiffAt (model n) (model n).tangent ∞ (T% A) x)
    (hB : ContMDiffAt (model n) (model n).tangent ∞ (T% B) x) :
    connection n M (A - B) x = connection n M A x - connection n M B x := by
  have hc := (connection n M).isCovariantDerivativeOnUniv
  have hneg : connection n M (-B) x = -connection n M B x := by
    simpa only [neg_one_smul] using hc.smul_const (-1 : ℝ) (hB.mdifferentiableAt (by simp))
  simpa only [sub_eq_add_neg, hneg] using
    hc.add (hA.mdifferentiableAt (by simp)) (hB.neg_section.mdifferentiableAt (by simp))

theorem connection_bracket
    (X : (y : M) → TangentSpace (model n) y)
    {Y Z : (y : M) → TangentSpace (model n) y} {x : M}
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x) :
    connection n M (VectorField.mlieBracket (model n) Y Z) x (X x) =
      connection n M (fun y ↦ connection n M Z y (Y y)) x (X x) -
        connection n M (fun y ↦ connection n M Y y (Z y)) x (X x) := by
  let A := fun y ↦ connection n M Z y (Y y)
  let B := fun y ↦ connection n M Y y (Z y)
  have hA := contMDiffAt_connection_apply n M hY hZ
  have hB := contMDiffAt_connection_apply n M hZ hY
  have heq : ∀ᶠ y in 𝓝 x, VectorField.mlieBracket (model n) Y Z y = A y - B y := by
    filter_upwards [eventually_mdifferentiableAt_field n M hY,
      eventually_mdifferentiableAt_field n M hZ] with y hyy hzy
    exact (connection_torsion_apply n M hyy hzy).symm
  have hc := (connection n M).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((contMDiffAt_mlieBracket_smooth n M hY hZ).mdifferentiableAt (by simp))
    ((hA.sub_section hB).mdifferentiableAt (by simp)) Filter.univ_mem heq
  calc
    _ = connection n M (A - B) x (X x) :=
      congrArg (fun L : TangentSpace (model n) x →L[ℝ] TangentSpace (model n) x ↦ L (X x)) hc
    _ = _ := by rw [connection_sub n M hA hB]; rfl

theorem curvatureOnFields_first_bianchi
    {X Y Z : (y : M) → TangentSpace (model n) y} {x : M}
    (hX : ContMDiffAt (model n) (model n).tangent ∞ (T% X) x)
    (hY : ContMDiffAt (model n) (model n).tangent ∞ (T% Y) x)
    (hZ : ContMDiffAt (model n) (model n).tangent ∞ (T% Z) x) :
    curvatureOnFields n M X Y Z x + curvatureOnFields n M Y Z X x +
      curvatureOnFields n M Z X Y x = 0 := by
  let : IsManifold (model n) (minSmoothness ℝ 3) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (model n) 3 M)
  have hXY := contMDiffAt_mlieBracket_smooth n M hX hY
  have hYZ := contMDiffAt_mlieBracket_smooth n M hY hZ
  have hZX := contMDiffAt_mlieBracket_smooth n M hZ hX
  have hXZ := contMDiffAt_mlieBracket_smooth n M hX hZ
  calc
    _ = (connection n M (VectorField.mlieBracket (model n) Y Z) x (X x) -
          connection n M X x (VectorField.mlieBracket (model n) Y Z x)) +
        (connection n M (VectorField.mlieBracket (model n) Z X) x (Y x) -
          connection n M Y x (VectorField.mlieBracket (model n) Z X x)) +
        (connection n M (VectorField.mlieBracket (model n) X Y) x (Z x) -
          connection n M Z x (VectorField.mlieBracket (model n) X Y x)) := by
      rw [connection_bracket n M X hY hZ, connection_bracket n M Y hZ hX,
        connection_bracket n M Z hX hY]
      unfold curvatureOnFields
      module
    _ = VectorField.mlieBracket (model n) X (VectorField.mlieBracket (model n) Y Z) x +
        VectorField.mlieBracket (model n) Y (VectorField.mlieBracket (model n) Z X) x +
        VectorField.mlieBracket (model n) Z (VectorField.mlieBracket (model n) X Y) x := by
      rw [connection_torsion_apply n M (hX.mdifferentiableAt (by simp)) (hYZ.mdifferentiableAt (by simp)),
        connection_torsion_apply n M (hY.mdifferentiableAt (by simp)) (hZX.mdifferentiableAt (by simp)),
        connection_torsion_apply n M (hZ.mdifferentiableAt (by simp)) (hXY.mdifferentiableAt (by simp))]
    _ = 0 := by
      have hJac := VectorField.leibniz_identity_mlieBracket_apply
        (hX.of_le (by simp)) (hY.of_le (by simp)) (hZ.of_le (by simp))
      have hn : VectorField.mlieBracket (model n) Y (VectorField.mlieBracket (model n) Z X) x =
          -VectorField.mlieBracket (model n) Y (VectorField.mlieBracket (model n) X Z) x := by
        rw [VectorField.mlieBracket_swap (V := Z) (W := X)]
        simpa only [neg_one_smul] using VectorField.mlieBracket_const_smul_right
          (V := Y) (c := (-1 : ℝ)) (hXZ.mdifferentiableAt (by simp))
      rw [hJac, hn, VectorField.mlieBracket_swap (V := Z) (W := VectorField.mlieBracket (model n) X Y)]
      simp only [Pi.neg_apply]
      module

theorem curvature_first_bianchi (x : M) (u v w : TangentSpace (model n) x) :
    curvature n M x u v w + curvature n M x v w u + curvature n M x w u v = 0 := by
  have h := curvatureOnFields_first_bianchi n M
    (X := extend (Model n) (x := x) u) (Y := extend (Model n) (x := x) v)
    (Z := extend (Model n) (x := x) w)
    (contMDiffAt_extend ..) (contMDiffAt_extend ..) (contMDiffAt_extend ..)
  simpa only [← curvature_eq_curvatureOnFields_extend] using h


/-- The frame indices of the actual curvature components are skew-symmetric. -/
theorem curvatureComponents_swap_frame (x : M) (a b i j : Fin (2 * n)) :
    curvatureComponents n M x a b i j = -curvatureComponents n M x b a i j := by
  have h := curvature_inner_skew n M x (orthonormalFrame n M x i)
    (orthonormalFrame n M x j) (orthonormalFrame n M x b) (orthonormalFrame n M x a)
  rw [← real_inner_comm (orthonormalFrame n M x b)] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The direction indices of the actual curvature components are skew-symmetric. -/
theorem curvatureComponents_swap_directions (x : M) (a b i j : Fin (2 * n)) :
    curvatureComponents n M x a b i j = -curvatureComponents n M x a b j i := by
  unfold curvatureComponents
  rw [curvature_swap, inner_neg_left]

end GaussBonnetChern

