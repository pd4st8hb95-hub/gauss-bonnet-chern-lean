import GaussBonnetChern.ChernAngularRecurrence
import GaussBonnetChern.ChernProductIdentities

noncomputable section
open scoped Manifold BigOperators
open Module
namespace GaussBonnetChern.Chern
open DifferentialForm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section PairFlips

def mixedPairFlip (r k : ℕ) (j : Fin k) : Equiv.Perm (Fin (r+2*k)) :=
  Equiv.swap (Fin.natAdd r (pairFirst j)) (Fin.natAdd r (pairSecond j))

theorem sign_mixedPairFlip (r k : ℕ) (j : Fin k) :
    Equiv.Perm.sign (mixedPairFlip r k j) = -1 := by
  apply Equiv.Perm.sign_swap
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natAdd, pairFirst, pairSecond, Fin.val_mk] at hv
  omega

@[simp] theorem mixedPairFlip_theta (r k : ℕ) (j : Fin k) (i : Fin r) :
    mixedPairFlip r k j (Fin.castAdd (2*k) i) = Fin.castAdd (2*k) i := by
  apply Equiv.swap_apply_of_ne_of_ne <;>
    intro h <;> have hv := congrArg Fin.val h <;>
    simp only [Fin.val_natAdd, Fin.val_castAdd, pairFirst, pairSecond, Fin.val_mk] at hv <;>
    have := i.isLt <;> omega

@[simp] theorem mixedPairFlip_first_self (r k : ℕ) (j : Fin k) :
    mixedPairFlip r k j (Fin.natAdd r (pairFirst j)) = Fin.natAdd r (pairSecond j) :=
  Equiv.swap_apply_left _ _

@[simp] theorem mixedPairFlip_second_self (r k : ℕ) (j : Fin k) :
    mixedPairFlip r k j (Fin.natAdd r (pairSecond j)) = Fin.natAdd r (pairFirst j) :=
  Equiv.swap_apply_right _ _

theorem mixedPairFlip_first_other (r k : ℕ) (i j : Fin k) (hij : i ≠ j) :
    mixedPairFlip r k j (Fin.natAdd r (pairFirst i)) = Fin.natAdd r (pairFirst i) := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, pairFirst, Fin.val_mk] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, pairFirst, pairSecond, Fin.val_mk] at hv
    omega

theorem mixedPairFlip_second_other (r k : ℕ) (i j : Fin k) (hij : i ≠ j) :
    mixedPairFlip r k j (Fin.natAdd r (pairSecond i)) = Fin.natAdd r (pairSecond i) := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, pairFirst, pairSecond, Fin.val_mk] at hv
    omega
  · intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, pairSecond, Fin.val_mk] at hv
    omega

end PairFlips

section ActualContraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem mixedMultilinear_curvaturePair_symmetry (r k : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2) (σ : Equiv.Perm (Fin k)) :
    (mixedMultilinear r k Θ B).domDomCongr (mixedCurvaturePerm r k σ) =
      mixedMultilinear r k Θ B := by
  apply MultilinearMap.ext
  intro w
  rw [MultilinearMap.domDomCongr_apply, mixedMultilinear_apply, mixedMultilinear_apply]
  have ht : (fun i : Fin r ↦ Θ (w (mixedCurvaturePerm r k σ (Fin.castAdd (2*k) i)))) =
      (fun i : Fin r ↦ Θ (w (Fin.castAdd (2*k) i))) := by
    funext i
    exact congrArg (fun t ↦ Θ (w t)) (mixedCurvaturePerm_theta r k σ i)
  have hc : (fun j : Fin k ↦ B (w (mixedCurvaturePerm r k σ (Fin.natAdd r (pairFirst j))))
      (w (mixedCurvaturePerm r k σ (Fin.natAdd r (pairSecond j))))) =
      (fun j : Fin k ↦ B (w (Fin.natAdd r (pairFirst (σ j))))
        (w (Fin.natAdd r (pairSecond (σ j))))) := by
    funext j
    exact congrArg₂ (fun s t ↦ B (w s) (w t))
      (mixedCurvaturePerm_first r k σ j) (mixedCurvaturePerm_second r k σ j)
  change wedge (oneFormProduct r (fun i ↦ Θ (w (mixedCurvaturePerm r k σ (Fin.castAdd (2*k) i)))))
    (twoFormProduct k (fun j ↦ B (w (mixedCurvaturePerm r k σ (Fin.natAdd r (pairFirst j))))
      (w (mixedCurvaturePerm r k σ (Fin.natAdd r (pairSecond j)))))) = _
  rw [ht, hc]
  exact congrArg (wedge (oneFormProduct r (fun i ↦ Θ (w (Fin.castAdd (2*k) i)))))
    (twoFormProduct_perm k
      (fun j ↦ B (w (Fin.natAdd r (pairFirst j))) (w (Fin.natAdd r (pairSecond j)))) σ)

theorem mixedMultilinear_pairFlip_symmetry (r k : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (hB : ∀ u v, B u v = -B v u) (j : Fin k) :
    (mixedMultilinear r k Θ B).domDomCongr (mixedPairFlip r k j) =
      Equiv.Perm.sign (mixedPairFlip r k j) • mixedMultilinear r k Θ B := by
  apply MultilinearMap.ext
  intro w
  rw [sign_mixedPairFlip]
  simp only [MultilinearMap.domDomCongr_apply, Units.neg_smul, one_smul,
    MultilinearMap.neg_apply]
  change mixedMultilinear r k Θ B (w ∘ mixedPairFlip r k j) = -(mixedMultilinear r k Θ B w)
  rw [mixedMultilinear_apply, mixedMultilinear_apply]
  let C : Fin k → Form 𝓘(ℝ,E) P 2 := fun t ↦
    B (w (Fin.natAdd r (pairFirst t))) (w (Fin.natAdd r (pairSecond t)))
  have ht : (fun i : Fin r ↦ Θ (w (mixedPairFlip r k j (Fin.castAdd (2*k) i)))) =
      (fun i : Fin r ↦ Θ (w (Fin.castAdd (2*k) i))) := by
    funext i
    exact congrArg (fun t ↦ Θ (w t)) (mixedPairFlip_theta r k j i)
  have hc : (fun t : Fin k ↦ B (w (mixedPairFlip r k j (Fin.natAdd r (pairFirst t))))
      (w (mixedPairFlip r k j (Fin.natAdd r (pairSecond t))))) = Function.update C j (-C j) := by
    funext t
    by_cases ht : t = j
    · subst t
      rw [Function.update_self]
      exact (congrArg₂ (fun s t ↦ B (w s) (w t))
        (mixedPairFlip_first_self r k j) (mixedPairFlip_second_self r k j)).trans (hB _ _)
    · rw [Function.update_of_ne ht]
      exact congrArg₂ (fun s t ↦ B (w s) (w t))
        (mixedPairFlip_first_other r k t j ht) (mixedPairFlip_second_other r k t j ht)
  change wedge (oneFormProduct r (fun i ↦ Θ (w (mixedPairFlip r k j (Fin.castAdd (2*k) i)))))
    (twoFormProduct k (fun t ↦ B (w (mixedPairFlip r k j (Fin.natAdd r (pairFirst t))))
      (w (mixedPairFlip r k j (Fin.natAdd r (pairSecond t)))))) =
    -wedge (oneFormProduct r (fun i ↦ Θ (w (Fin.castAdd (2*k) i)))) (twoFormProduct k C)
  rw [ht, hc]
  have hn : twoFormProduct k (Function.update C j (-C j)) = -twoFormProduct k C := by
    rw [← twoFormFactorsMultilinear_apply, ← twoFormFactorsMultilinear_apply]
    rw [MultilinearMap.map_update_neg, Function.update_eq_self]
  rw [hn]
  exact (wedgeLinear r (2*k) _).map_neg _

theorem mixed_insertion_first_eq_first (r k : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (T : W →ₗ[ℝ] W) (i j : Fin k) :
    (slotInsertion (mixedMultilinear r k Θ B) T (Fin.natAdd r (pairFirst i))).alternatization =
      (slotInsertion (mixedMultilinear r k Θ B) T (Fin.natAdd r (pairFirst j))).alternatization := by
  let τ := mixedCurvaturePerm r k (Equiv.swap i j)
  have hf : (mixedMultilinear r k Θ B).domDomCongr τ =
      Equiv.Perm.sign τ • mixedMultilinear r k Θ B := by
    rw [show τ = mixedCurvaturePerm r k (Equiv.swap i j) from rfl,
      sign_mixedCurvaturePerm, one_smul, mixedMultilinear_curvaturePair_symmetry]
  have hi : τ.symm (Fin.natAdd r (pairFirst i)) = Fin.natAdd r (pairFirst j) := by
    apply τ.injective
    rw [τ.apply_symm_apply]
    simp [τ]
  have h := alternatization_slotInsertion_exchange (mixedMultilinear r k Θ B) T
    (Fin.natAdd r (pairFirst i)) τ hf
  rwa [hi] at h

theorem mixed_insertion_first_eq_second (r k : ℕ)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (hB : ∀ u v, B u v = -B v u) (T : W →ₗ[ℝ] W) (j : Fin k) :
    (slotInsertion (mixedMultilinear r k Θ B) T (Fin.natAdd r (pairFirst j))).alternatization =
      (slotInsertion (mixedMultilinear r k Θ B) T (Fin.natAdd r (pairSecond j))).alternatization := by
  let τ := mixedPairFlip r k j
  have hi : τ.symm (Fin.natAdd r (pairFirst j)) = Fin.natAdd r (pairSecond j) := by
    apply τ.injective
    rw [τ.apply_symm_apply]
    exact (mixedPairFlip_second_self r k j).symm
  have h := alternatization_slotInsertion_exchange (mixedMultilinear r k Θ B) T
    (Fin.natAdd r (pairFirst j)) τ (mixedMultilinear_pairFlip_symmetry r k Θ B hB j)
  rwa [hi] at h

/-- The exact curvature-contraction multiplicity in arbitrary symbolic degree.
All hypotheses refer to actual linear form data and the actual fiber at `x`. -/
theorem mixed_curvature_contraction (r k : ℕ) (hk : 0 < k)
    (Θ : W →ₗ[ℝ] Form 𝓘(ℝ,E) P 1)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] Form 𝓘(ℝ,E) P 2)
    (hB : ∀ u v, B u v = -B v u)
    (b : Basis (Fin (r+2*k)) ℝ W) (U : W →ₗ[ℝ] ℝ) (u : W) (x : P)
    (hu : U u = 1) (hΘ : Θ u x = 0) :
    (mixedMultilinear r k Θ B).alternatization b x =
      (2*(k : ℝ)) • (slotInsertion (mixedMultilinear r k Θ B) (U.smulRight u)
        (Fin.natAdd r (pairFirst (⟨0, hk⟩ : Fin k)))).alternatization b x := by
  rw [← mixed_curvature_insertion_sum_at r k Θ B b U u x hu hΘ]
  have hs (t : Fin (2*k)) :
      (slotInsertion (mixedMultilinear r k Θ B) (U.smulRight u) (Fin.natAdd r t)).alternatization =
      (slotInsertion (mixedMultilinear r k Θ B) (U.smulRight u)
        (Fin.natAdd r (pairFirst (⟨0, hk⟩ : Fin k)))).alternatization := by
    obtain ⟨⟨j, a⟩, rfl⟩ := (curvaturePairEquiv k).surjective t
    fin_cases a
    · change (slotInsertion (mixedMultilinear r k Θ B) (U.smulRight u)
        (Fin.natAdd r (curvaturePairEquiv k (j, 0)))).alternatization = _
      rw [curvaturePairEquiv_first]
      exact mixed_insertion_first_eq_first r k Θ B _ j ⟨0,hk⟩
    · change (slotInsertion (mixedMultilinear r k Θ B) (U.smulRight u)
        (Fin.natAdd r (curvaturePairEquiv k (j, 1)))).alternatization = _
      rw [curvaturePairEquiv_second,
        ← mixed_insertion_first_eq_second r k Θ B hB _ j]
      exact mixed_insertion_first_eq_first r k Θ B _ j ⟨0,hk⟩
  simp_rw [hs]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  norm_cast

end ActualContraction
end GaussBonnetChern.Chern




