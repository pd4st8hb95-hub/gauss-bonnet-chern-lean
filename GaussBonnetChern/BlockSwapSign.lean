import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity

/-! # Sign of the block permutation used by the exterior product

The formula is symbolic in both block sizes, including empty blocks. It supplies
the exact `(-1)^(k*l)` factor in graded commutativity.
-/

noncomputable section

namespace GaussBonnetChern.DifferentialForm

def blockSwapPerm (k l : ℕ) : Equiv.Perm (Fin (k + l)) :=
  (finAddFlip : Fin (k + l) ≃ Fin (l + k)).trans (finCongr (Nat.add_comm l k))

theorem sign_blockSwapPerm (k l : ℕ) :
    Equiv.Perm.sign (blockSwapPerm k l) = (-1) ^ (k * l) := by
  by_cases hk : k = 0
  · subst k
    have heq : blockSwapPerm 0 l = 1 := by
      ext i
      simp [blockSwapPerm, finAddFlip_apply_mk_right (Nat.zero_le i.val) i.isLt]
    simp [heq]
  have hlN : l < k + l := by omega
  haveI : NeZero (k + l) := ⟨by omega⟩
  let c : Fin (k + l) := ⟨l, hlN⟩
  have hcycle : blockSwapPerm k l = finCycle c := by
    ext i
    by_cases hi : (i : ℕ) < k
    · simp [blockSwapPerm, finAddFlip_apply_mk_left hi, finCycle_apply, c,
        Fin.add_def, Nat.mod_eq_of_lt (show i.val + l < k + l by omega),
        Nat.mod_eq_of_lt (show l + i.val < k + l by omega), Nat.add_comm]
    · have hki : k ≤ i.val := by omega
      have hmod : (i.val + l) % (k + l) = i.val - k := by
        have heq : i.val + l = (k + l) + (i.val - k) := by omega
        rw [heq, Nat.add_mod]
        simp [Nat.mod_eq_of_lt (show i.val - k < k + l by omega)]
      simp [blockSwapPerm, finAddFlip_apply_mk_right hki i.isLt, finCycle_apply, c,
        Fin.add_def, hmod]
  have hpow : blockSwapPerm k l = (finRotate (k + l)) ^ l := by
    ext i
    rw [hcycle, Equiv.Perm.coe_pow]
    exact congrArg (fun f : Fin (k + l) → Fin (k + l) ↦ (f i).val)
      (finCycle_eq_finRotate_iterate (k := c))
  rw [hpow, map_pow, sign_finRotate, ← pow_mul]
  by_cases hl : l = 0
  · simp [hl]
  have hle : 1 ≤ l := by omega
  have heq : (k + l - 1) * l = k * l + l * (l - 1) := by
    rw [Nat.add_sub_assoc hle, Nat.add_mul]
    ring
  rw [heq, pow_add, (Nat.even_mul_pred_self l).neg_one_pow, mul_one]

end GaussBonnetChern.DifferentialForm
