import GaussBonnetChern.Pfaffian


noncomputable section
open scoped BigOperators
namespace GaussBonnetChern

theorem sum_perm_fin_two {A : Type*} [AddCommMonoid A] (f : Equiv.Perm (Fin 2) → A) :
    ∑ σ, f σ = f 1 + f (Equiv.swap 0 1) := by
  have he : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
    ext σ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hσ : σ 0 = 0 ∨ σ 0 = 1 := by omega
    rcases hσ with hσ | hσ
    · left
      apply Equiv.ext
      intro i
      fin_cases i
      · exact hσ
      · have hn := σ.injective.ne (show (1 : Fin 2) ≠ 0 by decide)
        simp only [hσ] at hn
        have hh : σ 1 = 1 := Fin.ext (by omega)
        exact hh
    · right
      apply Equiv.ext
      intro i
      fin_cases i
      · simpa using hσ
      · have hn := σ.injective.ne (show (1 : Fin 2) ≠ 0 by decide)
        simp only [hσ] at hn
        have hh : σ 1 = 0 := Fin.ext (by omega)
        simpa using hh
  have hn : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro h
    have hh := congrArg (fun σ : Equiv.Perm (Fin 2) ↦ σ 0) h
    simp at hh
  rw [he]
  simp [hn]

theorem eulerScalar_one_of_skew
    (B : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)
    (hframe : ∀ a b i j, B b a i j = -B a b i j)
    (hdir : ∀ a b i j, B a b j i = -B a b i j) :
    eulerScalar 1 B = B 0 1 0 1 / (2 * Real.pi) := by
  have h10 : B 1 0 0 1 = -B 0 1 0 1 := hframe 0 1 0 1
  have h01 : B 0 1 1 0 = -B 0 1 0 1 := hdir 0 1 0 1
  have h11 : B 1 0 1 0 = B 0 1 0 1 := by rw [hframe, h01, neg_neg]
  unfold eulerScalar curvatureContraction
  change (∑ σ : Equiv.Perm (Fin 2), ∑ τ : Equiv.Perm (Fin 2),
    (↑(Equiv.Perm.sign σ) : ℝ) * (↑(Equiv.Perm.sign τ) : ℝ) *
      ∏ k : Fin 1, B (σ (pairFirst k)) (σ (pairSecond k))
        (τ (pairFirst k)) (τ (pairSecond k))) / _ = _
  simp only [sum_perm_fin_two]
  norm_num [pairFirst, pairSecond, h10, h01, h11]
  ring


end GaussBonnetChern

