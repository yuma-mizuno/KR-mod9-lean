import KanadeRussell.Tsuchioka.PartialModeRelations
import KanadeRussell.Tsuchioka.ConcreteOrdering
import KanadeRussell.Tsuchioka.SourceReductions

/-! All three forbidden-pair reductions for the constructed Fock modes. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

theorem G3_relation_higher_remainder (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (hab : ¬3 ∣ a + b) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      symmetricSum (fun v => (highestWeightAction w).wordValue (v ++ t))
          (fun p => PowerSeries.coeff p (Scalar.G w 2)) a b (M + 1) -
        (Coefficients.mCoeff w * (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) / 12) •
          secondRootMode w (a + b) ((highestWeightAction w).wordValue t) ∈
        higherSpan (K := K) (fun v => (highestWeightAction w).wordValue (v ++ t)) [a, b] := by
  obtain ⟨N, hN⟩ := G3_anticommutator_word_finite w hw a b hab t
  refine ⟨N, ?_⟩
  intro M hM
  rw [hN M hM]
  let S := higherSpan (K := K) (fun v => (highestWeightAction w).wordValue (v ++ t)) [a, b]
  have hz := central_pair_mem w a b t (Scalar.bCoeff w * (-1 : K) ^ a / 48)
  have hm := S.smul_mem ((-1 : K) ^ (a + b)) (mode_pair_sum_mem w a b t)
  convert S.add_mem hz hm using 1
  module

theorem G23_relation_higher_remainder (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (hab : ¬3 ∣ a + b) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      symmetricSum (fun v => (highestWeightAction w).wordValue (v ++ t))
          (fun p => PowerSeries.coeff p (Scalar.G w 1)) a b (M + 1) -
        (Coefficients.tCoeff w / Coefficients.mCoeff w) •
          symmetricSum (fun v => (highestWeightAction w).wordValue (v ++ t))
            (fun p => PowerSeries.coeff p (Scalar.G w 2)) a b (M + 1) ∈
        higherSpan (K := K) (fun v => (highestWeightAction w).wordValue (v ++ t)) [a, b] := by
  obtain ⟨N₂, h₂⟩ := G2_relation_higher_remainder w hw a b t
  obtain ⟨N₃, h₃⟩ := G3_relation_higher_remainder w hw a b hab t
  refine ⟨max N₂ N₃, ?_⟩
  intro M hM
  let S := higherSpan (K := K) (fun v => (highestWeightAction w).wordValue (v ++ t)) [a, b]
  have hc : (Coefficients.tCoeff w / Coefficients.mCoeff w) *
        (Coefficients.mCoeff w * (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) / 12) =
      symmetricPhase w a b / 12 := by
    calc
      _ = ((Coefficients.tCoeff w / Coefficients.mCoeff w) * Coefficients.mCoeff w) *
          (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) / 12 := by ring
      _ = _ := by
        rw [div_mul_cancel₀ _ (Coefficients.mCoeff_ne_zero w hw)]
        rfl
  have h := S.sub_mem (h₂ M (le_trans (le_max_left _ _) hM))
    (S.smul_mem (Coefficients.tCoeff w / Coefficients.mCoeff w)
      (h₃ M (le_trans (le_max_right _ _) hM)))
  convert h using 1
  simp only [smul_sub, smul_smul, hc]
  abel

theorem G6_relation_higher_remainder (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (hab : ¬3 ∣ a + b) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      skewSum (fun v => (highestWeightAction w).wordValue (v ++ t))
        (fun p => PowerSeries.coeff p (Scalar.G6 w)) a b (M + 1) ∈
        higherSpan (K := K) (fun v => (highestWeightAction w).wordValue (v ++ t)) [a, b] := by
  obtain ⟨N, hN⟩ := G6_commutator_word_finite w hw a b hab t
  refine ⟨N, ?_⟩
  intro M hM
  rw [hN M hM]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (mode_pair_sum_mem w a b t))
    (central_pair_mem w a b t _)

/-- F2, with its total-index condition and all operator premises discharged. -/
theorem local_repeated_reduction (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a : ℤ) (ha : ¬3 ∣ 2 * a) :
    (highestWeightAction w).LocalReduction [a, a] := by
  intro t
  obtain ⟨N, hN⟩ := G23_relation_higher_remainder w hw a a
    (by simpa only [two_mul] using ha) t
  exact repeated_reduction_source_coefficients w hw
    (fun v => (highestWeightAction w).wordValue (v ++ t)) a N N (hN N le_rfl)

/-- F3, using the corrected G6 coefficient and the two proved finite relations. -/
theorem local_adjacent_reduction (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a : ℤ) (ha : ¬3 ∣ 2 * a + 1) :
    (highestWeightAction w).LocalReduction [a, a + 1] := by
  intro t
  have hab : ¬3 ∣ a + (a + 1) := by simpa only [two_mul, add_assoc] using ha
  obtain ⟨N, hN⟩ := G23_relation_higher_remainder w hw a (a + 1) hab t
  obtain ⟨L, hL⟩ := G6_relation_higher_remainder w hw a (a + 1) hab t
  apply adjacent_reduction_source_coefficients w hw
    (fun v => (highestWeightAction w).wordValue (v ++ t)) a N N L
  · simpa only [Nat.add_assoc] using hN (N + 1) (by omega)
  · simpa only [Nat.add_assoc] using hL (L + 1) (by omega)

/-- Every forbidden adjacent pair has a concrete homogeneous local reduction. -/
theorem local_pair_reduction (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (hab : ForbiddenPair a b) :
    (highestWeightAction w).LocalReduction [a, b] := by
  rcases hab with h | ⟨he, h⟩ | ⟨he, h⟩
  · exact local_ordering_reduction w hw a b h
  · subst b
    exact local_repeated_reduction w hw a (by simpa only [Int.dvd_iff_emod_eq_zero] using h)
  · subst b
    exact local_adjacent_reduction w hw a (by simpa only [Int.dvd_iff_emod_eq_zero] using h)

end KanadeRussell.Tsuchioka.Fock
