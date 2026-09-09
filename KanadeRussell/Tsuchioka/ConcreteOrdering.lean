import KanadeRussell.Tsuchioka.G1Commutator
import KanadeRussell.Tsuchioka.SourceCoefficients

/-! The concrete F1 ordering reduction, including its exceptional residue class. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

theorem mode_pair_sum_mem (w : K) (a b : ℤ) (t : Word) :
    mode w (a + b) ((highestWeightAction w).wordValue t) ∈
      higherSpan (K := K) (fun v => (highestWeightAction w).wordValue (v ++ t)) [a, b] := by
  change (highestWeightAction w).wordValue ([a + b] ++ t) ∈ _
  exact mem_higherSpan _ (Or.inl (by simp)) (by simp)

theorem central_pair_mem (w : K) (a b : ℤ) (t : Word) (c : K) :
    (if a + b = 0 then c • (highestWeightAction w).wordValue t else 0) ∈
      higherSpan (K := K) (fun v => (highestWeightAction w).wordValue (v ++ t)) [a, b] := by
  by_cases hab : a + b = 0
  · rw [if_pos hab]
    apply Submodule.smul_mem
    change (highestWeightAction w).wordValue ([] ++ t) ∈ _
    exact mem_higherSpan _ (Or.inl (by simp)) (by simpa using hab.symm)
  · rw [if_neg hab]
    exact Submodule.zero_mem _

/-- The first commutator leaves only shorter words after its second-root term
is removed, also when applied at shifted indices of the same total. -/
theorem G1_relation_higher_remainder (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b c d : ℤ) (hcd : c + d = a + b) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      skewSum (fun v => (highestWeightAction w).wordValue (v ++ t))
          (fun p => PowerSeries.coeff p (Scalar.G w 0)) c d (M + 1) -
        (skewPhase w c d / 12) • secondRootMode w (a + b) ((highestWeightAction w).wordValue t) ∈
        higherSpan (K := K) (fun v => (highestWeightAction w).wordValue (v ++ t)) [a, b] := by
  obtain ⟨N, hN⟩ := G1_commutator_word_finite w hw c d t
  refine ⟨N, ?_⟩
  intro M hM
  rw [hN M hM, hcd]
  let S := higherSpan (K := K) (fun v => (highestWeightAction w).wordValue (v ++ t)) [a, b]
  have hf := S.smul_mem
    (Coefficients.pCoeff w * (w ^ (-2 * c + 2 * d) - w ^ (2 * c - 2 * d)) / 12)
    (mode_pair_sum_mem w a b t)
  have hz := central_pair_mem w a b t (Scalar.cPrime w * (c : K) * (-1 : K) ^ c / 24)
  convert S.add_mem hf hz using 1
  simp only [skewPhase, Scalar.rootSecondResidue]
  module

theorem G2_relation_higher_remainder (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      symmetricSum (fun v => (highestWeightAction w).wordValue (v ++ t))
          (fun p => PowerSeries.coeff p (Scalar.G w 1)) a b (M + 1) -
        (symmetricPhase w a b / 12) •
          secondRootMode w (a + b) ((highestWeightAction w).wordValue t) ∈
        higherSpan (K := K) (fun v => (highestWeightAction w).wordValue (v ++ t)) [a, b] := by
  obtain ⟨N, hN⟩ := G2_anticommutator_word_finite w hw a b t
  refine ⟨N, ?_⟩
  intro M hM
  rw [hN M hM]
  let S := higherSpan (K := K) (fun v => (highestWeightAction w).wordValue (v ++ t)) [a, b]
  have hm := mode_pair_sum_mem w a b t
  have hf := S.smul_mem
    (Scalar.aPrime w * (w ^ (-2 * a + 2 * b) + w ^ (2 * a - 2 * b)) / 12) hm
  have hz := central_pair_mem w a b t (Scalar.cPrime w * (-1 : K) ^ a / 48)
  have ht := S.smul_mem ((-1 : K) ^ (a + b) / 3) hm
  convert S.add_mem (S.add_mem hf hz) ht using 1
  simp only [symmetricPhase, Coefficients.tCoeff]
  module

/-- F1 for the constructed modes on every suffix vector. Both source relations
and the shifted exceptional relation have concrete finite proofs. -/
theorem local_ordering_reduction (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (hab : b < a) :
    (highestWeightAction w).LocalReduction [a, b] := by
  intro t
  obtain ⟨N, hN⟩ := G1_relation_higher_remainder w hw a b a b rfl t
  obtain ⟨M, hM⟩ := G2_relation_higher_remainder w hw a b t
  obtain ⟨L, hL⟩ := G1_relation_higher_remainder w hw a b (a - 1) (b + 1) (by ring) t
  exact ordering_reduction_of_relations w hw
    (fun v => (highestWeightAction w).wordValue (v ++ t)) _ _
    (Scalar.coeff_zero_G w 0) (Scalar.coeff_zero_G w 1) a b hab N M (L + 1)
    (secondRootMode w (a + b) ((highestWeightAction w).wordValue t))
    (hN N le_rfl) (hM M le_rfl) (hL L le_rfl)

end KanadeRussell.Tsuchioka.Fock
