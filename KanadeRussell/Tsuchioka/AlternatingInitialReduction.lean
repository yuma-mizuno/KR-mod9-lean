import KanadeRussell.Tsuchioka.AlternatingGrading
import KanadeRussell.Tsuchioka.AlternatingInitialModes
import KanadeRussell.Tsuchioka.AlternatingVacuumModes
import KanadeRussell.Tsuchioka.AffineAlternatingHighestWeight

/-! The concrete alternating highest-weight action satisfies the initial
condition for minimum part three in the existing straightening theorem. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KanadeRussell.Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

theorem alternating_wordValue_val (w : K) (u : Word) :
    ((alternatingHighestWeightAction w).wordValue u).val =
      (highestWeightAction w).wordOperator u (alternatingSeed (K := K)) := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    change mode w i ((alternatingHighestWeightAction w).wordValue u).val =
      mode w i ((highestWeightAction w).wordOperator u alternatingSeed)
    rw [ih]

theorem mode_zero_alternatingSeed (w : K) (hw : w^4-w^2+1=0) :
    mode w 0 (alternatingSeed (K := K)) = (-w^3/2+w+3/4) • alternatingSeed := by
  have h := rootMode_zero_alternatingSeed w hw (RootData.simpleRoot 0)
  rw [rootMode_first, tensorFirstRoot_zero_alternatingSeed w hw] at h
  exact h

theorem mode_alternatingSeed_pos (w : K) (i : ℤ) (hi : 0 < i) :
    mode w i (alternatingSeed (K := K)) = 0 := by
  have h := (alternatingHighestWeightAction w).mode_mem i 0
    (alternatingHighestWeightAction w).vacuum (alternatingHighestWeightAction w).vacuum_mem
  rw [(alternatingHighestWeightAction w).negative (0-i) (by omega), Submodule.mem_bot] at h
  exact congrArg Subtype.val h

/-- Every forbidden final part below three reduces to a shorter word or zero. -/
theorem alternating_initial_reduction (w : K) (hw : w^4-w^2+1=0) (i : ℤ) (hi : -3 < i) :
    (alternatingHighestWeightAction w).wordValue [i] ∈
      higherSpan (K := K) (alternatingHighestWeightAction w).wordValue [i] := by
  by_cases hpos : 0 < i
  · have hz : (alternatingHighestWeightAction w).wordValue [i] = 0 := by
      apply Subtype.ext
      exact mode_alternatingSeed_pos w i hpos
    rw [hz]
    exact Submodule.zero_mem _
  have hc : i = -2 ∨ i = -1 ∨ i = 0 := by omega
  rcases hc with rfl | rfl | rfl
  · have hz : (alternatingHighestWeightAction w).wordValue [-2] = 0 := by
      apply Subtype.ext
      exact mode_neg_two_alternatingSeed w hw
    rw [hz]
    exact Submodule.zero_mem _
  · have hz : (alternatingHighestWeightAction w).wordValue [-1] = 0 := by
      apply Subtype.ext
      exact mode_neg_one_alternatingSeed w hw
    rw [hz]
    exact Submodule.zero_mem _
  · have he : (alternatingHighestWeightAction w).wordValue [] ∈
        higherSpan (K := K) (alternatingHighestWeightAction w).wordValue [0] :=
      mem_higherSpan _ (Or.inl (by simp)) (by simp)
    have hs := (higherSpan (K := K) (alternatingHighestWeightAction w).wordValue [0]).smul_mem
      (-w^3/2+w+3/4) he
    have hv : (alternatingHighestWeightAction w).wordValue [0] =
        (-w^3/2+w+3/4) • (alternatingHighestWeightAction w).wordValue [] := by
      apply Subtype.ext
      exact mode_zero_alternatingSeed w hw
    rw [hv]
    exact hs

end KanadeRussell.Tsuchioka.Fock
