import KanadeRussell.Straightening.FinitePairs
import KanadeRussell.Straightening.PairCoefficients
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-! Normalization of the ordering relation with exact reversed-tail reindexing. -/
namespace KanadeRussell.Straightening
open Tsuchioka PowerSeries
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem ordering_combination_eq (ρ : HighestWeightAction K V) (w : K)
    (hw : w^4-w^2+1 = 0) (a b : ℤ) (hab : b ≤ a) (hne : (a-b)%12 ≠ 7) (t : Word) :
    symmetricPhase w a b •
      (pairSum ρ (fun p => coeff p (Scalar.G w 0)) a b t -
       pairSum ρ (fun p => coeff p (Scalar.G w 0)) b a t) -
    skewPhase w a b •
      (pairSum ρ (fun p => coeff p (Scalar.G w 1)) a b t +
       pairSum ρ (fun p => coeff p (Scalar.G w 1)) b a t) =
    (symmetricPhase w a b-skewPhase w a b) • pairSum ρ (orderingCoeff w a b) a b t := by
  rw [pairSum_reverse ρ (fun p => coeff p (Scalar.G w 0)) a b hab t,
    pairSum_reverse ρ (fun p => coeff p (Scalar.G w 1)) a b hab t]
  simp only [← pairSum_sub, ← pairSum_add, ← pairSum_smul]
  apply congrArg (fun c => pairSum ρ c a b t)
  funext n
  have hh := div_mul_cancel₀
    (symmetricPhase w a b*coeff n (Scalar.G w 0) - skewPhase w a b*coeff n (Scalar.G w 1) -
      if (a-b).toNat ≤ n then
        symmetricPhase w a b*coeff (n-(a-b).toNat) (Scalar.G w 0) +
          skewPhase w a b*coeff (n-(a-b).toNat) (Scalar.G w 1) else 0)
    (ordering_denominator_ne_zero w hw a b hne)
  unfold orderingCoeff
  split_ifs at hh ⊢ <;> linear_combination -hh

theorem ordering_expansion_of_combined_relation (ρ : HighestWeightAction K V) (w : K)
    (hw : w^4-w^2+1 = 0) (a b : ℤ) (hab : b < a) (hne : (a-b)%12 ≠ 7)
    (h : ∀ t,
      symmetricPhase w a b •
        (pairSum ρ (fun p => coeff p (Scalar.G w 0)) a b t -
         pairSum ρ (fun p => coeff p (Scalar.G w 0)) b a t) -
      skewPhase w a b •
        (pairSum ρ (fun p => coeff p (Scalar.G w 1)) a b t +
         pairSum ρ (fun p => coeff p (Scalar.G w 1)) b a t) ∈
      shorterSpan (K := K) (fun u => ρ.wordValue (u ++ t)) [a,b]) :
    PairExpansion ρ a b (orderingCoeff w a b) := by
  apply pairExpansion_of_pairSum ρ a b _ (orderingCoeff_zero w hw a b hab hne)
  intro t
  have hh := h t
  rw [ordering_combination_eq ρ w hw a b (le_of_lt hab) hne t] at hh
  exact ((shorterSpan (K := K) (fun u => ρ.wordValue (u ++ t)) [a,b]).smul_mem_iff
    (ordering_denominator_ne_zero w hw a b hne)).mp hh

end KanadeRussell.Straightening
