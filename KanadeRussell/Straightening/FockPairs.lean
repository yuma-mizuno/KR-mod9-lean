import KanadeRussell.Straightening.FockSpanning
import KanadeRussell.Tsuchioka.PartialModeRelations
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-! Concrete repeated and adjacent expansions, and the minimum-two count bound. -/
namespace KanadeRussell.Straightening
open Tsuchioka PowerSeries
variable {K : Type*} [Field K] [CharZero K]

theorem fock_G3_shorter_remainder (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (hab : ¬3 ∣ a+b) (t : Word) :
    pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 2)) a b t +
      pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 2)) b a t -
      (Coefficients.mCoeff w*(w^(4*a+9*b)+w^(9*a+4*b))/12) •
        Fock.secondRootMode w (a+b) ((Fock.highestWeightAction w).wordValue t) ∈
      shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b] := by
  rw [fock_pairSum_eq_convolution, fock_pairSum_eq_convolution, Fock.G3_anticommutator w hw _ a b hab]
  let S := shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b]
  have hz := fock_central_shorter w a b t (Scalar.bCoeff w*(-1:K)^a/48)
  have hm := S.smul_mem ((-1:K)^(a+b)) (fock_mode_shorter w a b t)
  convert S.add_mem hz hm using 1
  module

theorem fock_G6_shorter (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (hab : ¬3 ∣ a+b) (t : Word) :
    pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G6 w)) a b t -
      pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G6 w)) b a t ∈
      shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b] := by
  rw [fock_pairSum_eq_convolution, fock_pairSum_eq_convolution, Fock.G6_commutator w hw _ a b hab]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (fock_mode_shorter w a b t))
    (fock_central_shorter w a b t _)

theorem fock_G2_G3_shorter (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (hab : ¬3 ∣ a+b) (t : Word) :
    pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 1)) a b t +
      pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 1)) b a t -
      (Coefficients.tCoeff w/Coefficients.mCoeff w) •
        (pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 2)) a b t +
         pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 2)) b a t) ∈
      shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b] := by
  let S := shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b]
  have h2 := fock_G2_shorter_remainder w hw a b t
  have h3 := S.smul_mem (Coefficients.tCoeff w/Coefficients.mCoeff w)
    (fock_G3_shorter_remainder w hw a b hab t)
  have hc : (Coefficients.tCoeff w/Coefficients.mCoeff w) *
      (Coefficients.mCoeff w*(w^(4*a+9*b)+w^(9*a+4*b))/12) = symmetricPhase w a b/12 := by
    have hr := div_mul_cancel₀ (Coefficients.tCoeff w) (Coefficients.mCoeff_ne_zero w hw)
    change _ = Coefficients.tCoeff w*(w^(4*a+9*b)+w^(9*a+4*b))/12
    linear_combination ((w^(4*a+9*b)+w^(9*a+4*b))/12)*hr
  have he : (pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 1)) a b t +
      pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 1)) b a t -
      (symmetricPhase w a b/12) • Fock.secondRootMode w (a+b) ((Fock.highestWeightAction w).wordValue t)) -
      (Coefficients.tCoeff w/Coefficients.mCoeff w) •
        (pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 2)) a b t +
         pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 2)) b a t -
         (Coefficients.mCoeff w*(w^(4*a+9*b)+w^(9*a+4*b))/12) •
           Fock.secondRootMode w (a+b) ((Fock.highestWeightAction w).wordValue t)) =
      pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 1)) a b t +
      pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 1)) b a t -
      (Coefficients.tCoeff w/Coefficients.mCoeff w) •
        (pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 2)) a b t +
         pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 2)) b a t) := by
    rw [smul_sub, smul_smul, hc]
    abel
  rw [← he]
  exact S.sub_mem h2 h3

theorem fock_repeated_expansion (w : K) (hw : w^4-w^2+1=0)
    (a : ℤ) (ha : a%3 ≠ 0) :
    PairExpansion (Fock.highestWeightAction w) a a (repeatedCoeff w) := by
  apply repeated_expansion_of_combined_relation _ w hw a
  intro t
  have hab : ¬3 ∣ a+a := by omega
  have hh := fock_G2_G3_shorter w hw a a hab t
  obtain ⟨N,hN⟩ := pair_tails_zero (Fock.highestWeightAction w) a a t
  refine ⟨N, ?_⟩
  simp only [pairSum_eq_sum _ _ a a t (N+2) (fun p hp => (hN p (by omega)).1)] at hh
  simpa only [symmetricSum, smul_add, Finset.sum_add_distrib] using hh

theorem fock_adjacent_expansion (w : K) (hw : w^4-w^2+1=0)
    (a : ℤ) (ha : (2*a+1)%3 ≠ 0) :
    PairExpansion (Fock.highestWeightAction w) a (a+1) (adjacentCoeff w) := by
  apply adjacent_expansion_of_combined_relation _ w hw a
  intro t
  have hab : ¬3 ∣ a+(a+1) := by omega
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (fock_G2_G3_shorter w hw a (a+1) hab t))
    (Submodule.smul_mem _ _ (fock_G6_shorter w hw a (a+1) hab t))

/-- Every forbidden triple reduces for the constructed Fock action. -/
theorem fock_forbiddenTriples (w : K) (hw : w^4-w^2+1=0) :
    ∀ a b c, ForbiddenTriple a b c → (Fock.highestWeightAction w).LocalReduction [a,b,c] :=
  forbiddenTriples_of_source_expansions _ w hw (Fock.local_ordering_reduction w hw)
    (fun a _ => fock_gapTwo_expansion w hw a) (fock_repeated_expansion w hw) (fock_adjacent_expansion w hw)

/-- The cyclic grade has the admissible minimum-two partition count as an upper bound.
No character formula or product lower bound is asserted here. -/
theorem fock_finrank_le_count (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.finrank K (Partitions.cyclicGrade (Fock.highestWeightAction w) n) ≤ Partitions.count 2 n :=
  fock_finrank_le_count_of_pair_expansions w hw n (fock_repeated_expansion w hw) (fock_adjacent_expansion w hw)

theorem fock_cyclicGrade_eq_span_normal (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Partitions.cyclicGrade (Fock.highestWeightAction w) n = Submodule.span K
      (Set.range (fun u : Partitions.NormalWords 2 n => (Fock.highestWeightAction w).wordValue u.val)) :=
  Partitions.cyclicGrade_eq_span_normal _ 2 n
    (forbiddenPairs_of_source_expansions _ w (Fock.local_ordering_reduction w hw)
      (fock_repeated_expansion w hw) (fock_adjacent_expansion w hw))
    (fock_forbiddenTriples w hw) (Fock.initial_reduction w)

theorem fock_cyclicGrade_finite (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.Finite K (Partitions.cyclicGrade (Fock.highestWeightAction w) n) :=
  Partitions.cyclicGrade_finite _ 2 n (by omega)
    (forbiddenPairs_of_source_expansions _ w (Fock.local_ordering_reduction w hw)
      (fock_repeated_expansion w hw) (fock_adjacent_expansion w hw))
    (fock_forbiddenTriples w hw) (Fock.initial_reduction w)

end KanadeRussell.Straightening
