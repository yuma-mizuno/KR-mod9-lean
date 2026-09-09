import KanadeRussell.Straightening.FockOrdering
import KanadeRussell.Straightening.SourceTriples
import KanadeRussell.Straightening.NormalizeAdjacent
import KanadeRussell.Straightening.NormalizeRepeated
set_option backward.isDefEq.respectTransparency false

/-! The remaining local inputs for the concrete minimum-two Fock count bound. -/
namespace KanadeRussell.Straightening
open Tsuchioka PowerSeries
variable {K : Type*} [Field K] [CharZero K]

/-- F4 needs only its adjacent expansion; ordering and the gap-two expansion are concrete. -/
theorem fock_f4_of_adjacent (w : K) (hw : w^4-w^2+1=0) (a : ℤ)
    (adjacent : PairExpansion (Fock.highestWeightAction w) a (a+1) (adjacentCoeff w)) :
    (Fock.highestWeightAction w).LocalReduction [a,a,a] :=
  f4_of_source_expansions _ w hw a adjacent (fock_gapTwo_expansion w hw a)
    (Fock.local_ordering_reduction w hw)

/-- Only the repeated and adjacent expansions remain as local hypotheses here.
The minimum-two initial condition, F1, and the gap-two expansion are proved. -/
theorem fock_finrank_le_count_of_pair_expansions (w : K) (hw : w^4-w^2+1=0) (n : ℕ)
    (repeated : ∀ a : ℤ, a%3 ≠ 0 →
      PairExpansion (Fock.highestWeightAction w) a a (repeatedCoeff w))
    (adjacent : ∀ a : ℤ, (2*a+1)%3 ≠ 0 →
      PairExpansion (Fock.highestWeightAction w) a (a+1) (adjacentCoeff w)) :
    Module.finrank K (Partitions.cyclicGrade (Fock.highestWeightAction w) n) ≤ Partitions.count 2 n :=
  finrank_le_count_of_source_expansions _ w hw 2 n (by omega)
    (Fock.local_ordering_reduction w hw) (fun a _ => fock_gapTwo_expansion w hw a)
    repeated adjacent (Fock.initial_reduction w)

/-- A version whose local hypotheses are unnormalized source combinations. -/
theorem fock_finrank_le_count_of_combined_relations (w : K) (hw : w^4-w^2+1=0) (n : ℕ)
    (repeated : ∀ a : ℤ, a%3 ≠ 0 → ∀ t, ∃ N : ℕ,
      symmetricSum (fun u => (Fock.highestWeightAction w).wordValue (u ++ t))
        (fun p => coeff p (Scalar.G w 1)) a a (N+2) -
      (Coefficients.tCoeff w/Coefficients.mCoeff w) •
        symmetricSum (fun u => (Fock.highestWeightAction w).wordValue (u ++ t))
          (fun p => coeff p (Scalar.G w 2)) a a (N+2) ∈
      shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,a])
    (adjacent : ∀ a : ℤ, (2*a+1)%3 ≠ 0 → ∀ t,
      adjacentCombination (Fock.highestWeightAction w) w a t ∈
      shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,a+1]) :
    Module.finrank K (Partitions.cyclicGrade (Fock.highestWeightAction w) n) ≤ Partitions.count 2 n :=
  fock_finrank_le_count_of_pair_expansions w hw n
    (fun a ha => repeated_expansion_of_combined_relation _ w hw a (repeated a ha))
    (fun a ha => adjacent_expansion_of_combined_relation _ w hw a (adjacent a ha))

end KanadeRussell.Straightening
