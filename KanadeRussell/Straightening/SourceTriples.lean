import KanadeRussell.Straightening.TripleOverlap
import KanadeRussell.Straightening.PairCoefficients
import KanadeRussell.Partitions.SpanningBridge
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-! F2--F6 from finite normalized source relations, with no assumed low coefficients. -/
namespace KanadeRussell.Straightening
open Tsuchioka
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem f4_of_source_expansions (ρ : HighestWeightAction K V) (w : K)
    (hw : w^4-w^2+1 = 0) (a : ℤ)
    (hleft : PairExpansion ρ a (a+1) (adjacentCoeff w))
    (hright : PairExpansion ρ (a+1) (a-1) (orderingCoeff w (a+1) (a-1)))
    (ordering : ∀ i j, j < i → ρ.LocalReduction [i,j]) :
    ρ.LocalReduction [a,a,a] :=
  overlap_right ρ a a (by omega) _ _ hleft hright
    (orderingCoeff_one_gap_two_ne_zero w hw _ _ (by omega)) ordering

theorem f5_of_source_expansions (ρ : HighestWeightAction K V) (w : K)
    (hw : w^4-w^2+1 = 0) (a : ℤ)
    (hleft : PairExpansion ρ a (a+1) (adjacentCoeff w))
    (hright : PairExpansion ρ (a+1) (a+1) (repeatedCoeff w))
    (ordering : ∀ i j, j < i → ρ.LocalReduction [i,j]) :
    ρ.LocalReduction [a,a,a+2] := by
  have hh : PairExpansion ρ (a+1) (a+2-1) (repeatedCoeff w) := by
    convert hright using 1; ring
  exact overlap_right ρ a (a+2) (by omega) _ _ hleft hh (repeatedCoeff_one_ne_zero w hw) ordering

theorem f6_of_source_expansions (ρ : HighestWeightAction K V) (w : K)
    (hw : w^4-w^2+1 = 0) (a : ℤ)
    (hleft : PairExpansion ρ (a-1) (a-1) (repeatedCoeff w))
    (hright : PairExpansion ρ (a-1) a (adjacentCoeff w))
    (ordering : ∀ i j, j < i → ρ.LocalReduction [i,j]) :
    ρ.LocalReduction [a-2,a,a] :=
  overlap_left ρ a _ _ hleft hright (repeatedCoeff_one_ne_zero w hw) ordering

theorem forbiddenPairs_of_source_expansions (ρ : HighestWeightAction K V) (w : K)
    (ordering : ∀ i j, j < i → ρ.LocalReduction [i,j])
    (repeated : ∀ a : ℤ, a%3 ≠ 0 → PairExpansion ρ a a (repeatedCoeff w))
    (adjacent : ∀ a : ℤ, (2*a+1)%3 ≠ 0 → PairExpansion ρ a (a+1) (adjacentCoeff w)) :
    ∀ a b, ForbiddenPair a b → ρ.LocalReduction [a,b] := by
  intro a b h
  rcases h with h | ⟨he,hr⟩ | ⟨he,hr⟩
  · exact ordering a b h
  · subst b
    exact (repeated a (by omega)).localReduction
  · subst b
    exact (adjacent a hr).localReduction

theorem forbiddenTriples_of_source_expansions (ρ : HighestWeightAction K V) (w : K)
    (hw : w^4-w^2+1 = 0)
    (ordering : ∀ i j, j < i → ρ.LocalReduction [i,j])
    (gapTwo : ∀ a : ℤ, a%3 = 0 →
      PairExpansion ρ (a+1) (a-1) (orderingCoeff w (a+1) (a-1)))
    (repeated : ∀ a : ℤ, a%3 ≠ 0 → PairExpansion ρ a a (repeatedCoeff w))
    (adjacent : ∀ a : ℤ, (2*a+1)%3 ≠ 0 → PairExpansion ρ a (a+1) (adjacentCoeff w)) :
    ∀ a b c, ForbiddenTriple a b c → ρ.LocalReduction [a,b,c] := by
  intro a b c h
  rcases h with h | h | h
  · rcases h with ⟨hab,hbc,ha⟩
    subst b
    subst c
    exact f4_of_source_expansions ρ w hw a (adjacent a (by omega)) (gapTwo a ha) ordering
  · rcases h with ⟨hab,hac,ha⟩
    subst b
    subst c
    exact f5_of_source_expansions ρ w hw a (adjacent a (by omega))
      (repeated (a+1) (by omega)) ordering
  · rcases h with ⟨hbc,hab,hb⟩
    subst c
    have ha : a = b-2 := by omega
    rw [ha]
    have hh : PairExpansion ρ (b-1) b (adjacentCoeff w) := by
      simpa using adjacent (b-1) (by omega)
    exact f6_of_source_expansions ρ w hw b (repeated (b-1) (by omega)) hh ordering

/-- The source pair expansions suffice for the actual partition-count bound.
The concrete expansions and character identification remain to be proved. -/
theorem finrank_le_count_of_source_expansions (ρ : HighestWeightAction K V) (w : K)
    (hw : w^4-w^2+1 = 0) (minimum n : ℕ) (hm : 1 ≤ minimum)
    (ordering : ∀ i j, j < i → ρ.LocalReduction [i,j])
    (gapTwo : ∀ a : ℤ, a%3 = 0 →
      PairExpansion ρ (a+1) (a-1) (orderingCoeff w (a+1) (a-1)))
    (repeated : ∀ a : ℤ, a%3 ≠ 0 → PairExpansion ρ a a (repeatedCoeff w))
    (adjacent : ∀ a : ℤ, (2*a+1)%3 ≠ 0 → PairExpansion ρ a (a+1) (adjacentCoeff w))
    (initial : ∀ i, -(minimum:ℤ) < i →
      ρ.wordValue [i] ∈ higherSpan (K := K) ρ.wordValue [i]) :
    Module.finrank K (Partitions.cyclicGrade ρ n) ≤ Partitions.count minimum n :=
  Partitions.finrank_cyclicGrade_le_count ρ minimum n hm
    (forbiddenPairs_of_source_expansions ρ w ordering repeated adjacent)
    (forbiddenTriples_of_source_expansions ρ w hw ordering gapTwo repeated adjacent) initial

end KanadeRussell.Straightening
