import KanadeRussell.Straightening.TripleOrder
import KanadeRussell.Straightening.SpanTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-! Critical overlaps of finite normalized two-mode relations. -/
namespace KanadeRussell.Straightening
open Tsuchioka
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem right_pair_tail_mem (ρ : HighestWeightAction K V) (a c : ℤ) (p : ℕ)
    (hp : 0 < p) (t : Word) (hred : ρ.LocalReduction [a+1+p,c-1]) :
    ρ.wordValue ([a-p,a+1+p,c-1] ++ t) ∈
      higherSpan (K := K) (fun u => ρ.wordValue (u ++ t)) [a,a,c] := by
  have hh := span_context ρ [a-p] [] t [a,a,c]
    {u | Higher u [a+1+p,c-1] ∧ u.sum = [a+1+p,c-1].sum} ?_
    (ρ.wordValue ([a+1+p,c-1] ++ t)) (by simpa only [higherSpan,List.append_nil] using hred t)
  · simpa only [HighestWeightAction.wordOperator,HighestWeightAction.wordValue,
      LinearMap.comp_apply,LinearMap.id_apply,List.cons_append,List.nil_append] using hh
  · intro u hu
    have hs : u.sum = (a+1+p)+(c-1) := by simpa using hu.2
    constructor
    · simpa using higher_right_pair_overlap a c p hp u hu.1 hs
    · simp only [List.sum_append,List.sum_cons,List.sum_nil,add_zero]
      omega

theorem left_pair_tail_mem (ρ : HighestWeightAction K V) (a : ℤ) (p : ℕ)
    (hp : 0 < p) (t : Word) (hred : ρ.LocalReduction [a-1,a-1-p]) :
    ρ.wordValue ([a-1,a-1-p,a+p] ++ t) ∈
      higherSpan (K := K) (fun u => ρ.wordValue (u ++ t)) [a-2,a,a] := by
  have hh := span_context ρ [] [a+p] t [a-2,a,a]
    {u | Higher u [a-1,a-1-p] ∧ u.sum = [a-1,a-1-p].sum} ?_
    (ρ.wordValue ([a-1,a-1-p] ++ [a+p] ++ t))
    (by simpa only [higherSpan,List.append_assoc] using hred ([a+p] ++ t))
  · simpa only [HighestWeightAction.wordOperator,LinearMap.id_apply,
      List.cons_append,List.nil_append] using hh
  · intro u hu
    have hs : u.sum = (a-1)+(a-1-p) := by simpa using hu.2
    constructor
    · simpa using higher_left_pair_overlap a p hp u hu.1 hs
    · simp only [List.sum_append,List.sum_cons,List.sum_nil,add_zero,zero_add]
      omega

/-- One overlap proves both F4 (c=a) and F5 (c=a+2).
The normalized pair expansions, including their nonzero first coefficient,
are explicit inputs and must be obtained from the concrete mode relations. -/
theorem overlap_right (ρ : HighestWeightAction K V) (a c : ℤ) (hc : c ≤ a+2)
    (leftCoeff rightCoeff : ℕ → K)
    (hleft : PairExpansion ρ a (a+1) leftCoeff)
    (hright : PairExpansion ρ (a+1) (c-1) rightCoeff)
    (hfirst : rightCoeff 1 ≠ 0)
    (ordering : ∀ i j, j < i → ρ.LocalReduction [i,j]) :
    ρ.LocalReduction [a,a,c] := by
  intro t
  let value (u : Word) := ρ.wordValue (u ++ t)
  let S := higherSpan (K := K) value [a,a,c]
  obtain ⟨N,hL⟩ := hleft.in_context [] [c-1] t [a,a,c] (by simp)
    (by simp only [List.sum_cons,List.sum_nil,add_zero,zero_add]; ring)
  change value [a,a+1,c-1] + ∑ p ∈ Finset.range (N+1),
    leftCoeff (p+1) • value [a-(p+1:ℕ),a+1+(p+1:ℕ),c-1] ∈ S at hL
  have htailL : (∑ p ∈ Finset.range (N+1),
      leftCoeff (p+1) • value [a-(p+1:ℕ),a+1+(p+1:ℕ),c-1]) ∈ S := by
    apply S.sum_mem
    intro p hp
    apply S.smul_mem
    exact right_pair_tail_mem ρ a c (p+1) (by omega) t (ordering _ _ (by omega))
  have hlead : value [a,a+1,c-1] ∈ S := by
    simpa using S.sub_mem hL htailL
  obtain ⟨M,hR⟩ := hright.in_context [a] [] t [a,a,c] (by simp)
    (by simp only [List.sum_cons,List.sum_nil,add_zero]; ring)
  change value [a,a+1,c-1] + ∑ p ∈ Finset.range (M+1),
    rightCoeff (p+1) • value [a,a+1-(p+1:ℕ),c-1+(p+1:ℕ)] ∈ S at hR
  have htailR : (∑ p ∈ Finset.range M,
      rightCoeff (p+2) • value [a,a+1-(p+2:ℕ),c-1+(p+2:ℕ)]) ∈ S := by
    apply S.sum_mem
    intro p hp
    apply S.smul_mem
    apply mem_higherSpan
    · apply higher_triple <;> omega
    · simp only [List.sum_cons,List.sum_nil,add_zero]
      omega
  have hx : rightCoeff 1 • value [a,a,c] ∈ S := by
    convert S.sub_mem (S.sub_mem hR hlead) htailR using 1
    simp only [Finset.sum_range_succ',zero_add,Nat.cast_one,Nat.add_assoc,
      Nat.reduceAdd,add_sub_cancel_right,sub_add_cancel]
    module
  exact (S.smul_mem_iff hfirst).mp hx

/-- The left overlap yields F6, retaining the same repeated-pair first coefficient. -/
theorem overlap_left (ρ : HighestWeightAction K V) (a : ℤ)
    (leftCoeff rightCoeff : ℕ → K)
    (hleft : PairExpansion ρ (a-1) (a-1) leftCoeff)
    (hright : PairExpansion ρ (a-1) a rightCoeff)
    (hfirst : leftCoeff 1 ≠ 0)
    (ordering : ∀ i j, j < i → ρ.LocalReduction [i,j]) :
    ρ.LocalReduction [a-2,a,a] := by
  intro t
  let value (u : Word) := ρ.wordValue (u ++ t)
  let S := higherSpan (K := K) value [a-2,a,a]
  obtain ⟨N,hR⟩ := hright.in_context [a-1] [] t [a-2,a,a] (by simp)
    (by simp only [List.sum_cons,List.sum_nil,add_zero]; ring)
  change value [a-1,a-1,a] + ∑ p ∈ Finset.range (N+1),
    rightCoeff (p+1) • value [a-1,a-1-(p+1:ℕ),a+(p+1:ℕ)] ∈ S at hR
  have htailR : (∑ p ∈ Finset.range (N+1),
      rightCoeff (p+1) • value [a-1,a-1-(p+1:ℕ),a+(p+1:ℕ)]) ∈ S := by
    apply S.sum_mem
    intro p hp
    apply S.smul_mem
    exact left_pair_tail_mem ρ a (p+1) (by omega) t (ordering _ _ (by omega))
  have hlead : value [a-1,a-1,a] ∈ S := by
    simpa using S.sub_mem hR htailR
  obtain ⟨M,hL⟩ := hleft.in_context [] [a] t [a-2,a,a] (by simp)
    (by simp only [List.sum_cons,List.sum_nil,add_zero,zero_add]; ring)
  change value [a-1,a-1,a] + ∑ p ∈ Finset.range (M+1),
    leftCoeff (p+1) • value [a-1-(p+1:ℕ),a-1+(p+1:ℕ),a] ∈ S at hL
  have htailL : (∑ p ∈ Finset.range M,
      leftCoeff (p+2) • value [a-1-(p+2:ℕ),a-1+(p+2:ℕ),a]) ∈ S := by
    apply S.sum_mem
    intro p hp
    apply S.smul_mem
    apply mem_higherSpan
    · apply higher_triple <;> omega
    · simp only [List.sum_cons,List.sum_nil,add_zero]
      omega
  have hx : leftCoeff 1 • value [a-2,a,a] ∈ S := by
    convert S.sub_mem (S.sub_mem hL hlead) htailL using 1
    simp only [Finset.sum_range_succ',zero_add,Nat.cast_one,Nat.add_assoc,
      Nat.reduceAdd,sub_add_cancel,sub_sub,Int.reduceAdd]
    module
  exact (S.smul_mem_iff hfirst).mp hx

end KanadeRussell.Straightening
