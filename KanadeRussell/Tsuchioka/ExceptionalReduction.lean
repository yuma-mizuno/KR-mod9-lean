import KanadeRussell.Tsuchioka.Words

/-!
# Extraction of the corrected exceptional ordering reduction

The operator identities themselves are not assumed globally. The theorem below
says precisely what follows when their finite truncations hold on a vector.
All terms except the target are proved to be strictly higher words.
-/

open scoped BigOperators

namespace KanadeRussell.Tsuchioka

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def higherSpan (value : Word → V) (w : Word) : Submodule K V :=
  Submodule.span K (value '' {u | Higher u w ∧ u.sum = w.sum})

theorem mem_higherSpan (value : Word → V) {u w : Word} (h : Higher u w) (hsum : u.sum = w.sum) :
    value u ∈ higherSpan (K := K) value w :=
  Submodule.subset_span ⟨u, ⟨h, hsum⟩, rfl⟩

/-- The finite skew sum in the first relation of Theorem 3.2. -/
def skewSum (value : Word → V) (c : ℕ → K) (a b : ℤ) (N : ℕ) : V :=
  ∑ p ∈ Finset.range N,
    c p • (value [a - p, b + p] - value [b - p, a + p])

theorem skewSum_sub_target_mem (value : Word → V) (c : ℕ → K)
    (hc : c 0 = 1) (a b : ℤ) (hab : b < a) (N : ℕ) :
    skewSum value c a b (N + 1) - value [a, b] ∈
      higherSpan (K := K) value [a, b] := by
  let S := higherSpan (K := K) value [a, b]
  have htail :
      (∑ p ∈ Finset.range N,
        c (p + 1) • (value [a - (p + 1 : ℕ), b + (p + 1 : ℕ)] -
          value [b - (p + 1 : ℕ), a + (p + 1 : ℕ)])) ∈ S := by
    apply Submodule.sum_mem
    intro p hp
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact mem_higherSpan value (higher_pair_shift a b (p + 1) (by omega)) (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
    · exact mem_higherSpan value (higher_pair_swap a b (p + 1) hab) (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
  have hswap : value [b, a] ∈ S := by
    simpa using mem_higherSpan (K := K) value (higher_pair_swap a b 0 hab) (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
  have h := S.sub_mem htail hswap
  convert h using 1
  simp only [skewSum, Finset.sum_range_succ', hc, Nat.cast_zero, sub_zero, add_zero, one_smul]
  abel

theorem exceptional_skewSum_mem (value : Word → V) (c : ℕ → K)
    (a b : ℤ) (hab : b + 2 ≤ a) (N : ℕ) :
    skewSum value c (a - 1) (b + 1) N ∈
      higherSpan (K := K) value [a, b] := by
  apply Submodule.sum_mem
  intro p hp
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · exact mem_higherSpan value (higher_exceptional_direct a b p) (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
  · exact mem_higherSpan value (higher_exceptional_swap a b p hab) (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)

/-- The repaired F1 extraction. The two hypotheses are the first relation
at (A,B) and (A-1,B+1), after placing the lower-length terms in higherSpan.
The common second-root term cancels. No convergence assertion is hidden:
each identity is a finite truncation, and its cutoff is explicit. -/
theorem exceptional_ordering_reduction
    (value : Word → V) (c : ℕ → K) (hc : c 0 = 1)
    (a b : ℤ) (hab : b < a) (hr : (a - b) % 12 = 7)
    (N M : ℕ) (zprime : V) (β : K)
    (h₁ : skewSum value c a b (N + 1) - β • zprime ∈
      higherSpan (K := K) value [a, b])
    (h₂ : skewSum value c (a - 1) (b + 1) M - β • zprime ∈
      higherSpan (K := K) value [a, b]) :
    value [a, b] ∈ higherSpan (K := K) value [a, b] := by
  let S := higherSpan (K := K) value [a, b]
  have ht := skewSum_sub_target_mem value c hc a b hab N
  have hs := exceptional_skewSum_mem value c a b
    (by have := exceptional_gap a b hab hr; omega) M
  have hdiff : skewSum value c a b (N + 1) -
      skewSum value c (a - 1) (b + 1) M ∈ S := by
    convert S.sub_mem h₁ h₂ using 1
    abel
  convert S.sub_mem (S.add_mem hdiff hs) ht using 1
  abel

end KanadeRussell.Tsuchioka
