import KanadeRussell.Tsuchioka.Straightening
import KanadeRussell.Tsuchioka.ExceptionalReduction

/-!
# Transport of local operator reductions to arbitrary word contexts
-/

namespace KanadeRussell.Tsuchioka

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace HighestWeightAction

variable (ρ : HighestWeightAction K V)

def wordOperator : Word → Module.End K V
  | [] => LinearMap.id
  | i :: w => (ρ.mode i).comp (wordOperator w)

theorem wordValue_append (u v : Word) :
    ρ.wordValue (u ++ v) = ρ.wordOperator u (ρ.wordValue v) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, wordValue, wordOperator, LinearMap.comp_apply, ih]

/-- A local mode relation is required on every suffix vector. The finite
linear combination may depend on that suffix. This formulation avoids
treating an infinite formal operator expansion as an algebraic sum. -/
def LocalReduction (u : Word) : Prop :=
  ∀ t, ρ.wordValue (u ++ t) ∈
    higherSpan (K := K) (fun v => ρ.wordValue (v ++ t)) u

/-- A reduction evaluated on a fixed suffix can be multiplied by any
left word. Homogeneity and strictness are transported to the complete word. -/
theorem reduction_in_context (u t : Word)
    (h : ρ.wordValue (u ++ t) ∈
      higherSpan (K := K) (fun v => ρ.wordValue (v ++ t)) u)
    (s : Word) :
    ρ.wordValue (s ++ u ++ t) ∈
      higherSpan (K := K) ρ.wordValue (s ++ u ++ t) := by
  let S := higherSpan (K := K) ρ.wordValue (s ++ u ++ t)
  have hmap : ∀ x ∈ higherSpan (K := K) (fun v => ρ.wordValue (v ++ t)) u,
      ρ.wordOperator s x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, ⟨hv, hsum⟩, rfl⟩ := hy
      rw [← ρ.wordValue_append]
      apply mem_higherSpan
      · simpa only [List.append_assoc] using higher_context hv hsum s t
      · simp only [List.sum_append, hsum, add_assoc]
    | zero => simpa using S.zero_mem
    | add x y hx hy hix hiy =>
      simpa using S.add_mem hix hiy
    | smul c x hx hi =>
      simpa using S.smul_mem c hi
  have hv := hmap _ h
  rw [← ρ.wordValue_append] at hv
  simpa only [S, List.append_assoc] using hv

theorem LocalReduction.in_context {ρ : HighestWeightAction K V} {u : Word}
    (h : ρ.LocalReduction u) (s t : Word) :
    ρ.wordValue (s ++ u ++ t) ∈
      higherSpan (K := K) ρ.wordValue (s ++ u ++ t) :=
  ρ.reduction_in_context u t (h t) s

end HighestWeightAction

/-- Operator indices are the negatives of decreasing partition parts.
The last-index condition becomes the minimum-part condition once the
adjacent indices are ordered. The empty word satisfies all three conditions. -/
def AdmissibleWord (minimum : ℕ) (w : Word) : Prop :=
  (∀ s i, w = s ++ [i] → i ≤ -(minimum : ℤ)) ∧
  (∀ s t i j, w = s ++ [i, j] ++ t → PairAllowed i j) ∧
  (∀ s t i j k, w = s ++ [i, j, k] ++ t → i + 3 ≤ k)

/-- The full straightening induction from the six local reductions and the
initial conditions. This theorem does not construct or assert those
operator relations for the concrete D4^(3) modules. -/
theorem spanning_of_local_reductions
    (ρ : HighestWeightAction K V) (minimum : ℕ)
    (pairs : ∀ i j, ForbiddenPair i j → ρ.LocalReduction [i, j])
    (triples : ∀ i j k, ForbiddenTriple i j k → ρ.LocalReduction [i, j, k])
    (initial : ∀ i, -(minimum : ℤ) < i →
      ρ.wordValue [i] ∈ higherSpan (K := K) ρ.wordValue [i])
    (w : Word) :
    ρ.wordValue w ∈ Submodule.span K
      (ρ.wordValue '' {u | AdmissibleWord minimum u ∧ u.sum = w.sum}) := by
  classical
  apply wordValue_mem_span_normal ρ (AdmissibleWord minimum) ?_ w
  intro v hv hn
  change ρ.wordValue v ∈ higherSpan (K := K) ρ.wordValue v
  by_cases hlast : ∀ s i, v = s ++ [i] → i ≤ -(minimum : ℤ)
  · by_cases hp : ∀ s t i j, v = s ++ [i, j] ++ t → PairAllowed i j
    · have hbad : ¬∀ s t i j k, v = s ++ [i, j, k] ++ t → i + 3 ≤ k :=
        fun ht => hn ⟨hlast, hp, ht⟩
      push Not at hbad
      obtain ⟨s, t, i, j, k, rfl, hgap⟩ := hbad
      have hij : PairAllowed i j := hp s (k :: t) i j (by simp)
      have hjk : PairAllowed j k := hp (s ++ [i]) t j k (by simp [List.append_assoc])
      have hforbid := (forbiddenTriple_iff i j k hij hjk).mpr hgap
      exact (triples i j k hforbid).in_context s t
    · push Not at hp
      obtain ⟨s, t, i, j, rfl, hbad⟩ := hp
      exact (pairs i j ((forbiddenPair_iff i j).mpr hbad)).in_context s t
  · push Not at hlast
    obtain ⟨s, i, rfl, hi⟩ := hlast
    have h := ρ.reduction_in_context [i] [] (by simpa using initial i hi) s
    simpa using h


theorem admissibleWord_tail (minimum : ℕ) (i : ℤ) (w : Word)
    (h : AdmissibleWord minimum (i :: w)) : AdmissibleWord minimum w := by
  rcases h with ⟨hlast, hp, ht⟩
  refine ⟨?_, ?_, ?_⟩
  · intro s j hs
    apply hlast (i :: s) j
    simp [hs]
  · intro s t j k hs
    apply hp (i :: s) t j k
    simp [hs]
  · intro s t j k l hs
    apply ht (i :: s) t j k l
    simp [hs]

/-- The last-index condition really enforces the minimum on every part,
because the adjacent indices are ordered. -/
theorem admissibleWord_index_le (minimum : ℕ) (w : Word)
    (h : AdmissibleWord minimum w) : ∀ i ∈ w, i ≤ -(minimum : ℤ) := by
  induction w with
  | nil => simp
  | cons j w ih =>
    have ht := admissibleWord_tail minimum j w h
    have hw := ih ht
    have hj : j ≤ -(minimum : ℤ) := by
      cases w with
      | nil => exact h.1 [] j rfl
      | cons k w =>
        have hp : PairAllowed j k := h.2.1 [] w j k rfl
        exact hp.1.trans (hw k (by simp))
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hj
    · exact hw i hi



end KanadeRussell.Tsuchioka
