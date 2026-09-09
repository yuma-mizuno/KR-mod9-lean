import KanadeRussell.Tsuchioka.Words
set_option backward.isDefEq.respectTransparency false

/-!
# Highest-weight truncation and the induction underlying straightening

This file proves the general linear-algebra part of Section 4.2.
The concrete D₄⁽³⁾ action and the local reductions must still be constructed.
In particular, a hypothesis about reductions is not asserted as a theorem.
-/

namespace KanadeRussell.Tsuchioka

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The grading data needed for truncation. The mode with index i lowers
degree by i, and the vacuum has degree zero. -/
structure HighestWeightAction (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  grade : ℤ → Submodule K V
  negative : ∀ n, n < 0 → grade n = ⊥
  mode : ℤ → Module.End K V
  mode_mem : ∀ i n v, v ∈ grade n → mode i v ∈ grade (n - i)
  vacuum : V
  vacuum_mem : vacuum ∈ grade 0

namespace HighestWeightAction

variable (ρ : HighestWeightAction K V)

def wordValue : Word → V
  | [] => ρ.vacuum
  | i :: w => ρ.mode i (wordValue w)

theorem wordValue_mem (w : Word) : ρ.wordValue w ∈ ρ.grade (-w.sum) := by
  induction w with
  | nil => simpa [wordValue] using ρ.vacuum_mem
  | cons i w ih =>
    have h := ρ.mode_mem i (-w.sum) (ρ.wordValue w) ih
    simpa only [wordValue, List.sum_cons, neg_add_rev, sub_eq_add_neg] using h

/-- Any positive suffix sum forces the operator word to vanish on the vacuum.
This justifies restricting the higher-word induction to surviving words. -/
theorem wordValue_eq_zero_of_not_survives (w : Word) (h : ¬Survives w) :
    ρ.wordValue w = 0 := by
  induction w with
  | nil => exact (h (by simp [Survives, suffixSums])).elim
  | cons i w ih =>
    by_cases hw : Survives w
    · have hs : 0 < i + w.sum := by
        by_contra hs
        apply h
        intro s hmem
        simp only [suffixSums, List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · omega
        · exact hw s hmem
      have hv := ρ.wordValue_mem (i :: w)
      rw [ρ.negative _ (by simp only [List.sum_cons]; omega)] at hv
      simpa using hv
    · simp only [wordValue, ih hw, map_zero]

end HighestWeightAction

/-- Abstract straightening, keeping the total degree. A reduction expresses a
non-normal word as a finite linear combination of strictly higher words of
the same total index. Highest-weight truncation discards nonsurviving words.
No confluence, uniqueness, or linear independence is required. -/
theorem wordValue_mem_span_normal
    (ρ : HighestWeightAction K V) (normal : Word → Prop)
    (reduce : ∀ w, Survives w → ¬normal w →
      ρ.wordValue w ∈ Submodule.span K
        (ρ.wordValue '' {u | Higher u w ∧ u.sum = w.sum}))
    (w : Word) :
    ρ.wordValue w ∈ Submodule.span K
      (ρ.wordValue '' {u | normal u ∧ u.sum = w.sum}) := by
  classical
  by_cases hw : Survives w
  · let P (w : {w : Word // Survives w}) : Prop :=
      ρ.wordValue w.val ∈ Submodule.span K
        (ρ.wordValue '' {u | normal u ∧ u.sum = w.val.sum})
    have hp : ∀ v, P v := by
      intro v
      induction v using higher_wellFounded.induction with
      | h v ih =>
        by_cases hn : normal v.val
        · exact Submodule.subset_span ⟨v.val, ⟨hn, rfl⟩, rfl⟩
        · refine (Submodule.span_le.mpr ?_ :
            Submodule.span K (ρ.wordValue '' {u | Higher u v.val ∧ u.sum = v.val.sum}) ≤
              Submodule.span K (ρ.wordValue '' {u | normal u ∧ u.sum = v.val.sum}))
              (reduce v.val v.property hn)
          rintro _ ⟨u, ⟨hhigh, hsum⟩, rfl⟩
          by_cases hu : Survives u
          · have hi := ih ⟨u, hu⟩ hhigh
            dsimp [P] at hi ⊢
            rw [hsum] at hi
            exact hi
          · rw [ρ.wordValue_eq_zero_of_not_survives u hu]
            exact Submodule.zero_mem _
    exact hp ⟨w, hw⟩
  · rw [ρ.wordValue_eq_zero_of_not_survives w hw]
    exact Submodule.zero_mem _

/-- The numerical inequality used to pass from homogeneous spanning to
Corollary 1.4. Concrete spanning and character identifications remain inputs. -/
theorem finrank_le_card_of_spanning {ι : Type*} [Fintype ι]
    (v : ι → V) (h : Submodule.span K (Set.range v) = ⊤) :
    Module.finrank K V ≤ Fintype.card ι := by
  have hcard := finrank_range_le_card (R := K) v
  change Module.finrank K (Submodule.span K (Set.range v)) ≤ _ at hcard
  rw [h] at hcard
  simpa using hcard

end KanadeRussell.Tsuchioka
