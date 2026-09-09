import KanadeRussell.Sectors.SpanningBounds
import KanadeRussell.Tsuchioka.AllRootGeneration

/-! The minimum-three spanning theorem forces the first two relative
Z grades on the alternating seed to vanish, for every D4 root. -/
set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Partitions

/-- A nonempty partition cannot have positive total weight smaller than every part. -/
theorem count_eq_zero_of_pos_lt_minimum (minimum n : ℕ) (hn : 0 < n)
    (hsmall : n < minimum) : count minimum n = 0 := by
  letI : IsEmpty {p : Partition minimum // p.val.sum = n} := ⟨by
    rintro ⟨⟨l, hl⟩, hsum⟩
    cases l with
    | nil => simp at hsum; omega
    | cons a l =>
      have ha : minimum ≤ a := hl.1 a (by simp)
      simp only [List.sum_cons] at hsum
      omega⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

end KanadeRussell.Partitions

namespace KanadeRussell.Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

/-- There are no first-root cyclic vectors in relative degrees one or two. -/
theorem alternating_firstWordSpan_eq_bot_of_small (w : K) (hw : w^4-w^2+1=0)
    (n : ℕ) (hn : 0 < n) (hsmall : n < 3) :
    firstWordSpan w (alternatingSeed : Space K) (-(n : ℤ)) = ⊥ := by
  letI := Sectors.alternating_firstWordSpan_finite w hw n
  apply Submodule.finrank_eq_zero.mp
  have hbound := Sectors.alternating_firstWordSpan_finrank_le_count w hw n
  rw [Partitions.count_eq_zero_of_pos_lt_minimum 3 n hn hsmall] at hbound
  exact Nat.eq_zero_of_le_zero hbound

theorem alternating_firstWordSpan_neg_one_eq_bot (w : K) (hw : w^4-w^2+1=0) :
    firstWordSpan w (alternatingSeed : Space K) (-1) = ⊥ :=
  alternating_firstWordSpan_eq_bot_of_small w hw 1 (by decide) (by decide)

theorem alternating_firstWordSpan_neg_two_eq_bot (w : K) (hw : w^4-w^2+1=0) :
    firstWordSpan w (alternatingSeed : Space K) (-2) = ⊥ :=
  alternating_firstWordSpan_eq_bot_of_small w hw 2 (by decide) (by decide)

/-- The all-root homogeneous-generation theorem puts each small negative
root Z mode in the corresponding zero grade. -/
theorem rootMode_alternatingSeed_eq_zero_of_small (w : K) (hw : w^4-w^2+1=0)
    (beta : RootData.Root) (n : ℕ) (hn : 0 < n) (hsmall : n < 3) :
    rootMode w beta.val (-(n : ℤ)) (alternatingSeed : Space K) = 0 := by
  have hmem := firstWordSpan_rootMode_mem w hw alternatingSeed beta (-(n : ℤ)) 0
    alternatingSeed (firstWordSpan_seed w alternatingSeed)
  simpa only [add_zero, alternating_firstWordSpan_eq_bot_of_small w hw n hn hsmall,
    Submodule.mem_bot] using hmem

theorem rootMode_neg_one_alternatingSeed (w : K) (hw : w^4-w^2+1=0)
    (beta : RootData.Root) : rootMode w beta.val (-1) (alternatingSeed : Space K) = 0 :=
  rootMode_alternatingSeed_eq_zero_of_small w hw beta 1 (by decide) (by decide)

theorem rootMode_neg_two_alternatingSeed (w : K) (hw : w^4-w^2+1=0)
    (beta : RootData.Root) : rootMode w beta.val (-2) (alternatingSeed : Space K) = 0 :=
  rootMode_alternatingSeed_eq_zero_of_small w hw beta 2 (by decide) (by decide)

end KanadeRussell.Tsuchioka.Fock
