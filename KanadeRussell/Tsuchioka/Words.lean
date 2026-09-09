import Mathlib

/-!
# The word order and forbidden patterns in Tsuchioka, Section 4

An operator word `[i₁, ..., iₗ]` represents `Zᵢ₁ ... Zᵢₗ w₀`.
The suffix sums must be nonpositive for a word to survive on a highest-weight
vector. The word order is only well founded after this restriction.
These lemmas do not assert any operator relation or character formula.
-/

namespace KanadeRussell.Tsuchioka

abbrev Word := List ℤ

def suffixSums : Word → List ℤ
  | [] => []
  | i :: w => (i + w.sum) :: suffixSums w

@[simp] theorem suffixSums_length (w : Word) : (suffixSums w).length = w.length := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [suffixSums, ih]

theorem suffixSums_injective : Function.Injective suffixSums := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v <;> simp_all [suffixSums]
  | cons i u ih =>
    intro v h
    cases v with
    | nil => simp [suffixSums] at h
    | cons j v =>
      simp only [suffixSums, List.cons.injEq] at h
      have hv := ih h.2
      subst v
      have hij : i = j := by omega
      subst j
      rfl

/-- The support restriction in the definition of `Supp₀` in Section 4.2. -/
def Survives (w : Word) : Prop := ∀ s ∈ suffixSums w, s ≤ 0

/-- Tsuchioka's strict higher-word order, with the higher word first. -/
def Higher (u v : Word) : Prop :=
  u.length < v.length ∨
    (u ≠ v ∧ List.Forall₂ (fun a b : ℤ => b ≤ a) (suffixSums u) (suffixSums v))

/-- A natural-number measure for equal-length surviving words. -/
def suffixMass (w : Word) : ℕ := (-(suffixSums w).sum).toNat

private theorem sum_le_of_forall₂ {u v : List ℤ}
    (h : List.Forall₂ (fun a b : ℤ => b ≤ a) u v) : v.sum ≤ u.sum := by
  induction h with
  | nil => simp
  | cons h htail ih => simpa only [List.sum_cons] using add_le_add h ih

private theorem sum_lt_of_forall₂ {u v : List ℤ}
    (h : List.Forall₂ (fun a b : ℤ => b ≤ a) u v) (hne : u ≠ v) :
    v.sum < u.sum := by
  induction h with
  | nil => exact (hne rfl).elim
  | @cons a b u v hab htail ih =>
    have hsum := sum_le_of_forall₂ htail
    by_cases huv : u = v
    · subst v
      have : a ≠ b := by intro h; subst b; exact hne rfl
      simp only [List.sum_cons]
      omega
    · have := ih huv
      simp only [List.sum_cons]
      omega

theorem suffixMass_lt {u v : Word} (hu : Survives u) (hne : u ≠ v)
    (h : List.Forall₂ (fun a b : ℤ => b ≤ a) (suffixSums u) (suffixSums v)) :
    suffixMass u < suffixMass v := by
  have hlt := sum_lt_of_forall₂ h (fun heq => hne (suffixSums_injective heq))
  have hnonpos : (suffixSums u).sum ≤ 0 := by
    simpa using List.sum_le_card_nsmul (suffixSums u) 0 hu
  unfold suffixMass
  omega

/-- The adjacent ordering and congruence conditions, in operator indices. -/
def PairAllowed (a b : ℤ) : Prop := a ≤ b ∧ (b ≤ a + 1 → (a + b) % 3 = 0)

/-- Precisely the triples excluded by (F4), (F5), and (F6). -/
def ForbiddenTriple (a b c : ℤ) : Prop :=
  (a = b ∧ b = c ∧ a % 3 = 0) ∨
  (a = b ∧ c = a + 2 ∧ a % 3 = 0) ∨
  (b = c ∧ b = a + 2 ∧ b % 3 = 0)

/-- Once (F1)--(F3) have been applied, the three remaining forbidden patterns
are exactly the failures of the distance-two gap. This holds for all integer
indices; it is not a bounded enumeration. -/
theorem forbiddenTriple_iff (a b c : ℤ) (hab : PairAllowed a b)
    (hbc : PairAllowed b c) : ForbiddenTriple a b c ↔ c < a + 3 := by
  unfold PairAllowed at hab hbc
  unfold ForbiddenTriple
  constructor
  · omega
  · intro h
    have hab' : b = a ∨ b = a + 1 ∨ b = a + 2 := by omega
    have hac' : c = a ∨ c = a + 1 ∨ c = a + 2 := by omega
    rcases hab' with rfl | rfl | rfl <;>
      rcases hac' with rfl | rfl | rfl <;>
      simp_all [Int.add_emod] <;> omega

/-- The order becomes well founded on the words which survive on a
highest-weight vector. Shorter words lower the first measure; at fixed length,
strict suffix dominance lowers the sum of the negated suffix sums. -/
theorem higher_wellFounded :
    WellFounded (fun u v : {w : Word // Survives w} => Higher u.val v.val) := by
  let rank : {w : Word // Survives w} → ℕ × ℕ := fun w => (w.val.length, suffixMass w.val)
  refine Subrelation.wf (r := InvImage (Prod.Lex (· < ·) (· < ·)) rank) ?_ ?_
  · intro u v h
    rcases h with h | ⟨hne, h⟩
    · exact Prod.Lex.left _ _ h
    · have hlen : u.val.length = v.val.length := by
        simpa using h.length_eq
      change Prod.Lex (· < ·) (· < ·)
        (u.val.length, suffixMass u.val) (v.val.length, suffixMass v.val)
      rw [hlen]
      exact Prod.Lex.right _ (suffixMass_lt u.property hne h)
  · exact InvImage.wf rank (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf



theorem suffixSums_append (u v : Word) :
    suffixSums (u ++ v) =
      (suffixSums u).map (fun s => s + v.sum) ++ suffixSums v := by
  induction u with
  | nil => simp [suffixSums]
  | cons i u ih =>
    simp [suffixSums, List.sum_append, ih, add_assoc]

/-- Adding a common word on the right preserves higher-word comparisons. -/
theorem higher_append_right {u v : Word} (h : Higher u v) (t : Word) :
    Higher (u ++ t) (v ++ t) := by
  rcases h with h | ⟨hne, h⟩
  · exact Or.inl (by simpa using h)
  · refine Or.inr ⟨fun heq => hne (List.append_cancel_right heq), ?_⟩
    rw [suffixSums_append, suffixSums_append]
    apply List.rel_append
    · simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact List.Forall₂.imp (fun a b hab => by simpa using hab) h
    · exact List.forall₂_refl _

/-- A common left context preserves comparison when the local replacement
preserves its total index. This is the homogeneity needed by straightening. -/
theorem higher_append_left {u v : Word} (h : Higher u v)
    (hsum : u.sum = v.sum) (t : Word) : Higher (t ++ u) (t ++ v) := by
  rcases h with h | ⟨hne, h⟩
  · exact Or.inl (by simpa using h)
  · refine Or.inr ⟨fun heq => hne (List.append_cancel_left heq), ?_⟩
    rw [suffixSums_append, suffixSums_append, hsum]
    exact List.rel_append (List.forall₂_refl _) h

theorem higher_context {u v : Word} (h : Higher u v) (hsum : u.sum = v.sum)
    (s t : Word) : Higher (s ++ u ++ t) (s ++ v ++ t) :=
  higher_append_right (higher_append_left h hsum s) t

theorem higher_pair_shift (a b : ℤ) (p : ℕ) (hp : 0 < p) :
    Higher [a - p, b + p] [a, b] := by
  right
  constructor
  · intro h
    simp only [List.cons.injEq] at h
    omega
  · simp only [suffixSums, List.sum_cons, List.sum_nil, add_zero]
    exact .cons (by omega) (.cons (by omega) .nil)

theorem higher_pair_swap (a b : ℤ) (p : ℕ) (hab : b < a) :
    Higher [b - p, a + p] [a, b] := by
  right
  constructor
  · intro h
    simp only [List.cons.injEq] at h
    omega
  · simp only [suffixSums, List.sum_cons, List.sum_nil, add_zero]
    exact .cons (by omega) (.cons (by omega) .nil)

/-- All direct terms of the shifted exceptional relation are strictly higher. -/
theorem higher_exceptional_direct (a b : ℤ) (p : ℕ) :
    Higher [a - 1 - p, b + 1 + p] [a, b] := by
  right
  constructor
  · intro h
    simp only [List.cons.injEq] at h
    omega
  · simp only [suffixSums, List.sum_cons, List.sum_nil, add_zero]
    exact .cons (by omega) (.cons (by omega) .nil)

/-- The reversed terms are also strictly higher; the exceptional class
has a-b at least seven, which is stronger than the needed bound. -/
theorem higher_exceptional_swap (a b : ℤ) (p : ℕ) (hab : b + 2 ≤ a) :
    Higher [b + 1 - p, a - 1 + p] [a, b] := by
  right
  constructor
  · intro h
    simp only [List.cons.injEq] at h
    omega
  · simp only [suffixSums, List.sum_cons, List.sum_nil, add_zero]
    exact .cons (by omega) (.cons (by omega) .nil)

theorem exceptional_gap (a b : ℤ) (hab : b < a) (hr : (a - b) % 12 = 7) :
    b + 7 ≤ a := by omega

/-- The adjacent operator reductions (F1)--(F3), expressed as patterns. -/
def ForbiddenPair (a b : ℤ) : Prop :=
  b < a ∨ (a = b ∧ (2 * a) % 3 ≠ 0) ∨
    (b = a + 1 ∧ (2 * a + 1) % 3 ≠ 0)

theorem forbiddenPair_iff (a b : ℤ) : ForbiddenPair a b ↔ ¬PairAllowed a b := by
  unfold ForbiddenPair PairAllowed
  omega




theorem higher_adjacent_swap (a : ℤ) (p : ℕ) (hp : 1 < p) :
    Higher [a + 1 - p, a + p] [a, a + 1] := by
  right
  constructor
  · intro h
    simp only [List.cons.injEq] at h
    omega
  · simp only [suffixSums, List.sum_cons, List.sum_nil, add_zero]
    exact .cons (by omega) (.cons (by omega) .nil)


end KanadeRussell.Tsuchioka
