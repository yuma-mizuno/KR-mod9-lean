import Mathlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Local partition conditions and their three-step block decomposition. -/
namespace KanadeRussell.Partitions

def PairOK (a b : ℕ) : Prop := a ≤ b ∧ (b ≤ a+1 → (a+b)%3 = 0)

def Valid : List ℕ → Prop
  | [] => True
  | a::l =>
      (match l with | [] => True | b::_ => PairOK a b) ∧
      (match l with | _::c::_ => a+3 ≤ c | _ => True) ∧ Valid l

def Admissible (minimum : ℕ) (l : List ℕ) : Prop :=
  (∀ a ∈ l, minimum ≤ a) ∧ Valid l

def block : Fin 7 → List ℕ := ![[],[1],[2],[3],[1,2],[1,3],[3,3]]
def nextMinimum : Fin 7 → ℕ := ![1,1,1,2,1,2,3]

theorem pair_shift (a b : ℕ) : PairOK (a+3) (b+3) ↔ PairOK a b := by
  unfold PairOK
  omega

theorem valid_shift (l : List ℕ) : Valid (l.map (·+3)) ↔ Valid l := by
  induction l with
  | nil => simp [Valid]
  | cons a l ih =>
    cases l with
    | nil => simp [Valid]
    | cons b l =>
      cases l with
      | nil => simpa [Valid] using pair_shift a b
      | cons c l =>
        change (PairOK (a+3) (b+3) ∧ a+3+3 ≤ c+3 ∧ Valid ((b::c::l).map (·+3))) ↔
          (PairOK a b ∧ a+3 ≤ c ∧ Valid (b::c::l))
        rw [pair_shift, ih]
        simp only [Nat.add_le_add_iff_right]

theorem valid_head_le (a : ℕ) (l : List ℕ) (h : Valid (a::l)) : ∀ b ∈ l, a ≤ b := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have hab : a ≤ b := h.1.1
    have ht : Valid (b::l) := h.2.2
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab
    · exact hab.trans (ih b ht c hc)

theorem admissible_cons (minimum a : ℕ) (l : List ℕ) :
    Admissible minimum (a::l) ↔ minimum ≤ a ∧ Valid (a::l) := by
  constructor
  · intro h
    exact ⟨h.1 a (by simp), h.2⟩
  · rintro ⟨ha,hv⟩
    refine ⟨?_,hv⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact ha.trans (valid_head_le a l hv b hb)

theorem valid_triple (a b c : ℕ) (l : List ℕ) :
    Valid (a::b::c::l) ↔ PairOK a b ∧ a+3 ≤ c ∧ Valid (b::c::l) := Iff.rfl

/-- Every local transition applies to an arbitrary positive tail. -/
theorem block_append (i : Fin 7) (l : List ℕ) (hpos : ∀ a ∈ l, 1 ≤ a) :
    Admissible 1 (block i ++ l.map (·+3)) ↔ Admissible (nextMinimum i) l := by
  fin_cases i <;> cases l with
  | nil => simp [Admissible, block, nextMinimum, Valid, PairOK]
  | cons a l =>
    have ha : 1 ≤ a := hpos a (by simp)
    cases l with
    | nil => simp [admissible_cons, block, nextMinimum, Valid, PairOK]; omega
    | cons b l =>
      have hb : 1 ≤ b := hpos b (by simp)
      have hv := valid_shift (a::b::l)
      simp only [List.map_cons] at hv
      by_cases ht : Valid (a::b::l)
      · have hab : PairOK a b := ht.1
        simp [block, nextMinimum, admissible_cons, valid_triple, hv, ht, PairOK];
          unfold PairOK at hab; omega
      · simp [block, nextMinimum, admissible_cons, valid_triple, hv, ht]

theorem block_injective : Function.Injective block := by decide

theorem block_bounds (i : Fin 7) : ∀ a ∈ block i, 1 ≤ a ∧ a ≤ 3 := by
  fin_cases i <;> simp [block]

theorem nextMinimum_bounds (i : Fin 7) : 1 ≤ nextMinimum i ∧ nextMinimum i ≤ 3 := by
  fin_cases i <;> decide

/-- The seven blocks exhaust every admissible list supported in {1,2,3}. -/
theorem exists_block (l : List ℕ) (h : Admissible 1 l) (hb : ∀ a ∈ l, a ≤ 3) :
    ∃ i, block i = l := by
  cases l with
  | nil => exact ⟨0,rfl⟩
  | cons a l =>
    have ha := h.1 a (by simp)
    have ha' := hb a (by simp)
    cases l with
    | nil => interval_cases a <;> first | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩
    | cons b l =>
      have hb' := h.1 b (by simp)
      have hb'' := hb b (by simp)
      cases l with
      | nil =>
        have hp := h.2.1
        unfold PairOK at hp
        interval_cases a <;> interval_cases b <;>
          first | omega | exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩
      | cons c l =>
        have hc := hb c (by simp)
        have hg := h.2.2.1
        omega

theorem valid_take (l : List ℕ) (n : ℕ) (h : Valid l) : Valid (l.take n) := by
  induction n generalizing l with
  | zero => simp [Valid]
  | succ n ih =>
    cases l with
    | nil => simp [Valid]
    | cons a l =>
      cases n with
      | zero => simp [Valid]
      | succ n =>
        cases l with
        | nil => simp [Valid]
        | cons b l =>
          cases n with
          | zero => simpa [Valid] using h.1
          | succ n =>
            cases l with
            | nil => simpa [Valid] using h
            | cons c l =>
              exact ⟨h.1,h.2.1,ih (b::c::l) h.2.2⟩

theorem valid_drop (l : List ℕ) (n : ℕ) (h : Valid l) : Valid (l.drop n) := by
  induction n generalizing l with
  | zero => simpa using h
  | succ n ih =>
    cases l with
    | nil => simp [Valid]
    | cons a l => exact ih l h.2.2

end KanadeRussell.Partitions
