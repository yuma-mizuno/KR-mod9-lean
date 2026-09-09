import KanadeRussell.Partitions.Counting
import KanadeRussell.Tsuchioka.LocalReduction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Degree-preserving correspondence between partitions and admissible operator words. -/
namespace KanadeRussell.Partitions
open Tsuchioka

private def Pairs {α : Type*} (R : α → α → Prop) (l : List α) : Prop :=
  ∀ s t a b, l = s ++ [a,b] ++ t → R a b

private def Triples {α : Type*} (R : α → α → α → Prop) (l : List α) : Prop :=
  ∀ s t a b c, l = s ++ [a,b,c] ++ t → R a b c

private theorem pairs_nil {α : Type*} (R : α → α → Prop) : Pairs R [] := by
  intro s t a b h
  have := congrArg List.length h
  simp at this

private theorem triples_nil {α : Type*} (R : α → α → α → Prop) : Triples R [] := by
  intro s t a b c h
  have := congrArg List.length h
  simp at this

private theorem pairs_cons {α : Type*} (R : α → α → Prop) (a : α) (l : List α) :
    Pairs R (a::l) ↔ (match l with | [] => True | b::_ => R a b) ∧ Pairs R l := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · cases l with
      | nil => trivial
      | cons b t => exact h [] t a b rfl
    · intro s t b c he
      exact h (a::s) t b c (by simp [he])
  · rintro ⟨h,ht⟩ s t b c he
    cases s with
    | nil =>
      simp only [List.nil_append,List.cons_append,List.nil_append,List.cons.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      exact h
    | cons d s =>
      simp only [List.cons_append,List.cons.injEq] at he
      exact ht s t b c he.2

private theorem triples_cons {α : Type*} (R : α → α → α → Prop) (a : α) (l : List α) :
    Triples R (a::l) ↔ (match l with | b::c::_ => R a b c | _ => True) ∧ Triples R l := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · cases l with
      | nil => trivial
      | cons b t =>
        cases t with
        | nil => trivial
        | cons c t => exact h [] t a b c rfl
    · intro s t b c d he
      exact h (a::s) t b c d (by simp [he])
  · rintro ⟨h,ht⟩ s t b c d he
    cases s with
    | nil =>
      simp only [List.nil_append,List.cons_append,List.nil_append,List.cons.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      exact h
    | cons e s =>
      simp only [List.cons_append,List.cons.injEq] at he
      exact ht s t b c d he.2

private theorem valid_patterns (l : List ℕ) :
    Valid l ↔ Pairs PairOK l ∧ Triples (fun a _ c => a+3 ≤ c) l := by
  induction l with
  | nil => exact ⟨fun _ => ⟨pairs_nil _,triples_nil _⟩,fun _ => by trivial⟩
  | cons a l ih =>
    rw [pairs_cons,triples_cons]
    change (_ ∧ _ ∧ Valid l) ↔ _
    rw [ih]
    cases l with
    | nil => tauto
    | cons b l => cases l <;> simp only <;> tauto

private theorem pairs_reverse {α : Type*} (R : α → α → Prop) (l : List α) :
    Pairs R l.reverse ↔ Pairs (fun a b => R b a) l := by
  constructor
  · intro h s t a b he
    exact h t.reverse s.reverse b a (by simp [he,List.reverse_append,List.append_assoc])
  · intro h s t a b he
    apply h t.reverse s.reverse b a
    have hh := congrArg List.reverse he
    simpa [List.reverse_append,List.append_assoc] using hh

private theorem triples_reverse {α : Type*} (R : α → α → α → Prop) (l : List α) :
    Triples R l.reverse ↔ Triples (fun a b c => R c b a) l := by
  constructor
  · intro h s t a b c he
    exact h t.reverse s.reverse c b a (by simp [he,List.reverse_append,List.append_assoc])
  · intro h s t a b c he
    apply h t.reverse s.reverse c b a
    have hh := congrArg List.reverse he
    simpa [List.reverse_append,List.append_assoc] using hh

private theorem pairs_map {α β : Type*} (R : β → β → Prop) (f : α → β) (l : List α) :
    Pairs R (l.map f) ↔ Pairs (fun a b => R (f a) (f b)) l := by
  induction l with
  | nil => exact iff_of_true (pairs_nil _) (pairs_nil _)
  | cons a l ih =>
    simp only [List.map_cons,pairs_cons,ih]
    cases l <;> simp

private theorem triples_map {α β : Type*} (R : β → β → β → Prop) (f : α → β) (l : List α) :
    Triples R (l.map f) ↔ Triples (fun a b c => R (f a) (f b) (f c)) l := by
  induction l with
  | nil => exact iff_of_true (triples_nil _) (triples_nil _)
  | cons a l ih =>
    simp only [List.map_cons,triples_cons,ih]
    cases l with
    | nil => simp
    | cons b l => cases l <;> simp

private theorem admissibleWord_patterns (minimum : ℕ) (w : Word) :
    AdmissibleWord minimum w ↔ (∀ i ∈ w, i ≤ -(minimum : ℤ)) ∧
      Pairs PairAllowed w ∧ Triples (fun a _ c => a+3 ≤ c) w := by
  constructor
  · intro h
    exact ⟨admissibleWord_index_le minimum w h,h.2⟩
  · rintro ⟨h,hp,ht⟩
    refine ⟨?_,hp,ht⟩
    intro s i he
    apply h i
    simp [he]

def wordOfParts (l : List ℕ) : Word := (l.map (fun a : ℕ => -(a:ℤ))).reverse

theorem pair_neg_reverse (a b : ℕ) : PairAllowed (-(b:ℤ)) (-(a:ℤ)) ↔ PairOK a b := by
  unfold PairAllowed PairOK
  omega

theorem wordOfParts_admissible (minimum : ℕ) (l : List ℕ) :
    AdmissibleWord minimum (wordOfParts l) ↔ Admissible minimum l := by
  rw [admissibleWord_patterns]
  unfold wordOfParts
  rw [pairs_reverse, pairs_map _ (fun a : ℕ => -(a:ℤ)) l,
    triples_reverse, triples_map _ (fun a : ℕ => -(a:ℤ)) l]
  have hp : Pairs (fun a b : ℕ => PairAllowed (-(b:ℤ)) (-(a:ℤ))) l ↔ Pairs PairOK l := by
    simp only [Pairs,pair_neg_reverse]
  have ht : Triples (fun a _ c : ℕ => -(c:ℤ)+3 ≤ -(a:ℤ)) l ↔
      Triples (fun a _ c => a+3 ≤ c) l := by
    have he (a c : ℕ) : -(c:ℤ)+3 ≤ -(a:ℤ) ↔ a+3 ≤ c := by omega
    simp only [Triples,he]
  rw [hp,ht,← valid_patterns]
  unfold Admissible
  refine and_congr ?_ Iff.rfl
  simp only [List.mem_reverse,List.mem_map,forall_exists_index,and_imp]
  constructor
  · intro h a ha
    have hh := h (-(a:ℤ)) a ha rfl
    omega
  · intro h i a ha hi
    have hh := h a ha
    omega

def partsOfWord (w : Word) : List ℕ := w.reverse.map (fun i => (-i).toNat)

theorem partsOfWord_wordOfParts (l : List ℕ) : partsOfWord (wordOfParts l) = l := by
  simp [partsOfWord,wordOfParts,List.map_map,Function.comp_def]

theorem wordOfParts_partsOfWord (w : Word) (hw : ∀ i ∈ w, i ≤ 0) :
    wordOfParts (partsOfWord w) = w := by
  have hm : w.reverse.map (fun i => -(((-i).toNat:ℕ):ℤ)) = w.reverse := by
    trans w.reverse.map id
    · apply List.map_congr_left
      intro i hi
      have hh := hw i (List.mem_reverse.mp hi)
      dsimp only [id_eq]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    · exact List.map_id _
  simpa [partsOfWord,wordOfParts,List.map_map,Function.comp_def] using congrArg List.reverse hm

theorem wordOfParts_length (l : List ℕ) : (wordOfParts l).length = l.length := by
  simp [wordOfParts]

theorem wordOfParts_cons (a : ℕ) (l : List ℕ) :
    wordOfParts (a::l) = wordOfParts l ++ [-(a:ℤ)] := by
  simp [wordOfParts]

theorem wordOfParts_sum (l : List ℕ) : (wordOfParts l).sum = -(l.sum:ℤ) := by
  induction l with
  | nil => simp [wordOfParts]
  | cons a l ih => simp [wordOfParts_cons,ih,add_comm]

theorem partsOfWord_admissible (minimum : ℕ) (w : Word) (h : AdmissibleWord minimum w) :
    Admissible minimum (partsOfWord w) := by
  apply (wordOfParts_admissible minimum _).mp
  rw [wordOfParts_partsOfWord w (fun i hi => (admissibleWord_index_le minimum w h i hi).trans (by omega))]
  exact h

def wordEquiv (minimum : ℕ) : Partition minimum ≃ {w : Word // AdmissibleWord minimum w} where
  toFun p := ⟨wordOfParts p.val,(wordOfParts_admissible minimum p.val).mpr p.property⟩
  invFun w := ⟨partsOfWord w.val,partsOfWord_admissible minimum w.val w.property⟩
  left_inv p := Subtype.ext (partsOfWord_wordOfParts p.val)
  right_inv w := Subtype.ext (wordOfParts_partsOfWord w.val
    (fun i hi => (admissibleWord_index_le minimum w.val w.property i hi).trans (by omega)))

def NormalWords (minimum n : ℕ) := {w : Word // AdmissibleWord minimum w ∧ w.sum = -(n:ℤ)}

def fixedWeightWordEquiv (minimum n : ℕ) :
    {p : Partition minimum // p.val.sum = n} ≃ NormalWords minimum n where
  toFun p := ⟨wordOfParts p.val.val,(wordOfParts_admissible minimum _).mpr p.val.property,
    by rw [wordOfParts_sum,p.property]⟩
  invFun w := ⟨⟨partsOfWord w.val,partsOfWord_admissible minimum w.val w.property.1⟩,by
    change (partsOfWord w.val).sum = n
    have hs := wordOfParts_sum (partsOfWord w.val)
    rw [wordOfParts_partsOfWord w.val (fun i hi =>
      (admissibleWord_index_le minimum w.val w.property.1 i hi).trans (by omega)),w.property.2] at hs
    omega⟩
  left_inv p := Subtype.ext (Subtype.ext (partsOfWord_wordOfParts p.val.val))
  right_inv w := Subtype.ext (wordOfParts_partsOfWord w.val
    (fun i hi => (admissibleWord_index_le minimum w.val w.property.1 i hi).trans (by omega)))

theorem normalWords_card (minimum n : ℕ) : Nat.card (NormalWords minimum n) = count minimum n :=
  Nat.card_congr (fixedWeightWordEquiv minimum n).symm

theorem normalWords_finite (minimum n : ℕ) (hm : 1 ≤ minimum) : Finite (NormalWords minimum n) := by
  letI := finite_fixedWeight minimum hm n
  exact Finite.of_equiv _ (fixedWeightWordEquiv minimum n)

end KanadeRussell.Partitions
