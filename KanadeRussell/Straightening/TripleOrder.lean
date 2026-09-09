import KanadeRussell.Tsuchioka.LocalReduction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Strict word comparisons needed in the three overlap reductions. -/
namespace KanadeRussell.Straightening
open Tsuchioka

theorem higher_triple (x y z a b c : ℤ) (hs : x+y+z = a+b+c)
    (h2 : b+c ≤ y+z) (h3 : c ≤ z) (hne : y+z ≠ b+c ∨ z ≠ c) :
    Higher [x,y,z] [a,b,c] := by
  right
  refine ⟨?_,?_⟩
  · intro he
    simp only [List.cons.injEq] at he
    rcases hne with hne | hne <;> simp_all
  · simp only [suffixSums,List.sum_cons,List.sum_nil,add_zero]
    exact .cons (by omega) (.cons h2 (.cons h3 .nil))

private theorem higher_pair_coordinates (x y a b : ℤ) (h : Higher [x,y] [a,b])
    (hs : x+y = a+b) : b < y ∧ x < a := by
  rcases h with h | ⟨hne,h⟩
  · simp at h
  · have hy : b ≤ y := by
      cases h with
      | cons htot ht => cases ht with
        | cons hy _ => simpa using hy
    have hn : x ≠ a ∨ y ≠ b := by
      by_contra hh
      push Not at hh
      exact hne (by simp [hh.1,hh.2])
    omega

/-- A strict improvement of the right pair crosses the required triple boundary. -/
theorem higher_right_pair_overlap (a c : ℤ) (p : ℕ) (hp : 0 < p) (u : Word)
    (hu : Higher u [a+1+p,c-1]) (hs : u.sum = (a+1+p)+(c-1)) :
    Higher ((a-p)::u) [a,a,c] := by
  rcases hu with hlen | hhigh
  · left
    simp only [List.length_cons,List.length_nil] at hlen ⊢
    omega
  · have hlen := hhigh.2.length_eq
    simp only [suffixSums_length] at hlen
    cases u with
    | nil => simp at hlen
    | cons x u =>
      cases u with
      | nil => simp at hlen
      | cons y u =>
        cases u with
        | cons z u => simp at hlen
        | nil =>
          simp only [List.sum_cons,List.sum_nil,add_zero] at hs
          obtain ⟨hy,hx⟩ := higher_pair_coordinates x y (a+1+p) (c-1) (Or.inr hhigh) hs
          apply higher_triple <;> omega

/-- The corresponding strict comparison when the left pair is improved. -/
theorem higher_left_pair_overlap (a : ℤ) (p : ℕ) (hp : 0 < p) (u : Word)
    (hu : Higher u [a-1,a-1-p]) (hs : u.sum = (a-1)+(a-1-p)) :
    Higher (u ++ [a+p]) [a-2,a,a] := by
  rcases hu with hlen | hhigh
  · left
    simp only [List.length_cons,List.length_nil,List.length_append] at hlen ⊢
    omega
  · have hlen := hhigh.2.length_eq
    simp only [suffixSums_length] at hlen
    cases u with
    | nil => simp at hlen
    | cons x u =>
      cases u with
      | nil => simp at hlen
      | cons y u =>
        cases u with
        | cons z u => simp at hlen
        | nil =>
          simp only [List.sum_cons,List.sum_nil,add_zero] at hs
          obtain ⟨hy,hx⟩ := higher_pair_coordinates x y (a-1) (a-1-p) (Or.inr hhigh) hs
          apply higher_triple <;> omega

end KanadeRussell.Straightening
