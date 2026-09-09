import KanadeRussell.Tsuchioka.LocalReduction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Transport of finite homogeneous spans into a prescribed word comparison. -/
namespace KanadeRussell.Straightening
open Tsuchioka
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def shorterSpan (value : Word → V) (w : Word) : Submodule K V :=
  Submodule.span K (value '' {u | u.length < w.length ∧ u.sum = w.sum})

theorem span_context (ρ : HighestWeightAction K V) (s r t target : Word) (P : Set Word)
    (horder : ∀ u ∈ P, Higher (s ++ u ++ r) target ∧ (s ++ u ++ r).sum = target.sum)
    (x : V) (hx : x ∈ Submodule.span K ((fun u => ρ.wordValue (u ++ r ++ t)) '' P)) :
    ρ.wordOperator s x ∈ higherSpan (K := K) (fun u => ρ.wordValue (u ++ t)) target := by
  let S := higherSpan (K := K) (fun u => ρ.wordValue (u ++ t)) target
  change ρ.wordOperator s x ∈ S
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u,hu,rfl⟩ := hy
    have hh := horder u hu
    have hm := mem_higherSpan (K := K) (fun u => ρ.wordValue (u ++ t)) hh.1 hh.2
    rw [← ρ.wordValue_append]
    simpa [List.append_assoc,S] using hm
  | zero => simp
  | add x y hx hy hix hiy => simpa using S.add_mem hix hiy
  | smul c x hx hi => simpa using S.smul_mem c hi

theorem shorter_context (ρ : HighestWeightAction K V) (s r t target : Word) (a b : ℤ)
    (hlen : s.length+2+r.length = target.length)
    (hsum : s.sum+(a+b)+r.sum = target.sum)
    (x : V) (hx : x ∈ shorterSpan (K := K) (fun u => ρ.wordValue (u ++ r ++ t)) [a,b]) :
    ρ.wordOperator s x ∈ higherSpan (K := K) (fun u => ρ.wordValue (u ++ t)) target := by
  apply span_context ρ s r t target _ ?_ x hx
  intro u hu
  change u.length < [a,b].length ∧ u.sum = [a,b].sum at hu
  simp only [List.length_cons,List.length_nil,List.sum_cons,List.sum_nil,add_zero] at hu
  constructor
  · left
    simp only [List.length_append]
    omega
  · simp only [List.sum_append]
    omega

/-- A finite normalized two-mode identity modulo strictly shorter homogeneous words.
The cutoff may depend on the suffix, and every displayed scalar coefficient is retained. -/
def PairExpansion (ρ : HighestWeightAction K V) (a b : ℤ) (c : ℕ → K) : Prop :=
  ∀ t, ∃ N : ℕ,
    ρ.wordValue ([a,b] ++ t) +
      ∑ p ∈ Finset.range (N+1), c (p+1) • ρ.wordValue ([a-(p+1:ℕ),b+(p+1:ℕ)] ++ t) ∈
        shorterSpan (K := K) (fun u => ρ.wordValue (u ++ t)) [a,b]

theorem PairExpansion.in_context {ρ : HighestWeightAction K V} {a b : ℤ} {c : ℕ → K}
    (h : PairExpansion ρ a b c) (s r t target : Word)
    (hlen : s.length+2+r.length = target.length)
    (hsum : s.sum+(a+b)+r.sum = target.sum) :
    ∃ N : ℕ, ρ.wordValue ((s ++ [a,b] ++ r) ++ t) +
      ∑ p ∈ Finset.range (N+1), c (p+1) •
        ρ.wordValue ((s ++ [a-(p+1:ℕ),b+(p+1:ℕ)] ++ r) ++ t) ∈
          higherSpan (K := K) (fun u => ρ.wordValue (u ++ t)) target := by
  obtain ⟨N,hN⟩ := h (r ++ t)
  have hh := shorter_context ρ s r t target a b hlen hsum _
    (by simpa only [List.append_assoc] using hN)
  refine ⟨N,?_⟩
  simpa only [map_add,map_sum,map_smul,← ρ.wordValue_append,List.append_assoc] using hh

/-- Every normalized pair expansion also gives its ordinary higher-word reduction. -/
theorem PairExpansion.localReduction {ρ : HighestWeightAction K V} {a b : ℤ} {c : ℕ → K}
    (h : PairExpansion ρ a b c) : ρ.LocalReduction [a,b] := by
  intro t
  let value (u : Word) := ρ.wordValue (u ++ t)
  let S := higherSpan (K := K) value [a,b]
  obtain ⟨N,hN⟩ := h t
  have hs : shorterSpan (K := K) value [a,b] ≤ S := by
    apply Submodule.span_mono
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨u,⟨Or.inl hu.1,hu.2⟩,rfl⟩
  have htail : (∑ p ∈ Finset.range (N+1),
      c (p+1) • value [a-(p+1:ℕ),b+(p+1:ℕ)]) ∈ S := by
    apply S.sum_mem
    intro p hp
    apply S.smul_mem
    apply mem_higherSpan value (higher_pair_shift a b (p+1) (by omega))
    simp only [List.sum_cons,List.sum_nil,add_zero]
    omega
  simpa [value,S] using S.sub_mem (hs hN) htail

end KanadeRussell.Straightening
