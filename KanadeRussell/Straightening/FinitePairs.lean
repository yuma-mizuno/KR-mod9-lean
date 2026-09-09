import KanadeRussell.Straightening.SpanTransport
import Mathlib.Algebra.BigOperators.Finprod
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Quadratic sums on highest-weight suffixes have finite support. -/
namespace KanadeRussell.Straightening
open Tsuchioka
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mode_zero_above_grade (ρ : HighestWeightAction K V) (i d : ℤ) (x : V)
    (hx : x ∈ ρ.grade d) (hi : d < i) : ρ.mode i x = 0 := by
  have hm := ρ.mode_mem i d x hx
  rw [ρ.negative (d-i) (by omega), Submodule.mem_bot] at hm
  exact hm

theorem pair_tails_zero (ρ : HighestWeightAction K V) (a b : ℤ) (t : Word) :
    ∃ N : ℕ, ∀ p : ℕ, N ≤ p →
      ρ.wordValue ([a-p,b+p] ++ t) = 0 ∧
      ρ.wordValue ([b-p,a+p] ++ t) = 0 := by
  let d : ℤ := -t.sum
  refine ⟨(max (d-a) (d-b)).toNat+1, ?_⟩
  intro p hp
  have ht : ρ.wordValue t ∈ ρ.grade d := ρ.wordValue_mem t
  have ha := mode_zero_above_grade ρ (a+p) d _ ht (by omega)
  have hb := mode_zero_above_grade ρ (b+p) d _ ht (by omega)
  constructor <;>
    simp only [List.cons_append, List.nil_append, HighestWeightAction.wordValue]
  · rw [hb, map_zero]
  · rw [ha, map_zero]

noncomputable def pairSum (ρ : HighestWeightAction K V) (c : ℕ → K)
    (a b : ℤ) (t : Word) : V :=
  ∑ᶠ p : ℕ, c p • ρ.wordValue ([a-p,b+p] ++ t)

theorem pairSum_eq_sum (ρ : HighestWeightAction K V) (c : ℕ → K)
    (a b : ℤ) (t : Word) (N : ℕ)
    (hN : ∀ p : ℕ, N ≤ p → ρ.wordValue ([a-p,b+p] ++ t) = 0) :
    pairSum ρ c a b t = ∑ p ∈ Finset.range N, c p • ρ.wordValue ([a-p,b+p] ++ t) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro p hp
  apply Finset.mem_range.mpr
  by_contra h
  exact hp (by simp only [hN p (by omega), smul_zero])

theorem pairSum_finite_support (ρ : HighestWeightAction K V) (c : ℕ → K)
    (a b : ℤ) (t : Word) :
    (Function.support (fun p : ℕ => c p • ρ.wordValue ([a-p,b+p] ++ t))).Finite := by
  obtain ⟨N,hN⟩ := pair_tails_zero ρ a b t
  apply (Finset.finite_toSet (Finset.range N)).subset
  intro p hp
  apply Finset.mem_range.mpr
  by_contra h
  exact hp (by simp only [(hN p (by omega)).1, smul_zero])

theorem pairSum_add (ρ : HighestWeightAction K V) (c e : ℕ → K)
    (a b : ℤ) (t : Word) :
    pairSum ρ (fun p => c p + e p) a b t = pairSum ρ c a b t + pairSum ρ e a b t := by
  obtain ⟨N,hN⟩ := pair_tails_zero ρ a b t
  simp only [pairSum_eq_sum ρ _ a b t N (fun p hp => (hN p hp).1), add_smul,
    Finset.sum_add_distrib]

theorem pairSum_smul (ρ : HighestWeightAction K V) (r : K) (c : ℕ → K)
    (a b : ℤ) (t : Word) :
    pairSum ρ (fun p => r*c p) a b t = r • pairSum ρ c a b t := by
  obtain ⟨N,hN⟩ := pair_tails_zero ρ a b t
  simp only [pairSum_eq_sum ρ _ a b t N (fun p hp => (hN p hp).1),
    Finset.smul_sum, smul_smul]

theorem pairSum_sub (ρ : HighestWeightAction K V) (c e : ℕ → K)
    (a b : ℤ) (t : Word) :
    pairSum ρ (fun p => c p - e p) a b t = pairSum ρ c a b t - pairSum ρ e a b t := by
  obtain ⟨N,hN⟩ := pair_tails_zero ρ a b t
  simp only [pairSum_eq_sum ρ _ a b t N (fun p hp => (hN p hp).1), sub_smul,
    Finset.sum_sub_distrib]

/-- An identity of the finite-supported sums supplies every finite pair expansion. -/
theorem pairExpansion_of_pairSum (ρ : HighestWeightAction K V) (a b : ℤ) (c : ℕ → K)
    (hc : c 0 = 1)
    (h : ∀ t, pairSum ρ c a b t ∈
      shorterSpan (K := K) (fun u => ρ.wordValue (u ++ t)) [a,b]) :
    PairExpansion ρ a b c := by
  intro t
  obtain ⟨N,hN⟩ := pair_tails_zero ρ a b t
  have hh := h t
  rw [pairSum_eq_sum ρ c a b t (N+2) (fun p hp => (hN p (by omega)).1)] at hh
  refine ⟨N, ?_⟩
  rw [show N+2 = (N+1)+1 by omega, Finset.sum_range_succ'] at hh
  simpa only [hc, Nat.cast_zero, sub_zero, add_zero, one_smul, add_comm] using hh

/-- Reindexing by a natural shift retains every endpoint explicitly. -/
theorem finsum_shift (f : ℕ → V) (k : ℕ) :
    (∑ᶠ n : ℕ, if k ≤ n then f (n-k) else 0) = ∑ᶠ p : ℕ, f p := by
  have hr : Set.range (fun p : ℕ => k+p) = {n : ℕ | k ≤ n} := by
    ext n
    constructor
    · rintro ⟨p,rfl⟩; change k ≤ k+p; omega
    · intro hn; change k ≤ n at hn; exact ⟨n-k, by dsimp; omega⟩
  have hh := finsum_mem_range (f := fun n : ℕ => f (n-k))
    (g := fun p : ℕ => k+p) (by intro p q h; dsimp at h; omega)
  rw [hr, finsum_mem_def] at hh
  simpa [Set.indicator] using hh

theorem pairSum_reverse (ρ : HighestWeightAction K V) (c : ℕ → K)
    (a b : ℤ) (hab : b ≤ a) (t : Word) :
    pairSum ρ c b a t =
      pairSum ρ (fun n => if (a-b).toNat ≤ n then c (n-(a-b).toNat) else 0) a b t := by
  let k := (a-b).toNat
  have hk : (k : ℤ) = a-b := Int.toNat_of_nonneg (by omega)
  rw [pairSum, pairSum]
  rw [← finsum_shift (fun p : ℕ => c p • ρ.wordValue ([b-p,a+p] ++ t)) k]
  apply finsum_congr
  intro n
  change (if k ≤ n then c (n-k) • ρ.wordValue ([b-(n-k:ℕ),a+(n-k:ℕ)] ++ t) else 0) =
    (if k ≤ n then c (n-k) else 0) • ρ.wordValue ([a-n,b+n] ++ t)
  by_cases hn : k ≤ n
  · simp only [if_pos hn]
    have he : [b-(n-k:ℕ),a+(n-k:ℕ)] = [a-n,b+n] := by
      simp only [Nat.cast_sub hn]
      have h1 : b-((n:ℤ)-k) = a-n := by omega
      have h2 : a+((n:ℤ)-k) = b+n := by omega
      rw [h1,h2]
    rw [he]
  · simp only [if_neg hn, zero_smul]

theorem pairSum_succ_split (ρ : HighestWeightAction K V) (c : ℕ → K)
    (a b : ℤ) (t : Word) :
    pairSum ρ c a b t = c 0 • ρ.wordValue ([a,b] ++ t) +
      pairSum ρ (fun p => c (p+1)) (a-1) (b+1) t := by
  have he (p : ℕ) : [a-(p+1:ℕ),b+(p+1:ℕ)] = [(a-1)-p,(b+1)+p] := by
    push_cast
    have h1 : a-((p:ℤ)+1) = (a-1)-p := by ring
    have h2 : b+((p:ℤ)+1) = (b+1)+p := by ring
    rw [h1,h2]
  obtain ⟨N,hN⟩ := pair_tails_zero ρ a b t
  rw [pairSum_eq_sum ρ c a b t (N+1) (fun p hp => (hN p (by omega)).1)]
  rw [pairSum_eq_sum ρ (fun p => c (p+1)) (a-1) (b+1) t N (by
    intro p hp
    rw [← he]
    exact (hN (p+1) (by omega)).1)]
  rw [Finset.sum_range_succ']
  simp only [he, Nat.cast_zero, sub_zero, add_zero, add_comm]

end KanadeRussell.Straightening
