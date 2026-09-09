import Mathlib.Algebra.Module.End
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Algebraic sums of operator families that eventually vanish on each vector. -/
namespace KanadeRussell.Representation
variable {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]

private theorem cutoff_sum_eq (A : ℕ → Module.End K V) (v : V) (N M : ℕ)
    (hN : ∀ n ≥ N, A n v=0) (hM : ∀ n ≥ M, A n v=0) :
    (∑ n ∈ Finset.range N, A n v) = ∑ n ∈ Finset.range M, A n v := by
  have hle (a b : ℕ) (hab : a ≤ b) (ha : ∀ n ≥ a, A n v=0) :
      (∑ n ∈ Finset.range a, A n v) = ∑ n ∈ Finset.range b, A n v := by
    apply Finset.sum_subset (Finset.range_mono hab)
    intro n hn hna
    exact ha n (by simpa using hna)
  rcases le_total N M with h | h
  · exact hle N M h hN
  · exact (hle M N h hM).symm

noncomputable def locallyFiniteOperatorSum (A : ℕ → Module.End K V)
    (hA : ∀ v, ∃ N, ∀ n ≥ N, A n v=0) : Module.End K V := by
  let cutoff := fun v => Classical.choose (hA v)
  have hc (v) : ∀ n ≥ cutoff v, A n v=0 := Classical.choose_spec (hA v)
  let f := fun v => ∑ n ∈ Finset.range (cutoff v), A n v
  have hf (v) (N) (hN : ∀ n ≥ N, A n v=0) : f v = ∑ n ∈ Finset.range N, A n v :=
    cutoff_sum_eq A v _ N (hc v) hN
  refine { toFun := f, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    let N := max (cutoff v) (cutoff w)
    have hv : ∀ n ≥ N, A n v=0 := fun n hn => hc v n (le_trans (le_max_left _ _) hn)
    have hw : ∀ n ≥ N, A n w=0 := fun n hn => hc w n (le_trans (le_max_right _ _) hn)
    rw [hf v N hv, hf w N hw, hf (v+w) N (by intro n hn; simp [hv n hn, hw n hn])]
    simp [Finset.sum_add_distrib]
  · intro c v
    rw [hf (c • v) (cutoff v) (by intro n hn; simp [hc v n hn])]
    simp [f, Finset.smul_sum]

theorem locallyFiniteOperatorSum_apply_eq_sum (A : ℕ → Module.End K V)
    (hA : ∀ v, ∃ N, ∀ n ≥ N, A n v=0) (v : V) (N : ℕ)
    (hN : ∀ n ≥ N, A n v=0) :
    locallyFiniteOperatorSum A hA v = ∑ n ∈ Finset.range N, A n v := by
  exact cutoff_sum_eq A v _ N (Classical.choose_spec (hA v)) hN

theorem locallyFiniteOperatorSum_apply_eq_zero (A : ℕ → Module.End K V)
    (hA : ∀ v, ∃ N, ∀ n ≥ N, A n v=0) (v : V) (hv : ∀ n, A n v=0) :
    locallyFiniteOperatorSum A hA v = 0 := by
  rw [locallyFiniteOperatorSum_apply_eq_sum A hA v 0 (fun n _ => hv n)]
  simp

end KanadeRussell.Representation
