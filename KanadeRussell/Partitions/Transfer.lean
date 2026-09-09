import KanadeRussell.Source.LengthSeries
import KanadeRussell.Partitions.Blocks
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! The three-state block transfer system and uniqueness in every degree. -/
open PowerSeries
namespace KanadeRussell.Partitions
open Infra

noncomputable def transition : Fin 3 → Fin 3 → PowerSeries QSeries :=
  ![![1+monomial 1 q+monomial 1 (q^2)+monomial 2 (q^3),
      monomial 1 (q^3)+monomial 2 (q^4), monomial 2 (q^6)],
    ![1+monomial 1 (q^2), monomial 1 (q^3), monomial 2 (q^6)],
    ![1, monomial 1 (q^3), monomial 2 (q^6)]]

/-- The matrix entries are exactly the admissible initial-block weights. -/
theorem transition_eq_blocks (i j : Fin 3) : transition i j =
    ∑ b : Fin 7, if (∀ a ∈ block b, i.val+1 ≤ a) ∧ nextMinimum b = j.val+1
      then monomial (block b).length (q^(block b).sum) else 0 := by
  classical
  fin_cases i <;> fin_cases j <;>
    norm_num [transition, block, nextMinimum, Fin.sum_univ_succ]; ring

def TransferSystem (F : Fin 3 → PowerSeries QSeries) : Prop :=
  ∀ i, F i = ∑ j, transition i j*rescale (q^3) (F j)

noncomputable def sources : Fin 3 → PowerSeries QSeries :=
  ![Source.LengthSeries.T 0 0, Source.LengthSeries.T 1 3, Source.LengthSeries.T 2 3]

theorem sources_transfer : TransferSystem sources := by
  intro i
  fin_cases i
  · simpa [sources, transition, Fin.sum_univ_succ, add_assoc] using Source.LengthSeries.first_recurrence
  · simpa [sources, transition, Fin.sum_univ_succ, add_assoc] using Source.LengthSeries.second_recurrence
  · simpa [sources, transition, Fin.sum_univ_succ, add_assoc] using Source.LengthSeries.third_recurrence

theorem transition_constant (i j : Fin 3) : constantCoeff (transition i j) = if j = 0 then 1 else 0 := by
  have hm (k : ℕ) (x : QSeries) (hk : k ≠ 0) : constantCoeff (monomial k x) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial]
    simp [Ne.symm hk]
  fin_cases i <;> fin_cases j <;> simp [transition, hm]

private theorem coeff_mul_rescale_of_lower_zero (p f : PowerSeries QSeries) (r : QSeries) (n : ℕ)
    (h : ∀ k < n, coeff k f = 0) :
    coeff n (p*rescale r f) = constantCoeff p*r^n*coeff n f := by
  rw [coeff_mul, Finset.sum_eq_single (0,n)]
  · simp [coeff_rescale, mul_assoc]
  · intro ij hij hne
    have hs := Finset.mem_antidiagonal.mp hij
    have hi : ij.2 < n := by
      by_contra hlt
      apply hne
      apply Prod.ext <;> simp only <;> omega
    simp [coeff_rescale, h _ hi]
  · simp

theorem transfer_eq_zero (F : Fin 3 → PowerSeries QSeries) (hF : TransferSystem F)
    (h0 : ∀ i, constantCoeff (F i) = 0) : F = 0 := by
  have hall : ∀ n i, coeff n (F i) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n
        simpa only [coeff_zero_eq_constantCoeff] using h0
      have hc (i : Fin 3) : coeff n (F i) = (q^3)^n*coeff n (F 0) := by
        have hh := congrArg (coeff n) (hF i)
        rw [map_sum] at hh
        simp only [coeff_mul_rescale_of_lower_zero _ _ _ n (fun k hk => ih k hk _),
          transition_constant] at hh
        simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh
      have hz : (1-(q^3)^n)*coeff n (F 0) = 0 := by linear_combination hc 0
      have hr : 1-(q^3)^n ≠ 0 := by
        intro h
        have hh := congrArg constantCoeff h
        simp [q, hn] at hh
      have hf := (mul_eq_zero.mp hz).resolve_left hr
      intro i
      rw [hc i, hf, mul_zero]
  funext i
  apply PowerSeries.ext
  intro n
  exact (hall n i).trans (map_zero _).symm

/-- The initial constants determine the complete solution, not just a bounded truncation. -/
theorem transfer_unique (F G : Fin 3 → PowerSeries QSeries)
    (hF : TransferSystem F) (hG : TransferSystem G)
    (h0 : ∀ i, constantCoeff (F i) = constantCoeff (G i)) : F = G := by
  have hs : TransferSystem (F-G) := by
    intro i
    simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
    exact congrArg₂ (·-·) (hF i) (hG i)
  have hz := transfer_eq_zero (F-G) hs (fun i => by simpa using sub_eq_zero.mpr (h0 i))
  exact sub_eq_zero.mp hz

end KanadeRussell.Partitions
