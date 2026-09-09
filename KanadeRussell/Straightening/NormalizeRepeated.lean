import KanadeRussell.Straightening.PairCoefficients
import KanadeRussell.Straightening.SpanTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-! Normalization of the repeated-pair relation at a finite common cutoff. -/
namespace KanadeRussell.Straightening
open Tsuchioka PowerSeries
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem repeated_combination_eq (w : K) (hw : w^4-w^2+1 = 0)
    (value : Word → V) (a : ℤ) (N : ℕ) :
    symmetricSum value (fun p => coeff p (Scalar.G w 1)) a a N -
      (Coefficients.tCoeff w/Coefficients.mCoeff w) •
        symmetricSum value (fun p => coeff p (Scalar.G w 2)) a a N =
    (2*(1-Coefficients.tCoeff w/Coefficients.mCoeff w)) •
      ∑ p ∈ Finset.range N, repeatedCoeff w p • value [a-p,a+p] := by
  have hc (p : ℕ) : (2*(1-Coefficients.tCoeff w/Coefficients.mCoeff w))*repeatedCoeff w p =
      2*(coeff p (Scalar.G w 1)-(Coefficients.tCoeff w/Coefficients.mCoeff w)*coeff p (Scalar.G w 2)) := by
    have hh := div_mul_cancel₀
      (coeff p (Scalar.G w 1)-(Coefficients.tCoeff w/Coefficients.mCoeff w)*coeff p (Scalar.G w 2))
      (repeated_denominator_ne_zero w hw)
    unfold repeatedCoeff
    linear_combination 2*hh
  simp only [symmetricSum,Finset.smul_sum,smul_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hc]
  module

/-- The combined concrete G2/G3 identity is enough; no normalized relation is assumed. -/
theorem repeated_expansion_of_combined_relation (ρ : HighestWeightAction K V) (w : K)
    (hw : w^4-w^2+1 = 0) (a : ℤ)
    (relations : ∀ t, ∃ N : ℕ,
      symmetricSum (fun u => ρ.wordValue (u ++ t)) (fun p => coeff p (Scalar.G w 1)) a a (N+2) -
        (Coefficients.tCoeff w/Coefficients.mCoeff w) •
          symmetricSum (fun u => ρ.wordValue (u ++ t)) (fun p => coeff p (Scalar.G w 2)) a a (N+2) ∈
            shorterSpan (K := K) (fun u => ρ.wordValue (u ++ t)) [a,a]) :
    PairExpansion ρ a a (repeatedCoeff w) := by
  intro t
  obtain ⟨N,hN⟩ := relations t
  rw [repeated_combination_eq w hw] at hN
  have hscalar : 2*(1-Coefficients.tCoeff w/Coefficients.mCoeff w) ≠ 0 :=
    mul_ne_zero (by norm_num) (repeated_denominator_ne_zero w hw)
  have hh := ((shorterSpan (K := K) (fun u => ρ.wordValue (u ++ t)) [a,a]).smul_mem_iff hscalar).mp hN
  refine ⟨N,?_⟩
  rw [show N+2 = (N+1)+1 by omega,Finset.sum_range_succ'] at hh
  simpa only [repeatedCoeff_zero w hw,Nat.cast_zero,sub_zero,add_zero,one_smul,add_comm] using hh

end KanadeRussell.Straightening
