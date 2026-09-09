import KanadeRussell.Tsuchioka.SourceCoefficients
import KanadeRussell.Tsuchioka.OrderingReduction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-! Normalized pair coefficients computed from the actual source series. -/
namespace KanadeRussell.Straightening
open Tsuchioka PowerSeries
variable {K : Type*} [Field K] [CharZero K]

noncomputable def repeatedCoeff (w : K) (n : ℕ) : K :=
  (coeff n (Scalar.G w 1) - (Coefficients.tCoeff w / Coefficients.mCoeff w)*coeff n (Scalar.G w 2)) /
    (1 - Coefficients.tCoeff w / Coefficients.mCoeff w)

theorem repeated_denominator_ne_zero (w : K) (hw : w^4-w^2+1 = 0) :
    1-Coefficients.tCoeff w/Coefficients.mCoeff w ≠ 0 := by
  rw [Coefficients.tm_ratio w hw]
  intro h
  apply Coefficients.f2_ne_zero w hw
  linear_combination 2*h

theorem repeatedCoeff_zero (w : K) (hw : w^4-w^2+1 = 0) : repeatedCoeff w 0 = 1 := by
  simp only [repeatedCoeff,Scalar.coeff_zero_G,mul_one]
  exact div_self (repeated_denominator_ne_zero w hw)

theorem repeatedCoeff_one (w : K) (hw : w^4-w^2+1 = 0) :
    repeatedCoeff w 1 = (3+2*w-w^3)/3 := by
  apply (div_eq_iff (repeated_denominator_ne_zero w hw)).mpr
  rw [Scalar.coeff_one_G2 w hw,Scalar.coeff_one_G3 w hw,Coefficients.tm_ratio w hw]
  linear_combination (w^2-3)*hw

theorem repeatedCoeff_one_ne_zero (w : K) (hw : w^4-w^2+1 = 0) : repeatedCoeff w 1 ≠ 0 := by
  rw [repeatedCoeff_one w hw]
  convert Coefficients.f5_ne_zero w hw using 1; ring

/-- Reversed quadratic terms are reindexed at n >= a-b. -/
noncomputable def orderingCoeff (w : K) (a b : ℤ) (n : ℕ) : K :=
  (symmetricPhase w a b*coeff n (Scalar.G w 0) - skewPhase w a b*coeff n (Scalar.G w 1) -
    if (a-b).toNat ≤ n then
      symmetricPhase w a b*coeff (n-(a-b).toNat) (Scalar.G w 0) +
        skewPhase w a b*coeff (n-(a-b).toNat) (Scalar.G w 1) else 0) /
    (symmetricPhase w a b-skewPhase w a b)

theorem ordering_denominator_ne_zero (w : K) (hw : w^4-w^2+1 = 0) (a b : ℤ)
    (hne : (a-b)%12 ≠ 7) : symmetricPhase w a b-skewPhase w a b ≠ 0 := by
  intro h
  apply hne
  apply (Coefficients.orderingLeading_eq_zero_iff w hw a b).mp
  exact h

theorem orderingCoeff_zero (w : K) (hw : w^4-w^2+1 = 0) (a b : ℤ)
    (hab : b < a) (hne : (a-b)%12 ≠ 7) : orderingCoeff w a b 0 = 1 := by
  have hp : ¬(a-b).toNat ≤ 0 := by omega
  simp only [orderingCoeff,if_neg hp,Scalar.coeff_zero_G,mul_one,sub_zero]
  exact div_self (ordering_denominator_ne_zero w hw a b hne)

theorem orderingCoeff_one_gap_two (w : K) (hw : w^4-w^2+1 = 0) (a b : ℤ)
    (hg : a-b = 2) : orderingCoeff w a b 1 = w*(2-w^2)/3 := by
  have hp : ¬(a-b).toNat ≤ 1 := by omega
  unfold orderingCoeff
  rw [if_neg hp,sub_zero]
  apply (div_eq_iff (ordering_denominator_ne_zero w hw a b (by omega))).mpr
  rw [Scalar.coeff_one_G1 w hw,Scalar.coeff_one_G2 w hw]
  have hx : w^(4*a+9*b) = w^b*w^(8:ℕ) := by
    rw [(Coefficients.ordering_phase_factor w hw a b).1,hg]
    norm_num [zpow_natCast, zpow_ofNat, Int.toNat]
  have hy : w^(9*a+4*b) = w^b*w^(6:ℕ) := by
    rw [(Coefficients.ordering_phase_factor w hw a b).2,hg]
    norm_num only [Int.reduceMul]
    rw [Coefficients.zpow_mod_twelve w hw 18]
    norm_num [zpow_natCast, zpow_ofNat, Int.toNat]
  simp only [symmetricPhase,skewPhase,hx,hy]
  linear_combination w^b*(-76*w^10-104*w^9+152*w^8+208*w^7+48*w^6)*hw

theorem orderingCoeff_one_gap_two_ne_zero (w : K) (hw : w^4-w^2+1 = 0) (a b : ℤ)
    (hg : a-b = 2) : orderingCoeff w a b 1 ≠ 0 := by
  rw [orderingCoeff_one_gap_two w hw a b hg]
  convert Coefficients.f4_ne_zero w hw using 1; ring

/-- The adjacent combination includes the reversed terms shifted by one index. -/
noncomputable def adjacentCoeff (w : K) (n : ℕ) : K :=
  let r := Coefficients.tCoeff w/Coefficients.mCoeff w
  let g := coeff 0 (Scalar.G6 w)
  (g*(coeff n (Scalar.G w 1)-r*coeff n (Scalar.G w 2)) +
    (1-r)*coeff n (Scalar.G6 w) +
    g*(coeff (n+1) (Scalar.G w 1)-r*coeff (n+1) (Scalar.G w 2)) -
    (1-r)*coeff (n+1) (Scalar.G6 w))/(8*r)

theorem adjacent_denominator_ne_zero (w : K) (hw : w^4-w^2+1 = 0) :
    8*(Coefficients.tCoeff w/Coefficients.mCoeff w) ≠ 0 := by
  rw [Coefficients.tm_ratio w hw]
  convert Coefficients.f3_ne_zero w hw using 1; ring

theorem adjacentCoeff_zero (w : K) (hw : w^4-w^2+1 = 0) : adjacentCoeff w 0 = 1 := by
  unfold adjacentCoeff
  apply (div_eq_iff (adjacent_denominator_ne_zero w hw)).mpr
  simp only [Nat.zero_add,Scalar.coeff_zero_G,Scalar.coeff_zero_G6,mul_one,
    Scalar.coeff_one_G2 w hw,Scalar.coeff_one_G3 w hw,Scalar.coeff_one_G6 w hw,one_mul]
  have hh := Coefficients.f3_coefficient_from_ratios w hw
  rw [Coefficients.tm_ratio w hw] at hh ⊢
  linear_combination hh

end KanadeRussell.Straightening
