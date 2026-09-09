import KanadeRussell.Source.Anchors
import KanadeRussell.Infra.Exponents
set_option backward.isDefEq.respectTransparency false

/-! Euler's identity with nonnegative exponents, Appendix E.1. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell.Infra

noncomputable def eulerAltTerm (ν : ℤ) (n : ℕ) : PowerSeries ℤ :=
  (-1) ^ n * X ^ triangular ((n : ℤ) - ν) * bInv (X; X)_n

noncomputable def eulerAlt (ν : ℤ) : PowerSeries ℤ := ∑' n, eulerAltTerm ν n

theorem summable_eulerAltTerm (ν : ℤ) : Summable (eulerAltTerm ν) := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (2 * (ν.natAbs + k + 1) + 1))).subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have ht := twice_triangular ((n : ℤ) - ν)
  have hn' : (2 : ℤ) * (ν.natAbs + k + 1) < n := by omega
  have hν : ν ≤ (ν.natAbs : ℤ) := Int.le_natAbs
  have hh : (k : ℤ) + 1 ≤ (n : ℤ) - ν := by omega
  have htri : k < triangular ((n : ℤ) - ν) := by
    have : (k : ℤ) < triangular ((n : ℤ) - ν) := by nlinarith
    exact_mod_cast this
  apply hn
  change coeff k (eulerAltTerm ν n) = 0
  rw [eulerAltTerm, mul_comm ((-1 : PowerSeries ℤ) ^ n), mul_assoc,
    coeff_X_pow_mul', if_neg (by omega)]

/-- The cancellation needed to shift the Euler summation index. -/
theorem bInv_factorial_step (n : ℕ) :
    (1 - (X : PowerSeries ℤ) ^ (n + 1)) * bInv (X; X)_(n + 1) = bInv (X; X)_n := by
  have hu := isUnit_qPochhammer_q 0 n
  have hnext := (isUnit_qPochhammer_q 0 (n + 1)).mul_bInv_cancel
  simp only [Nat.zero_add, pow_one, q] at hu hnext
  have hp : ((X : PowerSeries ℤ); X)_n * ((1 - X ^ (n + 1)) * bInv (X; X)_(n + 1)) = 1 := by
    simpa only [qPochhammer_succ', pow_succ', mul_assoc] using hnext
  have hcancel := congrArg (fun z : PowerSeries ℤ => bInv ((X; X)_n : PowerSeries ℤ) * z) hp
  simpa only [← mul_assoc, hu.bInv_mul_cancel, one_mul, mul_one] using hcancel

/-- Shift identity before summation; all powers of `X` are natural. -/
theorem eulerAltTerm_step (ν n : ℕ) :
    eulerAltTerm (ν + 1) (n + 1) + eulerAltTerm ν n =
      X ^ ν * eulerAltTerm ν (n + 1) := by
  have he := triangular_step (n + 1) ν
  have hp : (X : PowerSeries ℤ) ^ ν * X ^ triangular (((n + 1 : ℕ) : ℤ) - ν) =
      X ^ (n + 1) * X ^ triangular (((n + 1 : ℕ) : ℤ) - (ν + 1)) := by
    simp only [← pow_add]
    congr 1
    omega
  have hc := bInv_factorial_step n
  have hs := triangular_succ n ν
  simp only [Nat.cast_add, Nat.cast_one] at hs
  unfold eulerAltTerm
  rw [show (X : PowerSeries ℤ) ^ ν *
      ((-1) ^ (n + 1) * X ^ triangular (((n + 1 : ℕ) : ℤ) - ν) * bInv (X; X)_(n + 1)) =
      (-1) ^ (n + 1) * (X ^ ν * X ^ triangular (((n + 1 : ℕ) : ℤ) - ν)) *
        bInv (X; X)_(n + 1) by ring, hp]
  simp only [Nat.cast_add, Nat.cast_one] at *
  rw [hs, pow_succ (-1 : PowerSeries ℤ)]
  linear_combination -((-1 : PowerSeries ℤ) ^ n * X ^ triangular ((n : ℤ) - ν)) * hc

/-- The initial term in the cleared Euler recurrence. -/
theorem eulerAltTerm_zero (ν : ℕ) :
    eulerAltTerm (ν + 1) 0 = X ^ ν * eulerAltTerm ν 0 := by
  have he := triangular_step 0 ν
  simp only [Nat.cast_zero, zero_sub, add_zero] at he
  simp only [eulerAltTerm, pow_zero, one_mul, qPochhammer_zero, bInv_one, mul_one]
  rw [← pow_add]
  congr 1
  simpa [add_comm] using he.symm

/-- Appendix E.1: the recurrence makes every positive-index cleared sum vanish. -/
theorem eulerAlt_recurrence (ν : ℕ) :
    eulerAlt (ν + 1) = (X ^ ν - 1) * eulerAlt ν := by
  have hnext := summable_eulerAltTerm (ν + 1)
  have hprev := summable_eulerAltTerm ν
  have hnextShift := (summable_nat_add_iff 1).mpr hnext
  have hprevShift := (summable_nat_add_iff 1).mpr hprev
  have hsum : (∑' n, eulerAltTerm (ν + 1) (n + 1)) + eulerAlt ν =
      X ^ ν * ∑' n, eulerAltTerm ν (n + 1) := by
    rw [eulerAlt, ← hnextShift.tsum_add hprev, ← hprevShift.tsum_mul_left]
    exact tsum_congr (eulerAltTerm_step ν)
  have hn := hnext.sum_add_tsum_nat_add 1
  have hp := hprev.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hn hp
  rw [eulerAltTerm_zero] at hn
  unfold eulerAlt at *
  linear_combination -hn + X ^ ν * hp + hsum

theorem eulerAlt_eq_zero (ν : ℕ) : eulerAlt (ν + 1) = 0 := by
  induction ν with
  | zero =>
    have h := eulerAlt_recurrence 0
    simpa using h
  | succ ν ih =>
    rw [eulerAlt_recurrence]
    simp only [Nat.cast_add, Nat.cast_one, ih, mul_zero]

/-- Appendix E.1: the surviving terms are evaluated by the ordinary Euler identity. -/
theorem eulerAltTerm_neg (k n : ℕ) :
    eulerAltTerm (-(k : ℤ)) n =
      X ^ triangular k * qPochhammerInfInner (-(X ^ (k + 1))) X n := by
  unfold eulerAltTerm qPochhammerInfInner
  rw [sub_neg_eq_add, triangular_add,
    neg_eq_neg_one_mul (X ^ (k + 1) : PowerSeries ℤ), mul_pow]
  simp only [pow_mul, pow_add]
  ring

theorem eulerAlt_neg (k : ℕ) :
    eulerAlt (-(k : ℤ)) = X ^ triangular k * (X ^ (k + 1); X)_∞ := by
  have h := (hasSum_qPochhammerInf (X ^ (k + 1) : PowerSeries ℤ) (q := X) (by simp)).mul_left
    (X ^ triangular k)
  exact ((h.congr_fun (fun n => eulerAltTerm_neg k n)).tsum_eq)

theorem euler_tail (k : ℕ) :
    ((X ^ (k + 1); X)_∞ : PowerSeries ℤ) = (X; X)_∞ * bInv (X; X)_k := by
  have hp := qPochhammerInf_eq_qPochhammer_mul_qPochhammerInf k
    (a := (X : PowerSeries ℤ)) (q := X) (by simp)
  rw [← pow_succ'] at hp
  have hu := isUnit_qPochhammer_q 0 k
  simp only [Nat.zero_add, pow_one, q] at hu
  rw [hp]
  symm
  calc
    _ = ((X; X)_k * bInv (X; X)_k) * (X ^ (k + 1); X)_∞ := by ring
    _ = _ := by rw [hu.mul_bInv_cancel, one_mul]

theorem eulerAlt_neg_factorial (k : ℕ) :
    eulerAlt (-(k : ℤ)) = X ^ triangular k * (X; X)_∞ * bInv (X; X)_k := by
  rw [eulerAlt_neg, euler_tail, mul_assoc]

end KanadeRussell.Infra
