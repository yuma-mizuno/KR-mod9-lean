import KanadeRussell.Source.Reflected
import KanadeRussell.Infra.Euler
import KanadeRussell.Infra.BaseChange
set_option backward.isDefEq.respectTransparency false

/-! Cleared Euler evaluation of each reindexed row of the long theta functional.
Multiplication by t^(12 triangular(-ν)) keeps every intermediate exponent nonnegative. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Source
open Infra

def longExponent (m : ℕ) (ν : ℤ) (n : ℕ) : ℕ :=
  3 * ((m : ℤ) - n + 2 * ν).natAbs ^ 2 + m ^ 2 + 6 * m * n + 3 * n ^ 2 + 6 * n

theorem longExponent_cast (m : ℕ) (ν : ℤ) (n : ℕ) :
    (longExponent m ν n : ℤ) =
      3 * ((m : ℤ) - n + 2 * ν) ^ 2 + (m : ℤ) ^ 2 + 6 * m * n + 3 * (n : ℤ) ^ 2 + 6 * n := by
  simp [longExponent]

/-- Universal clearing identity; it also applies when the naive prefactor is negative. -/
theorem longExponent_clear (m : ℕ) (ν : ℤ) (n : ℕ) :
    12 * triangular (-ν) + longExponent m ν n =
      longExponent m ν 0 + 12 * triangular ((n : ℤ) - ν) := by
  have h1 := longExponent_cast m ν n
  have h0 := longExponent_cast m ν 0
  have ht := twice_triangular ((n : ℤ) - ν)
  have hz := twice_triangular (-ν)
  simp only [Nat.cast_zero, sub_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h0
  nlinarith

noncomputable def longRowTerm (m : ℕ) (ν : ℤ) (n : ℕ) : QSeries :=
  (-1) ^ n * q ^ longExponent m ν n * bInv (q ^ 12; q ^ 12)_n
noncomputable def longRow (m : ℕ) (ν : ℤ) : QSeries := ∑' n, longRowTerm m ν n

theorem summable_longRow (m : ℕ) (ν : ℤ) : Summable (longRowTerm m ν) := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (k + 1))).subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have he : k < longExponent m ν n := by dsimp [longExponent]; omega
  apply hn
  change coeff k (longRowTerm m ν n) = 0
  rw [longRowTerm, mul_comm ((-1 : QSeries) ^ n), mul_assoc,
    coeff_X_pow_mul', if_neg (by omega)]

private theorem longRowTerm_clear (m : ℕ) (ν : ℤ) (n : ℕ) :
    q ^ (12 * triangular (-ν)) * longRowTerm m ν n =
      q ^ longExponent m ν 0 * intEval (q ^ 12) (eulerAltTerm ν n) := by
  have hu : IsUnit (q; q)_n := by simpa using isUnit_qPochhammer_q 0 n
  have hx : intEval (q ^ 12) q = q ^ 12 := by simp [q]
  simp only [eulerAltTerm, map_mul, map_pow, map_neg, map_one]
  rw [hu.map_bInv, map_qPochhammer, hx]
  change q ^ (12 * triangular (-ν)) * longRowTerm m ν n =
    q ^ longExponent m ν 0 * ((-1) ^ n * (q ^ 12) ^ triangular ((n : ℤ) - ν) *
      bInv (q ^ 12; q ^ 12)_n)
  rw [← pow_mul]
  calc
    _ = (-1) ^ n * q ^ (12 * triangular (-ν) + longExponent m ν n) * bInv (q ^ 12; q ^ 12)_n := by
      rw [pow_add, longRowTerm]
      ring
    _ = _ := by rw [longExponent_clear, pow_add]; ring

theorem longRow_clear (m : ℕ) (ν : ℤ) :
    q ^ (12 * triangular (-ν)) * longRow m ν =
      q ^ longExponent m ν 0 * intEval (q ^ 12) (eulerAlt ν) := by
  have hl := (summable_longRow m ν).hasSum.mul_left (q ^ (12 * triangular (-ν)))
  have hr := ((summable_eulerAltTerm ν).hasSum.map (intEval (q ^ 12)) (by fun_prop)).mul_left
    (q ^ longExponent m ν 0)
  exact hl.unique (hr.congr_fun (fun n => longRowTerm_clear m ν n))

theorem longRow_positive (m ν : ℕ) : longRow m (ν + 1) = 0 := by
  have h := longRow_clear m (ν + 1)
  rw [eulerAlt_eq_zero, map_zero, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ X_ne_zero)

theorem longExponent_negative_zero (m r : ℕ) :
    longExponent m (-(r : ℤ)) 0 = 4 * reflectedExponent m r := by
  have h := longExponent_cast m (-(r : ℤ)) 0
  have hr := reflectedExponent_cast m r
  simp only [Nat.cast_zero, sub_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  nlinarith

theorem longRow_negative (m r : ℕ) : longRow m (-(r : ℤ)) =
    q ^ (4 * reflectedExponent m r) * (q ^ 12; q ^ 12)_∞ * bInv (q ^ 12; q ^ 12)_r := by
  have h := longRow_clear m (-(r : ℤ))
  rw [eulerAlt_neg_factorial] at h
  have hu : IsUnit (q; q)_r := by simpa using isUnit_qPochhammer_q 0 r
  have hx : intEval (q ^ 12) q = q ^ 12 := by simp [q]
  simp only [map_mul, map_pow] at h
  rw [hu.map_bInv, map_qPochhammer, map_qPochhammerInf (intEval (q ^ 12)) (by fun_prop) q (by simp),
    hx, ← pow_mul, longExponent_negative_zero, neg_neg] at h
  apply mul_left_cancel₀ (pow_ne_zero (12 * triangular (r : ℤ)) (show (q : QSeries) ≠ 0 from X_ne_zero))
  convert h using 1
  ring

end KanadeRussell.Source
