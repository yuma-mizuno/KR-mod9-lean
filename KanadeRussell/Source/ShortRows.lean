import KanadeRussell.Source.ReflectedMinus
import KanadeRussell.Infra.Euler
import KanadeRussell.Infra.BaseChange
set_option backward.isDefEq.respectTransparency false

/-! Cleared Euler evaluation of each reindexed row of the short theta functional.
Multiplication by t^(4 triangular(-ν)) keeps every intermediate exponent nonnegative. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Source
open Infra

def shortExponent (a n : ℕ) (ν : ℤ) (m : ℕ) : ℕ :=
  (3 * (n : ℤ) + 2 * a - 1 + 2 * ν - m).natAbs ^ 2 +
    m ^ 2 + 6 * m * n + 3 * n ^ 2 + 6 * n + 4 * a * m

theorem shortExponent_cast (a n : ℕ) (ν : ℤ) (m : ℕ) :
    (shortExponent a n ν m : ℤ) =
      (3 * (n : ℤ) + 2 * a - 1 + 2 * ν - m) ^ 2 +
        (m : ℤ) ^ 2 + 6 * m * n + 3 * (n : ℤ) ^ 2 + 6 * n + 4 * a * m := by
  simp [shortExponent]

/-- Universal clearing identity; it also applies when the naive prefactor is negative. -/
theorem shortExponent_clear (a n : ℕ) (ν : ℤ) (m : ℕ) :
    4 * triangular (-ν) + shortExponent a n ν m =
      shortExponent a n ν 0 + 4 * triangular ((m : ℤ) - ν) := by
  have h1 := shortExponent_cast a n ν m
  have h0 := shortExponent_cast a n ν 0
  have ht := twice_triangular ((m : ℤ) - ν)
  have hz := twice_triangular (-ν)
  simp only [Nat.cast_zero, sub_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h0
  nlinarith

noncomputable def shortRowTerm (a n : ℕ) (ν : ℤ) (m : ℕ) : QSeries :=
  (-1) ^ m * q ^ shortExponent a n ν m * bInv (q ^ 4; q ^ 4)_m
noncomputable def shortRow (a n : ℕ) (ν : ℤ) : QSeries := ∑' m, shortRowTerm a n ν m

theorem summable_shortRow (a n : ℕ) (ν : ℤ) : Summable (shortRowTerm a n ν) := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (k + 1))).subset
  intro m hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have he : k < shortExponent a n ν m := by
    have hm := Nat.le_self_pow (by decide : 2 ≠ 0) m
    dsimp [shortExponent]
    omega
  apply hn
  change coeff k (shortRowTerm a n ν m) = 0
  rw [shortRowTerm, mul_comm ((-1 : QSeries) ^ m), mul_assoc,
    coeff_X_pow_mul', if_neg (by omega)]

private theorem shortRowTerm_clear (a n : ℕ) (ν : ℤ) (m : ℕ) :
    q ^ (4 * triangular (-ν)) * shortRowTerm a n ν m =
      q ^ shortExponent a n ν 0 * intEval (q ^ 4) (eulerAltTerm ν m) := by
  have hu : IsUnit (q; q)_m := by simpa using isUnit_qPochhammer_q 0 m
  have hx : intEval (q ^ 4) q = q ^ 4 := by simp [q]
  simp only [eulerAltTerm, map_mul, map_pow, map_neg, map_one]
  rw [hu.map_bInv, map_qPochhammer, hx]
  change q ^ (4 * triangular (-ν)) * shortRowTerm a n ν m =
    q ^ shortExponent a n ν 0 * ((-1) ^ m * (q ^ 4) ^ triangular ((m : ℤ) - ν) *
      bInv (q ^ 4; q ^ 4)_m)
  rw [← pow_mul]
  calc
    _ = (-1) ^ m * q ^ (4 * triangular (-ν) + shortExponent a n ν m) * bInv (q ^ 4; q ^ 4)_m := by
      rw [pow_add, shortRowTerm]
      ring
    _ = _ := by rw [shortExponent_clear, pow_add]; ring

theorem shortRow_clear (a n : ℕ) (ν : ℤ) :
    q ^ (4 * triangular (-ν)) * shortRow a n ν =
      q ^ shortExponent a n ν 0 * intEval (q ^ 4) (eulerAlt ν) := by
  have hl := (summable_shortRow a n ν).hasSum.mul_left (q ^ (4 * triangular (-ν)))
  have hr := ((summable_eulerAltTerm ν).hasSum.map (intEval (q ^ 4)) (by fun_prop)).mul_left
    (q ^ shortExponent a n ν 0)
  exact hl.unique (hr.congr_fun (fun m => shortRowTerm_clear a n ν m))

theorem shortRow_positive (a n ν : ℕ) : shortRow a n (ν + 1) = 0 := by
  have h := shortRow_clear a n (ν + 1)
  rw [eulerAlt_eq_zero, map_zero, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ X_ne_zero)

theorem shortRow_negative (a n r : ℕ) : shortRow a n (-(r : ℤ)) =
    q ^ shortExponent a n (-(r : ℤ)) 0 * (q ^ 4; q ^ 4)_∞ * bInv (q ^ 4; q ^ 4)_r := by
  have h := shortRow_clear a n (-(r : ℤ))
  rw [eulerAlt_neg_factorial] at h
  have hu : IsUnit (q; q)_r := by simpa using isUnit_qPochhammer_q 0 r
  have hx : intEval (q ^ 4) q = q ^ 4 := by simp [q]
  simp only [map_mul, map_pow] at h
  rw [hu.map_bInv, map_qPochhammer, map_qPochhammerInf (intEval (q ^ 4)) (by fun_prop) q (by simp),
    hx, ← pow_mul, neg_neg] at h
  apply mul_left_cancel₀ (pow_ne_zero (4 * triangular (r : ℤ)) (show (q : QSeries) ≠ 0 from X_ne_zero))
  convert h using 1
  ring

theorem shortExponent_zero_negative (n r : ℕ) :
    shortExponent 0 n (-(r : ℤ)) 0 = 1 + 4 * (reflectedExponent r n + r) := by
  have h := shortExponent_cast 0 n (-(r : ℤ)) 0
  have hr := reflectedExponent_cast r n
  simp only [Nat.cast_zero, sub_zero, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  nlinarith

theorem shortExponent_one_negative (n r : ℕ) :
    shortExponent 1 n (-(r : ℤ)) 0 = 1 + 4 * minusExponent r n := by
  have h := shortExponent_cast 1 n (-(r : ℤ)) 0
  have hr := minusExponent_cast r n
  norm_num only [Nat.cast_zero, Nat.cast_one, sub_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  nlinarith

end KanadeRussell.Source
