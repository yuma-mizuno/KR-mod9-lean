import KanadeRussell.Tsuchioka.SourceSeries

/-! Algebraic Fourier expansions: geometric series and bilateral coefficient functions. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

open PowerSeries

variable {A : Type*} [CommRing A]

/-- The geometric power series, defined coefficientwise. -/
noncomputable def geometric (c : A) : PowerSeries A := mk fun n => c ^ n

@[simp] theorem coeff_geometric (c : A) (n : ℕ) :
    coeff n (geometric c) = c ^ n := by simp [geometric]

theorem geometric_mul_linear (c : A) :
    geometric c * (1 - C c * X) = 1 := by
  apply PowerSeries.ext
  intro n
  rw [mul_comm, sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul]
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_X_mul, pow_succ, mul_comm]

@[simp] theorem constantCoeff_geometric (c : A) :
    constantCoeff (geometric c) = 1 := by simp [geometric]

/-- The Euler derivative of the geometric series. -/
noncomputable def eulerGeometric (c : A) : PowerSeries A :=
  X * derivative A (geometric c)

@[simp] theorem coeff_eulerGeometric (c : A) (n : ℕ) :
    coeff n (eulerGeometric c) = c ^ n * (n : A) := by
  rw [eulerGeometric, coeff_X_derivative, coeff_geometric]

theorem eulerGeometric_mul_linear_sq (c : A) :
    eulerGeometric c * (1 - C c * X) ^ 2 = C c * X := by
  have hg := geometric_mul_linear c
  have hd := congrArg (derivative A) hg
  simp only [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, derivative_C,
    derivative_X, smul_eq_mul, mul_one, mul_zero, add_zero, zero_sub] at hd
  unfold eulerGeometric
  linear_combination X * (1 - C c * X) * hd + C c * X * hg

/-- A series expanded in nonnegative powers as a bilateral coefficient function.
No infinite product of bilateral distributions is defined. -/
noncomputable def positive (f : PowerSeries A) (n : ℤ) : A :=
  if 0 ≤ n then coeff n.toNat f else 0

@[simp] theorem positive_nat (f : PowerSeries A) (n : ℕ) :
    positive f (n : ℤ) = coeff n f := by simp [positive]

theorem positive_neg_nat (f : PowerSeries A) (n : ℕ) (hn : 0 < n) :
    positive f (-(n : ℤ)) = 0 := by
  simp only [positive, if_neg (by omega : ¬ 0 ≤ -(n : ℤ))]

/-- The source's bar operation sends exponent n to exponent -n. -/
def reflect (f : ℤ → A) (n : ℤ) : A := f (-n)

theorem positive_add (f g : PowerSeries A) :
    positive (f + g) = positive f + positive g := by
  funext n
  simp only [positive, Pi.add_apply]
  split <;> simp

theorem positive_sub (f g : PowerSeries A) :
    positive (f - g) = positive f - positive g := by
  funext n
  simp only [positive, Pi.sub_apply]
  split <;> simp

theorem positive_C_mul (a : A) (f : PowerSeries A) :
    positive (C a * f) = fun n => a * positive f n := by
  funext n
  simp only [positive]
  split <;> simp [coeff_C_mul]

end KanadeRussell.Tsuchioka.FormalSeries

namespace KanadeRussell.Tsuchioka.Scalar

open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

/-- The formal delta series, interpreted by its coefficients at all integer exponents. -/
def delta (c : K) (n : ℤ) : K := c ^ n

/-- The formal Euler derivative of the delta series. -/
def eulerDelta (c : K) (n : ℤ) : K := (n : K) * c ^ n

theorem even_geometric_one :
    positive (2 * geometric (1 : K) - 1) +
      reflect (positive (2 * geometric (1 : K) - 1)) = fun n => 2 * delta 1 n := by
  funext n
  change (positive _ n : K) + positive _ (-n) = _
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast]
    by_cases hn : n = 0
    · subst n; norm_num [positive, delta, two_mul]
    · rw [positive_nat, positive_neg_nat _ n (by omega)]
      norm_num [delta, two_mul, hn]
  | negSucc n =>
    change (positive _ (-((n + 1 : ℕ) : ℤ)) : K) +
      positive _ (-(-((n + 1 : ℕ) : ℤ))) = _
    rw [positive_neg_nat _ _ (by omega), neg_neg, positive_nat]
    norm_num [delta, two_mul]

theorem odd_eulerGeometric_neg_one (a : K) :
    positive (1 + C a * eulerGeometric (-1 : K)) -
      reflect (positive (1 + C a * eulerGeometric (-1 : K))) =
        fun n => a * eulerDelta (-1) n := by
  funext n
  change (positive _ n : K) - positive _ (-n) = _
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast]
    by_cases hn : n = 0
    · subst n; simp [eulerDelta]
    · rw [positive_nat, positive_neg_nat _ n (by omega)]
      simp only [map_add, coeff_one, if_neg hn, zero_add, coeff_C_mul,
        coeff_eulerGeometric, sub_zero, eulerDelta, zpow_natCast, Int.cast_natCast]
      ring
  | negSucc n =>
    change (positive _ (-((n + 1 : ℕ) : ℤ)) : K) -
      positive _ (-(-((n + 1 : ℕ) : ℤ))) = a * eulerDelta (-1) (-((n + 1 : ℕ) : ℤ))
    rw [positive_neg_nat _ _ (by omega), neg_neg, positive_nat,
      eulerDelta, zpow_neg, zpow_natCast]
    simp only [map_add, coeff_one, Nat.succ_ne_zero, if_false, zero_add, coeff_C_mul,
      coeff_eulerGeometric, zero_sub, eulerDelta, Int.cast_neg, Int.cast_natCast,
      inv_pow, inv_neg, inv_one]
    ring_nf
    rw [show (-1 : K)⁻¹ = -1 by simp]

/-- Exact ordinary expansion of G1 inverse times G2. -/
theorem distinct_G2_expansion (w : K) :
    H w (-exponents 0) * G w 1 = 2 * geometric 1 - 1 := by
  have h := distinctProduct_cross w (0 : Fin 4)
  have hg := geometric_mul_linear (1 : K)
  norm_num [numerator, distinctExponents, Fin.prod_univ_succ, coe_numerator] at h
  apply (PowerSeries.isUnit_iff_constantCoeff.mpr (show IsUnit (constantCoeff
    (1 - X : PowerSeries K)) by simp)).mul_right_cancel
  calc
    (H w (-exponents 0) * G w 1) * (1 - X) = 1 + X := by simpa using h
    _ = (2 * geometric 1 - 1) * (1 - X) := by
      simp only [map_one, one_mul] at hg
      linear_combination -2 * hg

/-- Exact ordinary expansion of G1 squared times G4. -/
theorem same_G4_expansion (w : K) :
    G w 0 ^ 2 * G w 3 = 1 + 4 * eulerGeometric (-1) := by
  have h := sameProduct_cross w (2 : Fin 4)
  have hg := eulerGeometric_mul_linear_sq (-1 : K)
  norm_num [numerator, sameExponents, Fin.prod_univ_succ, coe_numerator] at h
  norm_num only [map_neg, map_one, neg_one_mul, sub_neg_eq_add] at hg
  apply (PowerSeries.isUnit_iff_constantCoeff.mpr (show IsUnit (constantCoeff
    ((1 + X : PowerSeries K) ^ 2)) by simp)).mul_right_cancel
  calc
    (G w 0 ^ 2 * G w 3) * (1 + X) ^ 2 = (1 - X) ^ 2 := by simpa using h
    _ = (1 + 4 * eulerGeometric (-1)) * (1 + X) ^ 2 := by
      linear_combination -4 * hg

/-- The second Fourier identity in source Proposition 3.3, at every integer exponent. -/
theorem distinct_G2_fourier (w : K) :
    positive (H w (-exponents 0) * G w 1) +
      reflect (positive (H w (-exponents 0) * G w 1)) = fun n => 2 * delta 1 n := by
  rw [distinct_G2_expansion]
  exact even_geometric_one

/-- The fifth Fourier identity in source Proposition 3.3, including its zero coefficient. -/
theorem same_G4_fourier (w : K) :
    positive (G w 0 ^ 2 * G w 3) - reflect (positive (G w 0 ^ 2 * G w 3)) =
      fun n => 4 * eulerDelta (-1) n := by
  rw [same_G4_expansion]
  simpa only [map_ofNat] using odd_eulerGeometric_neg_one (4 : K)

end KanadeRussell.Tsuchioka.Scalar
