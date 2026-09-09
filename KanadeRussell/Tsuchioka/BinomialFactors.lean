import KanadeRussell.Tsuchioka.FormalExponential

/-! Full formal-series identification of rational binomial factors and exponentials. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

open PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The formal logarithm of 1-cX, with its zero constant term. -/
noncomputable def logOneSub (c : A) : PowerSeries A :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else -(algebraMap ℚ A (1 / (n : ℚ))) * c ^ n

@[simp] theorem constantCoeff_logOneSub (c : A) :
    constantCoeff (logOneSub c) = 0 := by
  simp [logOneSub]

theorem coeff_derivative_logOneSub (c : A) (n : ℕ) :
    coeff n (derivative A (logOneSub c)) = -(c ^ (n + 1)) := by
  rw [coeff_derivative, logOneSub, coeff_mk, if_neg (by omega)]
  have hn : (n : A) + 1 = algebraMap ℚ A ((n : ℚ) + 1) := by simp
  have hunit : algebraMap ℚ A (1 / ((n : ℚ) + 1)) *
      algebraMap ℚ A ((n : ℚ) + 1) = 1 := by
    rw [← map_mul, one_div_mul_cancel (by positivity), map_one]
  push_cast
  rw [hn]
  linear_combination -(c ^ (n + 1)) * hunit

theorem logOneSub_differential (c : A) :
    (1 - C c * X) * derivative A (logOneSub c) = -C c := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, map_neg, coeff_C]
  cases n with
  | zero => simp [coeff_derivative_logOneSub, coeff_zero_X_mul]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative_logOneSub, coeff_derivative_logOneSub]
    simp [pow_succ]
    ring

/-- Uniqueness also holds after multiplying the differential equation by a unit. -/
theorem differential_unique_unit (a b : PowerSeries A) (ha : IsUnit a)
    {f g : PowerSeries A} (hf : a * derivative A f = b * f)
    (hg : a * derivative A g = b * g)
    (hc : constantCoeff f = constantCoeff g) : f = g := by
  letI : IsAddTorsionFree A := .of_module_rat A
  obtain ⟨u, rfl⟩ := ha
  apply differential_unique ((↑u⁻¹ : PowerSeries A) * b) _ _ hc
  · calc
      derivative A f = (↑u⁻¹ : PowerSeries A) * (↑u * derivative A f) := by simp
      _ = ((↑u⁻¹ : PowerSeries A) * b) * f := by rw [hf, mul_assoc]
  · calc
      derivative A g = (↑u⁻¹ : PowerSeries A) * (↑u * derivative A g) := by simp
      _ = ((↑u⁻¹ : PowerSeries A) * b) * g := by rw [hg, mul_assoc]

theorem choose_recurrence (r : ℚ) (n : ℕ) :
    ((n : ℚ) + 1) * Ring.choose r (n + 1) =
      Ring.choose r n * (r - n) := by
  simpa [Nat.choose_succ_self_right, Ring.choose_one_right, nsmul_eq_mul] using
    (Ring.choose_smul_choose r (n := n + 1) (k := n) (by omega))

/-- The usual rational binomial expansion of (1-cX)^r. -/
noncomputable def binomialFactor (r : ℚ) (c : A) : PowerSeries A :=
  rescale (-c) (binomialSeries A r)

@[simp] theorem coeff_binomialFactor (r : ℚ) (c : A) (n : ℕ) :
    coeff n (binomialFactor r c) =
      (-c) ^ n * algebraMap ℚ A (Ring.choose r n) := by
  simp [binomialFactor, Algebra.smul_def]

@[simp] theorem constantCoeff_binomialFactor (r : ℚ) (c : A) :
    constantCoeff (binomialFactor r c) = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_binomialFactor]
  simp

theorem binomialFactor_recurrence (r : ℚ) (c : A) (n : ℕ) :
    coeff (n + 1) (binomialFactor r c) * ((n : A) + 1) =
      (-c) * (algebraMap ℚ A r - (n : A)) * coeff n (binomialFactor r c) := by
  have h := congrArg (algebraMap ℚ A) (choose_recurrence r n)
  simp only [map_mul, map_add, map_one, map_sub, map_natCast] at h
  simp only [coeff_binomialFactor, pow_succ]
  linear_combination (-c) ^ n * (-c) * h

omit [Algebra ℚ A] in
theorem coeff_X_derivative (f : PowerSeries A) (n : ℕ) :
    coeff n (X * derivative A f) = coeff n f * (n : A) := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_X_mul, coeff_derivative]

theorem binomialFactor_differential (r : ℚ) (c : A) :
    (1 - C c * X) * derivative A (binomialFactor r c) =
      C (-(algebraMap ℚ A r) * c) * binomialFactor r c := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_C_mul,
    coeff_derivative, coeff_X_derivative, binomialFactor_recurrence]
  ring

/-- The formal binomial series agrees with the logarithmic exponential in every degree. -/
theorem binomialFactor_eq_exponential (r : ℚ) (c : A) :
    binomialFactor r c = exponential (C (algebraMap ℚ A r) * logOneSub c) := by
  have hz : constantCoeff (C (algebraMap ℚ A r) * logOneSub c) = 0 := by simp
  apply differential_unique_unit (1 - C c * X) (C (-(algebraMap ℚ A r) * c))
    (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp))
    (binomialFactor_differential r c)
  · rw [derivative_exponential hz, Derivation.leibniz]
    simp only [derivative_C, smul_eq_mul, mul_zero, add_zero]
    have hd := logOneSub_differential c
    calc
      (1 - C c * X) *
          (exponential (C (algebraMap ℚ A r) * logOneSub c) *
            (C (algebraMap ℚ A r) * derivative A (logOneSub c))) =
        C (algebraMap ℚ A r) * exponential (C (algebraMap ℚ A r) * logOneSub c) *
          ((1 - C c * X) * derivative A (logOneSub c)) := by ring
      _ = C (-(algebraMap ℚ A r) * c) *
          exponential (C (algebraMap ℚ A r) * logOneSub c) := by
        rw [hd]
        simp only [map_mul, map_neg]
        ring
  · simp [hz]

theorem binomialFactor_add (r s : ℚ) (c : A) :
    binomialFactor (r + s) c = binomialFactor r c * binomialFactor s c := by
  simp only [binomialFactor, binomialSeries_add, map_mul]

@[simp] theorem binomialFactor_zero (c : A) : binomialFactor 0 c = 1 := by
  simp [binomialFactor]

@[simp] theorem binomialFactor_one (c : A) : binomialFactor 1 c = 1 - C c * X := by
  have h := congrArg (rescale (-c)) (binomialSeries_nat (A := A) (R := ℚ) 1)
  simpa [binomialFactor, map_neg, sub_eq_add_neg] using h

theorem binomialFactor_neg_mul (r : ℚ) (c : A) :
    binomialFactor (-r) c * binomialFactor r c = 1 := by
  rw [← binomialFactor_add]
  simp

theorem binomialFactor_three (r : ℚ) (c : A) :
    binomialFactor r c ^ 3 = binomialFactor (3 * r) c := by
  rw [show 3 * r = r + r + r by ring, binomialFactor_add, binomialFactor_add]
  ring

theorem binomialFactor_shift_one (r : ℚ) (c : A) :
    binomialFactor (r + 1) c = binomialFactor r c * (1 - C c * X) := by
  rw [binomialFactor_add, binomialFactor_one]

theorem binomialFactor_shift_neg_one (r : ℚ) (c : A) :
    binomialFactor (r - 1) c * (1 - C c * X) = binomialFactor r c := by
  rw [← binomialFactor_one, ← binomialFactor_add, sub_add_cancel]

theorem binomialFactor_nat (n : ℕ) (c : A) :
    binomialFactor (n : ℚ) c = (1 - C c * X) ^ n := by
  have h := congrArg (rescale (-c)) (binomialSeries_nat (A := A) (R := ℚ) n)
  simpa [binomialFactor, map_neg, sub_eq_add_neg] using h

/-- Integer exponents give a polynomial cross-multiplication identity. -/
theorem binomialFactor_int_cross (z : ℤ) (c : A) :
    binomialFactor (z : ℚ) c * (1 - C c * X) ^ (-z).toNat =
      (1 - C c * X) ^ z.toNat := by
  cases z with
  | ofNat n => simp [binomialFactor_nat]
  | negSucc n =>
    have h := binomialFactor_neg_mul (A := A) ((n + 1 : ℕ) : ℚ) c
    rw [binomialFactor_nat] at h
    simpa using h

theorem binomialFactor_shift_int (r : ℚ) (z : ℤ) (c : A) :
    binomialFactor (r + z) c * (1 - C c * X) ^ (-z).toNat =
      binomialFactor r c * (1 - C c * X) ^ z.toNat := by
  rw [binomialFactor_add, mul_assoc, binomialFactor_int_cross]


/-- Binomial expansions commute with coefficient homomorphisms. -/
theorem map_binomialFactor {B : Type*} [CommRing B] [Algebra ℚ B]
    (h : A →+* B) (r : ℚ) (c : A) :
    PowerSeries.map h (binomialFactor r c) = binomialFactor r (h c) := by
  apply PowerSeries.ext
  intro n
  simp [coeff_binomialFactor, RingHom.map_rat_algebraMap]

/-- Rescaling the variable rescales the linear binomial factor. -/
theorem rescale_binomialFactor (d : A) (r : ℚ) (c : A) :
    rescale d (binomialFactor r c) = binomialFactor r (d * c) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_rescale, coeff_binomialFactor]
  rw [← mul_assoc, ← mul_pow]
  congr 2
  ring

end KanadeRussell.Tsuchioka.FormalSeries
