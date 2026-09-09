import KanadeRussell.Infra.QDifference
set_option backward.isDefEq.respectTransparency false

/-! Coefficient form of the scalar equation in paper `eq:app-scalar-equation`. -/

open PowerSeries

namespace KanadeRussell.Infra

variable {R : Type*} [CommRing R]

/-- The first two coefficients of the scalar operator vanish identically; its later
coefficients are the denominator-cleared recurrence used for G and the Airy source. -/
theorem scalarEquation_of_recurrence (q : R) (f : PowerSeries R)
    (hrec : ∀ n : ℕ, (1 - q ^ (n + 2)) * (1 - q ^ (n + 1)) * coeff (n + 2) f =
      q ^ (2 * n + 3) * (1 - q ^ (n + 1)) * coeff (n + 1) f + q ^ (n + 1) * coeff n f) :
    scalarEquation q f = 0 := by
  apply PowerSeries.ext
  intro n
  rcases n with _ | n
  · simp only [scalarEquation, add_mul, sub_mul, mul_assoc, pow_two,
      map_add, map_sub, coeff_C_mul, coeff_zero_X_mul, coeff_rescale,
      pow_zero, one_mul, mul_zero, map_zero]
    ring
  rcases n with _ | n
  · simp only [scalarEquation, add_mul, sub_mul, mul_assoc, pow_two,
      map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_rescale,
      pow_zero, one_mul, mul_zero, map_zero]
    ring
  · simp only [scalarEquation, add_mul, sub_mul, mul_assoc, pow_two,
      map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_rescale, map_zero, one_mul]
    linear_combination q * hrec n

end KanadeRussell.Infra
