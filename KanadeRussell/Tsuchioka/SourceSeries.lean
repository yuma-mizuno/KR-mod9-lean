import KanadeRussell.Tsuchioka.ScalarFactors

/-! The ordinary scalar series in the source, and their rational normalized products. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Scalar

open scoped BigOperators
open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

/-- The source's six-factor binomial series, with its ordinary variable. -/
noncomputable def H (w : K) (a : Fin 6 → ℤ) : PowerSeries K :=
  ∏ p : Fin 6, binomialFactor ((a p : ℚ) / 3) (w ^ (-(p.val : ℤ))) *
    binomialFactor (-(a p : ℚ) / 3) (-(w ^ (-(p.val : ℤ))))

@[simp] theorem constantCoeff_H (w : K) (a : Fin 6 → ℤ) :
    constantCoeff (H w a) = 1 := by
  simp [H, map_prod]

theorem H_add (w : K) (a b : Fin 6 → ℤ) :
    H w (a + b) = H w a * H w b := by
  simp only [H, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [Pi.add_apply, Int.cast_add, add_div, neg_add,
    binomialFactor_add]
  ring

@[simp] theorem H_zero (w : K) : H w 0 = 1 := by simp [H]

theorem H_neg_mul (w : K) (a : Fin 6 → ℤ) : H w (-a) * H w a = 1 := by
  rw [← H_add, neg_add_cancel, H_zero]

/-- The five exponent lists printed in the definition of G1,...,G5. -/
def exponents : Fin 5 → Fin 6 → ℤ :=
  ![![2, 1, 1, 0, -1, -1], ![-1, 1, 1, 0, -1, -1],
    ![-1, 1, -2, 0, 2, -1], ![2, -2, -2, 0, 2, 2], ![2, -2, 1, 0, -1, 2]]

/-- Index 0 denotes G1 and index 4 denotes G5. -/
noncomputable def G (w : K) (i : Fin 5) : PowerSeries K := H w (exponents i)

/-- Integer exponents in G1 squared times G2,...,G5. -/
def sameExponents : Fin 4 → Fin 6 → ℤ :=
  ![![1, 1, 1, 0, -1, -1], ![1, 1, 0, 0, 0, -1],
    ![2, 0, 0, 0, 0, 0], ![2, 0, 1, 0, -1, 0]]

/-- Integer exponents in G1 inverse times G2,...,G5. -/
def distinctExponents : Fin 4 → Fin 6 → ℤ :=
  ![![-1, 0, 0, 0, 0, 0], ![-1, 0, -1, 0, 1, 0],
    ![0, -1, -1, 0, 1, 1], ![0, -1, 0, 0, 0, 1]]

theorem same_exponents_identity (i : Fin 4) :
    exponents 0 + exponents 0 + exponents i.succ = fun p => 3 * sameExponents i p := by
  funext p
  fin_cases i <;> fin_cases p <;> decide

theorem distinct_exponents_identity (i : Fin 4) :
    -exponents 0 + exponents i.succ = fun p => 3 * distinctExponents i p := by
  funext p
  fin_cases i <;> fin_cases p <;> decide

/-- The same-position Wick products have integral exponents, in every degree. -/
theorem sameProduct_eq_H (w : K) (i : Fin 4) :
    G w 0 ^ 2 * G w i.succ = H w (fun p => 3 * sameExponents i p) := by
  rw [← same_exponents_identity, H_add, H_add]
  simp only [G, pow_two]

/-- The distinct-position Wick products have integral exponents, in every degree. -/
theorem distinctProduct_eq_H (w : K) (i : Fin 4) :
    H w (-exponents 0) * G w i.succ = H w (fun p => 3 * distinctExponents i p) := by
  rw [← distinct_exponents_identity, H_add]
  rfl

/-- Numerator polynomial of a binomial quotient with integral exponents. -/
noncomputable def numerator (w : K) (b : Fin 6 → ℤ) : Polynomial K :=
  ∏ p : Fin 6,
    (1 - Polynomial.C (w ^ (-(p.val : ℤ))) * Polynomial.X) ^ (b p).toNat *
    (1 + Polynomial.C (w ^ (-(p.val : ℤ))) * Polynomial.X) ^ (-(b p)).toNat

theorem coe_numerator (w : K) (b : Fin 6 → ℤ) :
    (numerator w b : PowerSeries K) = ∏ p : Fin 6,
      (1 - C (w ^ (-(p.val : ℤ))) * X) ^ (b p).toNat *
      (1 + C (w ^ (-(p.val : ℤ))) * X) ^ (-(b p)).toNat := by
  change Polynomial.coeToPowerSeries.ringHom (numerator w b) = _
  simp [numerator, map_prod]

@[simp] theorem numerator_constantCoeff (w : K) (b : Fin 6 → ℤ) :
    (numerator w b).coeff 0 = 1 := by
  rw [← Polynomial.constantCoeff_apply]
  unfold numerator
  simp only [map_prod, map_mul, map_pow]
  simp [Polynomial.constantCoeff_apply]

theorem numerator_isUnit (w : K) (b : Fin 6 → ℤ) :
    IsUnit (numerator w b : PowerSeries K) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp

/-- Clearing the explicit polynomial denominator recovers the explicit numerator. -/
theorem H_integer_cross (w : K) (b : Fin 6 → ℤ) :
    H w (fun p => 3 * b p) * (numerator w (-b) : PowerSeries K) =
      (numerator w b : PowerSeries K) := by
  rw [coe_numerator, coe_numerator]
  simp only [H, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [Pi.neg_apply, neg_neg, Int.cast_mul, Int.cast_ofNat]
  have h1 := binomialFactor_int_cross (b p) (w ^ (-(p.val : ℤ)))
  have h2 := binomialFactor_int_cross (-(b p)) (-(w ^ (-(p.val : ℤ))))
  simp only [neg_neg, Int.cast_neg, map_neg, neg_mul, sub_neg_eq_add] at h2
  rw [show (3 : ℚ) * b p / 3 = b p by ring,
    show -((3 : ℚ) * b p) / 3 = -(b p : ℚ) by ring]
  calc
    _ = (binomialFactor (b p : ℚ) (w ^ (-(p.val : ℤ))) *
        (1 - C (w ^ (-(p.val : ℤ))) * X) ^ (-(b p)).toNat) *
      (binomialFactor (-(b p : ℚ)) (-(w ^ (-(p.val : ℤ)))) *
        (1 + C (w ^ (-(p.val : ℤ))) * X) ^ (b p).toNat) := by ring
    _ = _ := by rw [h1, h2]

theorem sameProduct_cross (w : K) (i : Fin 4) :
    (G w 0 ^ 2 * G w i.succ) *
        (numerator w (-sameExponents i) : PowerSeries K) =
      (numerator w (sameExponents i) : PowerSeries K) := by
  rw [sameProduct_eq_H]
  exact H_integer_cross w (sameExponents i)

theorem distinctProduct_cross (w : K) (i : Fin 4) :
    (H w (-exponents 0) * G w i.succ) *
        (numerator w (-distinctExponents i) : PowerSeries K) =
      (numerator w (distinctExponents i) : PowerSeries K) := by
  rw [distinctProduct_eq_H]
  exact H_integer_cross w (distinctExponents i)

end KanadeRussell.Tsuchioka.Scalar
