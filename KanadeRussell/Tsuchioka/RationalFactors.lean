import KanadeRussell.Tsuchioka.ScalarFactors

/-! Rational polynomial identities for the source scalar factors. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

open scoped BigOperators
open PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Cubing a product of third-integer binomial powers clears its fractional exponents. -/
theorem binomialProduct_cube_cross {ι : Type*} (s : Finset ι) (a : ι → ℤ) (c : ι → A) :
    (∏ i ∈ s, binomialFactor ((a i : ℚ) / 3) (c i)) ^ 3 *
      (∏ i ∈ s, (1 - C (c i) * X) ^ (-(a i)).toNat) =
        ∏ i ∈ s, (1 - C (c i) * X) ^ (a i).toNat := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [binomialFactor_three, show 3 * ((a i : ℚ) / 3) = (a i : ℚ) by ring]
  exact binomialFactor_int_cross (a i) (c i)

end KanadeRussell.Tsuchioka.FormalSeries

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

/-- The actual numerator polynomial after cubing the first-root scalar factor. -/
noncomputable def orbitNumerator (w : K) : Polynomial (LaurentSeries (Space K)) :=
  ∏ p : Fin 12,
    (1 - Polynomial.C (ratioMonomial w p.val) * Polynomial.X) ^ (orbitPairing p).toNat

/-- The actual denominator polynomial after cubing the first-root scalar factor. -/
noncomputable def orbitDenominator (w : K) : Polynomial (LaurentSeries (Space K)) :=
  ∏ p : Fin 12,
    (1 - Polynomial.C (ratioMonomial w p.val) * Polynomial.X) ^ (-(orbitPairing p)).toNat

theorem coe_orbitNumerator (w : K) :
    (orbitNumerator w : PowerSeries (LaurentSeries (Space K))) =
      ∏ p : Fin 12, (1 - C (ratioMonomial w p.val) * X) ^ (orbitPairing p).toNat := by
  change Polynomial.coeToPowerSeries.ringHom (orbitNumerator w) = _
  simp [orbitNumerator, map_prod]

theorem coe_orbitDenominator (w : K) :
    (orbitDenominator w : PowerSeries (LaurentSeries (Space K))) =
      ∏ p : Fin 12, (1 - C (ratioMonomial w p.val) * X) ^ (-(orbitPairing p)).toNat := by
  change Polynomial.coeToPowerSeries.ringHom (orbitDenominator w) = _
  simp [orbitDenominator, map_prod]

theorem orbitProduct_cube_cross (w : K) :
    orbitProduct w ^ 3 * (orbitDenominator w : PowerSeries (LaurentSeries (Space K))) =
      (orbitNumerator w : PowerSeries (LaurentSeries (Space K))) := by
  rw [coe_orbitNumerator, coe_orbitDenominator]
  exact binomialProduct_cube_cross Finset.univ orbitPairing (fun p => ratioMonomial w p.val)

@[simp] theorem orbitNumerator_constantCoeff (w : K) : (orbitNumerator w).coeff 0 = 1 := by
  rw [← Polynomial.constantCoeff_apply]
  unfold orbitNumerator
  simp only [map_prod, map_pow, map_sub, map_one, map_mul]
  simp [Polynomial.constantCoeff_apply]

@[simp] theorem orbitDenominator_constantCoeff (w : K) : (orbitDenominator w).coeff 0 = 1 := by
  rw [← Polynomial.constantCoeff_apply]
  unfold orbitDenominator
  simp only [map_prod, map_pow, map_sub, map_one, map_mul]
  simp [Polynomial.constantCoeff_apply]

theorem orbitDenominator_isUnit (w : K) :
    IsUnit (orbitDenominator w : PowerSeries (LaurentSeries (Space K))) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp

/-- Exact rational expression for the cube of the paper's G1.
This is an identity of full formal series; no coefficient cutoff is used. -/
theorem sourceG1_cube_cross (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    sourceG1 w ^ 3 * (orbitDenominator w : PowerSeries (LaurentSeries (Space K))) =
      (orbitNumerator w : PowerSeries (LaurentSeries (Space K))) := by
  rw [← orbitProduct_eq_sourceG1 w hw]
  exact orbitProduct_cube_cross w

/-- The rational cubic relation holds for the scalar obtained from the actual Fock field. -/
theorem rootFactor_cube_cross (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    rootFactor w ^ 3 * (orbitDenominator w : PowerSeries (LaurentSeries (Space K))) =
      (orbitNumerator w : PowerSeries (LaurentSeries (Space K))) := by
  rw [rootFactor_eq_sourceG1 w hw]
  exact sourceG1_cube_cross w hw

end KanadeRussell.Tsuchioka.Fock
