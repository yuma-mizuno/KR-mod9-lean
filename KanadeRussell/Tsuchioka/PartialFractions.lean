import KanadeRussell.Tsuchioka.PartialFractionCertificates
import KanadeRussell.Tsuchioka.ScalarPhases

/-! Complete partial-fraction expansions of the normalized source scalar products. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace KanadeRussell.Tsuchioka.Scalar

open scoped BigOperators
open PowerSeries FormalSeries

def phaseNumerator {A : Type*} [CommRing A] (w x : A) (b : Fin 6 → ℤ) : A :=
  ∏ p : Fin 6,
    (1 - phasePolynomial w (Fin.castAdd 6 p) * x) ^ (b p).toNat *
    (1 + phasePolynomial w (Fin.castAdd 6 p) * x) ^ (-(b p)).toNat

variable {K : Type*} [Field K] [CharZero K]

theorem coe_numerator_eq_phaseNumerator (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (b : Fin 6 → ℤ) :
    (numerator w b : PowerSeries K) = phaseNumerator (C w) X b := by
  rw [coe_numerator, phaseNumerator]
  apply Finset.prod_congr rfl
  intro p hp
  have h : C (w ^ (-(p.val : ℤ))) =
      phasePolynomial (C w) (Fin.castAdd 6 p) := by
    have hp := negative_phase w hw (Fin.castAdd 6 p)
    change w ^ (-(p.val : ℤ)) = _ at hp
    rw [hp, map_phasePolynomial]
  rw [h]

theorem cyclotomic_C (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    (C w : PowerSeries K) ^ 4 - (C w) ^ 2 + 1 = 0 := by
  have h := congrArg (C : K →+* PowerSeries K) hw
  simpa only [map_add, map_sub, map_pow, map_one, map_zero] using h

noncomputable def phaseGeometric (w : K) (p : Fin 12) : PowerSeries K :=
  geometric (phasePolynomial w p)

theorem phaseGeometric_mul (w : K) (p : Fin 12) :
    phaseGeometric w p * (1 - phasePolynomial (C w) p * X) = 1 := by
  rw [← map_phasePolynomial (C : K →+* PowerSeries K), phaseGeometric]
  exact geometric_mul_linear _

theorem phaseEulerGeometric_mul (w : K) (p : Fin 12) :
    eulerGeometric (phasePolynomial w p) * (1 - phasePolynomial (C w) p * X) ^ 2 =
      phasePolynomial (C w) p * X := by
  rw [← map_phasePolynomial (C : K →+* PowerSeries K)]
  exact eulerGeometric_mul_linear_sq _

def aPrime (w : K) : K := 4 + 4 * w - 2 * w ^ 3
def cPrime (w : K) : K := 42 + 48 * w - 24 * w ^ 3
def bCoeff (w : K) : K := 14 + 16 * w - 8 * w ^ 3

theorem same_G2_full_expansion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    G w 0 ^ 2 * G w 1 =
      C (aPrime w) * (phaseGeometric w 4 + phaseGeometric w 8) +
      C (Coefficients.tCoeff w) * (phaseGeometric w 5 + phaseGeometric w 7) +
      C (cPrime w) * geometric (-1) - 1 := by
  have h := sameProduct_cross w (0 : Fin 4)
  have hb : sameExponents (0 : Fin 4) = ![1, 1, 1, 0, -1, -1] := rfl
  rw [hb] at h
  apply (numerator_isUnit w (-(![1, 1, 1, 0, -1, -1] : Fin 6 → ℤ))).mul_right_cancel
  calc
    _ = (numerator w ![1, 1, 1, 0, -1, -1] : PowerSeries K) := by simpa using h
    _ = _ := by
      have hc := Certificates.same_G2 (C w) X
        (phaseGeometric w 4) (phaseGeometric w 8)
        (phaseGeometric w 5) (phaseGeometric w 7) (geometric (-1))
        (cyclotomic_C w hw)
        (phaseGeometric_mul w 4) (phaseGeometric_mul w 8)
        (phaseGeometric_mul w 5) (phaseGeometric_mul w 7)
        (phaseGeometric_mul w 6)
      rw [coe_numerator_eq_phaseNumerator w hw, coe_numerator_eq_phaseNumerator w hw]
      convert hc.symm using 1 <;>
        norm_num [phaseNumerator, Fin.prod_univ_succ, phasePolynomial, Int.reduceNeg,
          phaseGeometric, aPrime, cPrime, Coefficients.tCoeff, map_add, map_sub,
          map_mul, map_pow, map_ofNat] <;>
        simp only [show (-1 : ℤ).toNat = 0 by decide,
          show (-2 : ℤ).toNat = 0 by decide, show (2 : ℤ).toNat = 2 by decide,
          pow_zero, mul_one] <;> first | (left; ring) | ring


theorem same_G3_full_expansion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    G w 0 ^ 2 * G w 2 = C (Coefficients.mCoeff w) * (phaseGeometric w 5 + phaseGeometric w 7) +
      C (bCoeff w) * geometric (-1) - 1 := by
  have h := sameProduct_cross w (1 : Fin 4)
  have hb : sameExponents (1 : Fin 4) = ![1, 1, 0, 0, 0, -1] := rfl
  rw [hb] at h
  apply (numerator_isUnit w (-(![1, 1, 0, 0, 0, -1] : Fin 6 → ℤ))).mul_right_cancel
  calc
    _ = (numerator w ![1, 1, 0, 0, 0, -1] : PowerSeries K) := by simpa using h
    _ = _ := by
      have hc := Certificates.same_G3 (C w) X
        (phaseGeometric w 5) (phaseGeometric w 7) (geometric (-1))
        (cyclotomic_C w hw)
        (phaseGeometric_mul w 5) (phaseGeometric_mul w 7) (phaseGeometric_mul w 6)
      rw [coe_numerator_eq_phaseNumerator w hw, coe_numerator_eq_phaseNumerator w hw]
      convert hc.symm using 1 <;>
        norm_num [phaseNumerator, Fin.prod_univ_succ, phasePolynomial, Int.reduceNeg,
          phaseGeometric, aPrime, cPrime, bCoeff, Coefficients.tCoeff, Coefficients.mCoeff,
          Coefficients.pCoeff, Coefficients.qCoeff, map_add, map_sub,
          map_mul, map_pow, map_ofNat] <;>
        simp only [show (-1 : ℤ).toNat = 0 by decide,
          show (-2 : ℤ).toNat = 0 by decide, show (2 : ℤ).toNat = 2 by decide,
          pow_zero, mul_one] <;> first | (left; ring) | ring

theorem same_G5_full_expansion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    G w 0 ^ 2 * G w 4 = 1 + 12 * eulerGeometric (-1) +
      C (Coefficients.qCoeff w) * (phaseGeometric w 8 - phaseGeometric w 4) := by
  have h := sameProduct_cross w (3 : Fin 4)
  have hb : sameExponents (3 : Fin 4) = ![2, 0, 1, 0, -1, 0] := rfl
  rw [hb] at h
  apply (numerator_isUnit w (-(![2, 0, 1, 0, -1, 0] : Fin 6 → ℤ))).mul_right_cancel
  calc
    _ = (numerator w ![2, 0, 1, 0, -1, 0] : PowerSeries K) := by simpa using h
    _ = _ := by
      have hc := Certificates.same_G5 (C w) X
        (phaseGeometric w 8) (phaseGeometric w 4) (eulerGeometric (-1))
        (cyclotomic_C w hw)
        (phaseGeometric_mul w 8) (phaseGeometric_mul w 4) (phaseEulerGeometric_mul w 6)
      rw [coe_numerator_eq_phaseNumerator w hw, coe_numerator_eq_phaseNumerator w hw]
      convert hc.symm using 1 <;>
        norm_num [phaseNumerator, Fin.prod_univ_succ, phasePolynomial, Int.reduceNeg,
          phaseGeometric, aPrime, cPrime, bCoeff, Coefficients.tCoeff, Coefficients.mCoeff,
          Coefficients.pCoeff, Coefficients.qCoeff, map_add, map_sub,
          map_mul, map_pow, map_ofNat] <;>
        simp only [show (-1 : ℤ).toNat = 0 by decide,
          show (-2 : ℤ).toNat = 0 by decide, show (2 : ℤ).toNat = 2 by decide,
          pow_zero, mul_one] <;> first | (left; ring) | ring

theorem distinct_G3_full_expansion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    H w (-exponents 0) * G w 2 = 6 * geometric 1 - 2 * (phaseGeometric w 10 + phaseGeometric w 2) - 1 := by
  have h := distinctProduct_cross w (1 : Fin 4)
  have hb : distinctExponents (1 : Fin 4) = ![-1, 0, -1, 0, 1, 0] := rfl
  rw [hb] at h
  apply (numerator_isUnit w (-(![-1, 0, -1, 0, 1, 0] : Fin 6 → ℤ))).mul_right_cancel
  calc
    _ = (numerator w ![-1, 0, -1, 0, 1, 0] : PowerSeries K) := by simpa using h
    _ = _ := by
      have hc := Certificates.distinct_G3 (C w) X
        (geometric 1) (phaseGeometric w 10) (phaseGeometric w 2)
        (cyclotomic_C w hw)
        (phaseGeometric_mul w 0) (phaseGeometric_mul w 10) (phaseGeometric_mul w 2)
      rw [coe_numerator_eq_phaseNumerator w hw, coe_numerator_eq_phaseNumerator w hw]
      convert hc.symm using 1 <;>
        norm_num [phaseNumerator, Fin.prod_univ_succ, phasePolynomial, Int.reduceNeg,
          phaseGeometric, aPrime, cPrime, bCoeff, Coefficients.tCoeff, Coefficients.mCoeff,
          Coefficients.pCoeff, Coefficients.qCoeff, map_add, map_sub,
          map_mul, map_pow, map_ofNat] <;>
        simp only [show (-1 : ℤ).toNat = 0 by decide,
          show (-2 : ℤ).toNat = 0 by decide, show (2 : ℤ).toNat = 2 by decide,
          pow_zero, mul_one] <;> first | (left; ring) | ring

theorem distinct_G4_scaled_expansion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    3 * (H w (-exponents 0) * G w 3) = 3 + C (Coefficients.pCoeff w) *
      (3 * phaseGeometric w 11 - phaseGeometric w 10 + phaseGeometric w 2 - 3 * phaseGeometric w 1) := by
  have h := distinctProduct_cross w (2 : Fin 4)
  have hb : distinctExponents (2 : Fin 4) = ![0, -1, -1, 0, 1, 1] := rfl
  rw [hb] at h
  apply (numerator_isUnit w (-(![0, -1, -1, 0, 1, 1] : Fin 6 → ℤ))).mul_right_cancel
  calc
    _ = 3 * (numerator w ![0, -1, -1, 0, 1, 1] : PowerSeries K) := by
      calc
        _ = 3 * ((H w (-exponents 0) * G w 3) * (numerator w (-(![0, -1, -1, 0, 1, 1] : Fin 6 → ℤ)) : PowerSeries K)) := by ring
        _ = _ := by simpa using congrArg (fun f : PowerSeries K => 3 * f) h
    _ = _ := by
      have hc := Certificates.distinct_G4 (C w) X
        (phaseGeometric w 11) (phaseGeometric w 10) (phaseGeometric w 2) (phaseGeometric w 1)
        (cyclotomic_C w hw)
        (phaseGeometric_mul w 11) (phaseGeometric_mul w 10) (phaseGeometric_mul w 2) (phaseGeometric_mul w 1)
      rw [coe_numerator_eq_phaseNumerator w hw, coe_numerator_eq_phaseNumerator w hw]
      convert hc.symm using 1 <;>
        norm_num [phaseNumerator, Fin.prod_univ_succ, phasePolynomial, Int.reduceNeg,
          phaseGeometric, aPrime, cPrime, bCoeff, Coefficients.tCoeff, Coefficients.mCoeff,
          Coefficients.pCoeff, Coefficients.qCoeff, map_add, map_sub,
          map_mul, map_pow, map_ofNat] <;>
        simp only [show (-1 : ℤ).toNat = 0 by decide,
          show (-2 : ℤ).toNat = 0 by decide, show (2 : ℤ).toNat = 2 by decide,
          pow_zero, mul_one] <;> first | (left; ring) | ring

theorem distinct_G5_full_expansion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    H w (-exponents 0) * G w 4 = 1 + C (Coefficients.qCoeff w) * (phaseGeometric w 11 - phaseGeometric w 1) := by
  have h := distinctProduct_cross w (3 : Fin 4)
  have hb : distinctExponents (3 : Fin 4) = ![0, -1, 0, 0, 0, 1] := rfl
  rw [hb] at h
  apply (numerator_isUnit w (-(![0, -1, 0, 0, 0, 1] : Fin 6 → ℤ))).mul_right_cancel
  calc
    _ = (numerator w ![0, -1, 0, 0, 0, 1] : PowerSeries K) := by simpa using h
    _ = _ := by
      have hc := Certificates.distinct_G5 (C w) X
        (phaseGeometric w 11) (phaseGeometric w 1)
        (cyclotomic_C w hw)
        (phaseGeometric_mul w 11) (phaseGeometric_mul w 1)
      rw [coe_numerator_eq_phaseNumerator w hw, coe_numerator_eq_phaseNumerator w hw]
      convert hc.symm using 1 <;>
        norm_num [phaseNumerator, Fin.prod_univ_succ, phasePolynomial, Int.reduceNeg,
          phaseGeometric, aPrime, cPrime, bCoeff, Coefficients.tCoeff, Coefficients.mCoeff,
          Coefficients.pCoeff, Coefficients.qCoeff, map_add, map_sub,
          map_mul, map_pow, map_ofNat] <;>
        simp only [show (-1 : ℤ).toNat = 0 by decide,
          show (-2 : ℤ).toNat = 0 by decide, show (2 : ℤ).toNat = 2 by decide,
          pow_zero, mul_one] <;> first | (left; ring) | ring

end KanadeRussell.Tsuchioka.Scalar
