import KanadeRussell.Tsuchioka.PartialFractions
import KanadeRussell.Tsuchioka.SourceFourier

/-! The scalar Fourier identity for the first generalized commutator. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace KanadeRussell.Tsuchioka.Scalar

open scoped BigOperators
open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

/-- The second-root residue printed in source Section 3.4. -/
def rootSecondResidue (w : K) : K := -52 + 104 * w ^ 2 + 90 * w ^ 3

theorem G1_cube_eq_H (w : K) :
    G w 0 ^ 3 = H w (fun p => 3 * exponents 0 p) := by
  change H w (exponents 0) ^ 3 = _
  rw [pow_succ, pow_two, ← H_add, ← H_add]
  congr 1
  funext p
  simp only [Pi.add_apply]
  ring

theorem G1_cube_cross (w : K) :
    G w 0 ^ 3 * (numerator w (-exponents 0) : PowerSeries K) =
      (numerator w (exponents 0) : PowerSeries K) := by
  rw [G1_cube_eq_H]
  exact H_integer_cross w (exponents 0)

theorem G1_cube_expansion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    G w 0 ^ 3 =
      1 + C (Coefficients.pCoeff w) * (phaseGeometric w 4 - phaseGeometric w 8) +
        C (rootSecondResidue w) * (phaseGeometric w 5 - phaseGeometric w 7) +
        C (2 * cPrime w) * eulerGeometric (-1) := by
  have h := G1_cube_cross w
  have hb : exponents (0 : Fin 5) = ![2, 1, 1, 0, -1, -1] := rfl
  rw [hb] at h
  apply (numerator_isUnit w (-(![2, 1, 1, 0, -1, -1] : Fin 6 → ℤ))).mul_right_cancel
  calc
    _ = (numerator w ![2, 1, 1, 0, -1, -1] : PowerSeries K) := h
    _ = _ := by
      have hc := Certificates.same_G1 (C w) X
        (phaseGeometric w 4) (phaseGeometric w 8)
        (phaseGeometric w 5) (phaseGeometric w 7) (eulerGeometric (-1))
        (cyclotomic_C w hw)
        (phaseGeometric_mul w 4) (phaseGeometric_mul w 8)
        (phaseGeometric_mul w 5) (phaseGeometric_mul w 7) (phaseEulerGeometric_mul w 6)
      rw [coe_numerator_eq_phaseNumerator w hw, coe_numerator_eq_phaseNumerator w hw]
      convert hc.symm using 1 <;>
        norm_num [phaseNumerator, Fin.prod_univ_succ, phasePolynomial, Int.reduceNeg,
          phaseGeometric, cPrime, rootSecondResidue, Coefficients.pCoeff,
          map_add, map_sub, map_mul, map_pow, map_ofNat] <;>
        simp only [show (-1 : ℤ).toNat = 0 by decide,
          show (-2 : ℤ).toNat = 0 by decide, show (2 : ℤ).toNat = 2 by decide,
          pow_zero, mul_one] <;> first | (left; ring) | ring


/-- The complete scalar delta identity underlying the first generalized commutator. -/
theorem G1_cube_fourier (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    antisymmetricFourier (G w 0 ^ 3) =
      fun n => Coefficients.pCoeff w *
        (delta (w ^ (-4 : ℤ)) n - delta (w ^ 4) n) +
        rootSecondResidue w * (delta (w ^ (-5 : ℤ)) n - delta (w ^ 5) n) +
        (2 * cPrime w) * eulerDelta (-1) n := by
  have h8 := phasePolynomial_opposite w hw (4 : Fin 12)
  have h7 := phasePolynomial_opposite w hw (5 : Fin 12)
  change phasePolynomial w 8 = (phasePolynomial w 4)⁻¹ at h8
  change phasePolynomial w 7 = (phasePolynomial w 5)⁻¹ at h7
  have hform : G w 0 ^ 3 =
      ((1 + C (2 * cPrime w) * eulerGeometric (-1)) +
        C (Coefficients.pCoeff w) *
          (geometric (phasePolynomial w 4) - geometric (phasePolynomial w 4)⁻¹)) +
        C (rootSecondResidue w) *
          (geometric (phasePolynomial w 5) - geometric (phasePolynomial w 5)⁻¹) := by
    rw [G1_cube_expansion w hw, ← h8, ← h7]
    simp only [phaseGeometric]
    ring
  rw [hform, antisymmetricFourier_add, antisymmetric_euler_pair,
    antisymmetricFourier_C_mul, antisymmetric_geometric_pair]
  rw [phasePolynomial_inverse w hw 4, phasePolynomial_inverse w hw 5,
    ← negative_phase w hw 4, ← negative_phase w hw 5]
  norm_num only [show (4 : Fin 12).val = 4 by rfl,
    show (5 : Fin 12).val = 5 by rfl, Nat.cast_ofNat]
  funext n
  simp only [Pi.add_apply]
  ring

end KanadeRussell.Tsuchioka.Scalar
