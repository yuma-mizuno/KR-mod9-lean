import KanadeRussell.Tsuchioka.PartialFractions
import KanadeRussell.Tsuchioka.FourierAssembly

/-! The remaining six Fourier identities of source Proposition 3.3. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Scalar

open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

theorem same_G2_fourier (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    symmetricFourier (G w 0 ^ 2 * G w 1) =
      fun n => aPrime w * (delta (w ^ (-4 : ℤ)) n + delta (w ^ 4) n) +
        Coefficients.tCoeff w * (delta (w ^ (-5 : ℤ)) n + delta (w ^ 5) n) +
        cPrime w * delta (-1) n := by
  have h8 := phasePolynomial_opposite w hw (4 : Fin 12)
  have h7 := phasePolynomial_opposite w hw (5 : Fin 12)
  change phasePolynomial w 8 = (phasePolynomial w 4)⁻¹ at h8
  change phasePolynomial w 7 = (phasePolynomial w 5)⁻¹ at h7
  have h := symmetric_weighted_pairs (aPrime w) (Coefficients.tCoeff w) (cPrime w)
    (phasePolynomial w 4) (phasePolynomial w 5) (-1) (by simp)
    (by dsimp [aPrime, cPrime, Coefficients.tCoeff]; ring)
  conv_lhs at h => rw [← h8, ← h7]
  conv_rhs at h =>
    rw [phasePolynomial_inverse w hw 4, phasePolynomial_inverse w hw 5,
      ← negative_phase w hw 4, ← negative_phase w hw 5]
  norm_num only [show (1 : Fin 12).val = 1 by rfl,
    show (2 : Fin 12).val = 2 by rfl, show (4 : Fin 12).val = 4 by rfl,
    show (5 : Fin 12).val = 5 by rfl, Nat.cast_ofNat, pow_one] at h
  rw [same_G2_full_expansion w hw]
  exact h

theorem same_G3_fourier (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    symmetricFourier (G w 0 ^ 2 * G w 2) =
      fun n => Coefficients.mCoeff w * (delta (w ^ (-5 : ℤ)) n + delta (w ^ 5) n) +
        bCoeff w * delta (-1) n := by
  have h7 := phasePolynomial_opposite w hw (5 : Fin 12)
  change phasePolynomial w 7 = (phasePolynomial w 5)⁻¹ at h7
  have h := symmetric_weighted_pairs (Coefficients.mCoeff w) 0 (bCoeff w)
    (phasePolynomial w 5) 1 (-1) (by simp)
    (by dsimp [bCoeff, Coefficients.mCoeff]; ring)
  simp only [map_zero, zero_mul, add_zero, zero_add] at h
  conv_lhs at h => rw [← h7]
  conv_rhs at h =>
    rw [phasePolynomial_inverse w hw 5, ← negative_phase w hw 5]
  norm_num only [show (1 : Fin 12).val = 1 by rfl,
    show (2 : Fin 12).val = 2 by rfl, show (4 : Fin 12).val = 4 by rfl,
    show (5 : Fin 12).val = 5 by rfl, Nat.cast_ofNat, pow_one] at h
  rw [same_G3_full_expansion w hw]
  exact h


theorem distinct_G3_fourier (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    symmetricFourier (H w (-exponents 0) * G w 2) =
      fun n => 6 * delta 1 n -
        2 * (delta (w ^ 2) n + delta (w ^ (-2 : ℤ)) n) := by
  have h10 := phasePolynomial_opposite w hw (2 : Fin 12)
  change phasePolynomial w 10 = (phasePolynomial w 2)⁻¹ at h10
  have h := symmetric_weighted_pairs (-2 : K) 0 6
    (phasePolynomial w 2) 1 1 (by simp) (by norm_num)
  simp only [map_zero, zero_mul, add_zero, zero_add] at h
  conv_lhs at h => rw [← h10]
  conv_rhs at h =>
    rw [phasePolynomial_inverse w hw 2, ← negative_phase w hw 2]
  norm_num only [show (1 : Fin 12).val = 1 by rfl,
    show (2 : Fin 12).val = 2 by rfl, show (4 : Fin 12).val = 4 by rfl,
    show (5 : Fin 12).val = 5 by rfl, Nat.cast_ofNat, pow_one] at h
  rw [distinct_G3_full_expansion w hw]
  convert h using 1
  · apply congrArg symmetricFourier
    norm_num only [map_neg, map_ofNat, phaseGeometric]
    ring
  · funext n
    ring

theorem same_G5_fourier (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    antisymmetricFourier (G w 0 ^ 2 * G w 4) =
      fun n => 12 * eulerDelta (-1) n +
        Coefficients.qCoeff w * (delta (w ^ 4) n - delta (w ^ (-4 : ℤ)) n) := by
  have h8 := phasePolynomial_opposite w hw (4 : Fin 12)
  change phasePolynomial w 8 = (phasePolynomial w 4)⁻¹ at h8
  have h := antisymmetric_euler_pair (12 : K) (Coefficients.qCoeff w)
    (phasePolynomial w 4)⁻¹
  simp only [inv_inv] at h
  conv_lhs at h => rw [← h8]
  conv_rhs at h =>
    rw [phasePolynomial_inverse w hw 4, ← negative_phase w hw 4]
  norm_num only [show (1 : Fin 12).val = 1 by rfl,
    show (2 : Fin 12).val = 2 by rfl, show (4 : Fin 12).val = 4 by rfl,
    show (5 : Fin 12).val = 5 by rfl, Nat.cast_ofNat, pow_one] at h
  rw [same_G5_full_expansion w hw]
  simpa only [map_ofNat, phaseGeometric] using h

theorem distinct_G5_fourier (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    antisymmetricFourier (H w (-exponents 0) * G w 4) =
      fun n => Coefficients.qCoeff w * (delta w n - delta (w ^ (-1 : ℤ)) n) := by
  have h11 := phasePolynomial_opposite w hw (1 : Fin 12)
  change phasePolynomial w 11 = (phasePolynomial w 1)⁻¹ at h11
  have h := antisymmetric_euler_pair (0 : K) (Coefficients.qCoeff w)
    (phasePolynomial w 1)⁻¹
  simp only [map_zero, zero_mul, add_zero, zero_add, inv_inv] at h
  conv_lhs at h => rw [← h11]
  conv_rhs at h =>
    rw [phasePolynomial_inverse w hw 1, ← negative_phase w hw 1]
  norm_num only [show (1 : Fin 12).val = 1 by rfl,
    show (2 : Fin 12).val = 2 by rfl, show (4 : Fin 12).val = 4 by rfl,
    show (5 : Fin 12).val = 5 by rfl, Nat.cast_ofNat, pow_one] at h
  rw [distinct_G5_full_expansion w hw]
  simpa only [map_ofNat, phaseGeometric, pow_one] using h

theorem distinct_G4_fourier (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    antisymmetricFourier (H w (-exponents 0) * G w 3) =
      fun n => Coefficients.pCoeff w *
        (delta w n - delta (w ^ 2) n / 3 + delta (w ^ (-2 : ℤ)) n / 3 -
          delta (w ^ (-1 : ℤ)) n) := by
  have h11 := phasePolynomial_opposite w hw (1 : Fin 12)
  have h10 := phasePolynomial_opposite w hw (2 : Fin 12)
  change phasePolynomial w 11 = (phasePolynomial w 1)⁻¹ at h11
  change phasePolynomial w 10 = (phasePolynomial w 2)⁻¹ at h10
  have hform : 3 * (H w (-exponents 0) * G w 3) =
      C (3 : K) +
      C (3 * Coefficients.pCoeff w) *
        (geometric (phasePolynomial w 1)⁻¹ - geometric (phasePolynomial w 1)) +
      C (-Coefficients.pCoeff w) *
        (geometric (phasePolynomial w 2)⁻¹ - geometric (phasePolynomial w 2)) := by
    rw [distinct_G4_scaled_expansion w hw, ← h11, ← h10]
    simp only [phaseGeometric, map_ofNat, map_mul, map_neg]
    ring
  have h := congrArg antisymmetricFourier hform
  have hpair := antisymmetric_weighted_pairs (3 : K)
    (3 * Coefficients.pCoeff w) (-Coefficients.pCoeff w)
    (phasePolynomial w 1)⁻¹ (phasePolynomial w 2)⁻¹
  simp only [inv_inv] at hpair
  rw [show (3 : PowerSeries K) = C (3 : K) by norm_num only [map_ofNat],
    antisymmetricFourier_C_mul, hpair] at h
  conv_rhs at h =>
    rw [phasePolynomial_inverse w hw 1, phasePolynomial_inverse w hw 2,
      ← negative_phase w hw 1, ← negative_phase w hw 2]
  norm_num only [show (1 : Fin 12).val = 1 by rfl,
    show (2 : Fin 12).val = 2 by rfl, show (4 : Fin 12).val = 4 by rfl,
    show (5 : Fin 12).val = 5 by rfl, Nat.cast_ofNat, pow_one] at h
  funext n
  have hn := congrFun h n
  linear_combination (1 / 3) * hn

end KanadeRussell.Tsuchioka.Scalar
