import KanadeRussell.Tsuchioka.SourceFourier
import KanadeRussell.Tsuchioka.SourceCoefficients

/-! The two scalar Fourier identities for the actual source G6 combination. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Scalar

open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

theorem same_G6_fourier (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    antisymmetricFourier (G w 0 ^ 2 * G6 w) =
      fun n => 4 * (1 - 3 * (Coefficients.pCoeff w / Coefficients.qCoeff w)) *
        eulerDelta (-1) n -
        Coefficients.pCoeff w * (delta (w ^ 4) n - delta (w ^ (-4 : ℤ)) n) := by
  have hf : G w 0 ^ 2 * G6 w =
      G w 0 ^ 2 * G w 3 -
        C (Coefficients.pCoeff w / Coefficients.qCoeff w) * (G w 0 ^ 2 * G w 4) := by
    unfold G6
    ring
  have h4 : antisymmetricFourier (G w 0 ^ 2 * G w 3) =
      fun n => 4 * eulerDelta (-1) n := same_G4_fourier w
  rw [hf, antisymmetricFourier_sub, h4, antisymmetricFourier_C_mul, same_G5_fourier w hw]
  funext n
  simp only [Pi.sub_apply]
  have hq := div_mul_cancel₀ (Coefficients.pCoeff w) (Coefficients.qCoeff_ne_zero w hw)
  linear_combination -(delta (w ^ 4) n - delta (w ^ (-4 : ℤ)) n) * hq

theorem distinct_G6_fourier (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    antisymmetricFourier (H w (-exponents 0) * G6 w) =
      fun n => (Coefficients.pCoeff w / 3) *
        (delta (w ^ (-2 : ℤ)) n - delta (w ^ 2) n) := by
  have hf : H w (-exponents 0) * G6 w =
      H w (-exponents 0) * G w 3 -
        C (Coefficients.pCoeff w / Coefficients.qCoeff w) *
          (H w (-exponents 0) * G w 4) := by
    unfold G6
    ring
  rw [hf, antisymmetricFourier_sub, distinct_G4_fourier w hw,
    antisymmetricFourier_C_mul, distinct_G5_fourier w hw]
  funext n
  simp only [Pi.sub_apply]
  have hq := div_mul_cancel₀ (Coefficients.pCoeff w) (Coefficients.qCoeff_ne_zero w hw)
  linear_combination -(delta w n - delta (w ^ (-1 : ℤ)) n) * hq

end KanadeRussell.Tsuchioka.Scalar
