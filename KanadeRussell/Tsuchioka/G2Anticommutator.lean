import KanadeRussell.Tsuchioka.OperatorKernels
import KanadeRussell.Tsuchioka.SourceFourier

/-! The G2 anticommutator of source Theorem 3.2, on the constructed Fock modes. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

theorem sameResidue_G2 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    sameResidue w f a b (Scalar.symmetricFourier (Scalar.G w 0 ^ 2 * Scalar.G w 1)) =
      (Scalar.aPrime w * (w ^ (-2 * a + 2 * b) + w ^ (2 * a - 2 * b)) / 12) •
        mode w (a + b) f +
      (Coefficients.tCoeff w * (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) / 12) •
        secondRootMode w (a + b) f +
      (if a + b = 0 then (Scalar.cPrime w * (-1 : K) ^ a / 48) • f else 0) := by
  rw [Scalar.same_G2_fourier w hw]
  change sameResidue w f a b
    (Scalar.aPrime w • (Scalar.delta (w ^ (-4 : ℤ)) + Scalar.delta (w ^ 4)) +
      Coefficients.tCoeff w • (Scalar.delta (w ^ (-5 : ℤ)) + Scalar.delta (w ^ 5)) +
      Scalar.cPrime w • Scalar.delta (-1 : K)) = _
  simp only [map_add, map_smul, sameResidue_delta_four w hw,
    sameResidue_delta_eight w hw, sameResidue_delta_five w hw,
    sameResidue_delta_seven w hw, sameResidue_delta_central w hw]
  by_cases hab : a + b = 0 <;> simp only [hab, if_true, if_false, smul_add, smul_smul,
    smul_zero, add_zero] <;> module

theorem mixedResidue_G2 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    mixedResidue w f a b
      (Scalar.symmetricFourier (Scalar.H w (-Scalar.exponents 0) * Scalar.G w 1)) =
      ((-1 : K) ^ (a + b) / 3) • mode w (a + b) f := by
  change mixedResidue w f a b
    (positive (Scalar.H w (-Scalar.exponents 0) * Scalar.G w 1) +
      reflect (positive (Scalar.H w (-Scalar.exponents 0) * Scalar.G w 1))) = _
  rw [Scalar.distinct_G2_fourier w]
  change mixedResidue w f a b ((2 : K) • Scalar.delta (1 : K)) = _
  rw [map_smul, mixedResidue_delta_one w hw, smul_smul]
  congr 1
  ring

/-- The second relation of source Theorem 3.2. Its left side is a finite
convolution on every polynomial input, and every operator on the right is
constructed on the same Fock space. -/
theorem G2_anticommutator (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    quadraticConvolution w (Scalar.G w 1) f a b +
      quadraticConvolution w (Scalar.G w 1) f b a =
      (Scalar.aPrime w * (w ^ (-2 * a + 2 * b) + w ^ (2 * a - 2 * b)) / 12) •
        mode w (a + b) f +
      (Coefficients.tCoeff w * (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) / 12) •
        secondRootMode w (a + b) f +
      (if a + b = 0 then (Scalar.cPrime w * (-1 : K) ^ a / 48) • f else 0) +
      ((-1 : K) ^ (a + b) / 3) • mode w (a + b) f := by
  rw [quadraticConvolution_symmetric_kernel w hw, sameResidue_G2 w hw,
    mixedResidue_G2 w hw]

end KanadeRussell.Tsuchioka.Fock
