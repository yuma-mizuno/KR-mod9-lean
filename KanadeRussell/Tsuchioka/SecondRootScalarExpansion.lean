import KanadeRussell.Tsuchioka.TensorAllRootKernel

/-! The full second-root self scalar is the conjugate first-root scalar,
with w replaced by -w. This follows from the actual Cartan exponents,
the unit denominators, and the checked first-root partial fractions. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace KanadeRussell.Tsuchioka.Scalar

open PowerSeries FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem cyclotomic_neg (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    (-w) ^ 4 - (-w) ^ 2 + 1 = 0 := by linear_combination hw

theorem rootScalar_second_second (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    rootScalar w (simpleRoot 1) (simpleRoot 1) = G (-w) 0 ^ 3 := by
  have h := rootScalar_cross w (simpleRoot 1) (simpleRoot 1)
  rw [RootData.rootPairingExponents_second_second] at h
  apply (orbitNumerator_isUnit w (-(![2, -1, 1, 0, -1, 1, -2, 1, -1, 0, 1, -1] :
    Fin 12 → ℤ))).mul_right_cancel
  calc
    _ = (orbitNumerator w ![2, -1, 1, 0, -1, 1, -2, 1, -1, 0, 1, -1] :
        PowerSeries K) := h
    _ = _ := by
      rw [G1_cube_expansion (-w) (cyclotomic_neg w hw)]
      have hc := Certificates.same_G1 (PowerSeries.C (-w)) X
        (phaseGeometric (-w) 4) (phaseGeometric (-w) 8)
        (phaseGeometric (-w) 5) (phaseGeometric (-w) 7) (eulerGeometric (-1))
        (cyclotomic_C (-w) (cyclotomic_neg w hw))
        (phaseGeometric_mul (-w) 4) (phaseGeometric_mul (-w) 8)
        (phaseGeometric_mul (-w) 5) (phaseGeometric_mul (-w) 7)
        (phaseEulerGeometric_mul (-w) 6)
      simp only [coe_orbitNumerator, negative_phase w hw]
      convert hc.symm using 1 <;>
        norm_num [Fin.prod_univ_succ, phasePolynomial, phaseGeometric,
          cPrime, rootSecondResidue, Coefficients.pCoeff,
          map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat] <;>
        simp only [show (-1 : ℤ).toNat = 0 by decide,
          show (-2 : ℤ).toNat = 0 by decide, show (2 : ℤ).toNat = 2 by decide, pow_zero, mul_one] <;> ring

theorem rootCommutatorKernel_second_second (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    rootCommutatorKernel w (simpleRoot 1) (simpleRoot 1) =
      fun n => Coefficients.pCoeff (-w) *
        (delta (w ^ (-4 : ℤ)) n - delta (w ^ 4) n) +
        rootSecondResidue (-w) * (delta w n - delta (w ^ (-1 : ℤ)) n) +
        (2 * cPrime (-w)) * eulerDelta (-1) n := by
  have hn := cyclotomic_neg w hw
  have h4 : (-w) ^ (-4 : ℤ) = w ^ (-4 : ℤ) := by
    have ha := negative_phase (-w) hn (4 : Fin 12)
    have hb := negative_phase w hw (4 : Fin 12)
    have ha' : (-w) ^ (-4 : ℤ) = -(w ^ 2) := by simpa [phasePolynomial] using ha
    have hb' : w ^ (-4 : ℤ) = -(w ^ 2) := by simpa [phasePolynomial] using hb
    exact ha'.trans hb'.symm
  have h5 : (-w) ^ (-5 : ℤ) = w := by
    simpa [phasePolynomial] using negative_phase (-w) hn (5 : Fin 12)
  have h5p : (-w) ^ 5 = w ^ (-1 : ℤ) := by
    have hi := congrArg Inv.inv h5
    simpa only [zpow_neg, inv_inv, zpow_ofNat, zpow_neg_one, pow_one] using hi
  change antisymmetricFourier (rootScalar w (simpleRoot 1) (simpleRoot 1)) = _
  rw [rootScalar_second_second w hw, G1_cube_fourier (-w) hn, h4, h5, h5p]
  simp [show (-w) ^ 4 = w ^ 4 by ring]

end KanadeRussell.Tsuchioka.Scalar
