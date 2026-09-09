import KanadeRussell.Tsuchioka.TensorAllRootKernel
import KanadeRussell.Tsuchioka.MixedRootScalarCertificates

/-! Both rational mixed-root expansions and their complete four-pole
bilateral Fourier identity, at every integer exponent. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace KanadeRussell.Tsuchioka.Scalar

open PowerSeries FormalSeries
open RootData (simpleRoot rootPairingExponents)

variable {K : Type*} [Field K] [CharZero K]

def mixedRootPole : Fin 4 → Fin 12 := ![0, 2, 9, 11]

def mixedRootResidue (w : K) : Fin 4 → K :=
  ![-Coefficients.pCoeff w, Coefficients.pCoeff (-w),
    -Coefficients.pCoeff (-w), Coefficients.pCoeff w]

theorem sum_mixedRootResidue (w : K) : ∑ k : Fin 4, mixedRootResidue w k = 0 := by
  simp [mixedRootResidue, Fin.sum_univ_succ]

theorem coe_orbitNumerator_phase (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (e : Fin 12 → ℤ) :
    (orbitNumerator w e : PowerSeries K) =
      ∏ p : Fin 12, (1 - PowerSeries.C (phasePolynomial w p) * X) ^ (e p).toNat := by
  simp only [coe_orbitNumerator, negative_phase w hw]

theorem rootScalar_first_second_expansion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    rootScalar w (simpleRoot 0) (simpleRoot 1) =
      1 + ∑ k : Fin 4, PowerSeries.C (mixedRootResidue w k) *
        phaseGeometric w (mixedRootPole k) := by
  have h := rootScalar_cross w (simpleRoot 0) (simpleRoot 1)
  rw [RootData.rootPairingExponents_first_second] at h
  apply (orbitNumerator_isUnit w (-(![-1, 0, -1, 1, 0, 1, 1, 0, 1, -1, 0, -1] :
    Fin 12 → ℤ))).mul_right_cancel
  calc
    _ = (orbitNumerator w ![-1, 0, -1, 1, 0, 1, 1, 0, 1, -1, 0, -1] :
        PowerSeries K) := h
    _ = _ := by
      have hc := Certificates.mixed_first_second (PowerSeries.C w) X
        (phaseGeometric w 0) (phaseGeometric w 2) (phaseGeometric w 9) (phaseGeometric w 11)
        (cyclotomic_C w hw)
        (phaseGeometric_mul w 0) (by simpa [phasePolynomial, neg_add_eq_sub] using phaseGeometric_mul w 2)
        (phaseGeometric_mul w 9) (phaseGeometric_mul w 11)
      rw [coe_orbitNumerator_phase w hw, coe_orbitNumerator_phase w hw]
      convert hc.symm using 1 <;>
        norm_num [mixedRootResidue, mixedRootPole, Coefficients.pCoeff,
          Fin.sum_univ_succ, Fin.prod_univ_succ, phasePolynomial,
          map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat] <;>
        simp only [show (-1 : ℤ).toNat = 0 by decide, pow_zero, mul_one] <;> ring

theorem rootScalar_second_first_expansion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    rootScalar w (simpleRoot 1) (simpleRoot 0) =
      1 - ∑ k : Fin 4, PowerSeries.C (mixedRootResidue w k) *
        geometric ((phasePolynomial w (mixedRootPole k))⁻¹) := by
  have h := rootScalar_cross w (simpleRoot 1) (simpleRoot 0)
  rw [RootData.rootPairingExponents_second_first] at h
  apply (orbitNumerator_isUnit w (-(![-1, -1, 0, -1, 1, 0, 1, 1, 0, 1, -1, 0] :
    Fin 12 → ℤ))).mul_right_cancel
  calc
    _ = (orbitNumerator w ![-1, -1, 0, -1, 1, 0, 1, 1, 0, 1, -1, 0] :
        PowerSeries K) := h
    _ = _ := by
      have hc := Certificates.mixed_second_first (PowerSeries.C w) X
        (phaseGeometric w 0) (phaseGeometric w 1) (phaseGeometric w 3) (phaseGeometric w 10)
        (cyclotomic_C w hw)
        (phaseGeometric_mul w 0) (phaseGeometric_mul w 1)
        (phaseGeometric_mul w 3) (phaseGeometric_mul w 10)
      rw [coe_orbitNumerator_phase w hw, coe_orbitNumerator_phase w hw]
      simp only [← phasePolynomial_opposite w hw]
      convert hc.symm using 1 <;>
        norm_num [mixedRootResidue, mixedRootPole, Coefficients.pCoeff,
          Fin.sum_univ_succ, Fin.prod_univ_succ, phasePolynomial, oppositePhase, phaseGeometric,
          map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat] <;>
        simp only [show (-1 : ℤ).toNat = 0 by decide, pow_zero, mul_one] <;> ring

/-- Reciprocal simple-pole expansions with zero total residue give a
bilateral delta sum, including the constant coefficient. -/
theorem reciprocal_geometric_fourier {ι : Type*} [Fintype ι]
    (r u : ι → K) (hr : ∑ k, r k = 0) (n : ℤ) :
    positive (1 + ∑ k, PowerSeries.C (r k) * geometric (u k)) n -
      positive (1 - ∑ k, PowerSeries.C (r k) * geometric (u k)⁻¹) (-n) =
        ∑ k, r k * (u k) ^ n := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast]
    by_cases hn : n = 0
    · subst n
      simp [positive, hr]
    · rw [positive_nat, positive_neg_nat _ n (by omega)]
      simp [hn, coeff_geometric]
  | negSucc n =>
    change positive _ (-((n + 1 : ℕ) : ℤ)) - positive _ (-(-((n + 1 : ℕ) : ℤ))) =
      ∑ k, r k * (u k) ^ (-((n + 1 : ℕ) : ℤ))
    rw [positive_neg_nat _ _ (by omega), neg_neg, positive_nat]
    simp only [map_sub, map_sum, coeff_C_mul, coeff_one, Nat.succ_ne_zero, if_false,
      coeff_geometric, zero_sub, neg_neg, zpow_neg, zpow_natCast, inv_pow]

theorem rootCommutatorKernel_first_second (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    rootCommutatorKernel w (simpleRoot 0) (simpleRoot 1) =
      fun n => ∑ k : Fin 4, mixedRootResidue w k *
        (phasePolynomial w (mixedRootPole k)) ^ n := by
  funext n
  simp only [rootCommutatorKernel, rootScalar_first_second_expansion w hw,
    rootScalar_second_first_expansion w hw, phaseGeometric]
  exact reciprocal_geometric_fourier (mixedRootResidue w)
    (fun k => phasePolynomial w (mixedRootPole k)) (sum_mixedRootResidue w) n

end KanadeRussell.Tsuchioka.Scalar
