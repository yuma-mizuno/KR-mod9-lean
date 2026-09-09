import KanadeRussell.Tsuchioka.OrbitPairingFactorization
import KanadeRussell.Tsuchioka.TensorNormalOrdering

/-! The exact tensor Wick factor for arbitrary D4 lattice pairs is the
integer binomial product of their twelve actual Cartan pairings. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open PowerSeries FormalSeries
open RootData (Lattice pairing coxeter rootWeight)

variable {K : Type*} [Field K] [CharZero K]

theorem orbitPairing_fourier (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta gamma : Lattice) (n : ℕ) :
    (∑ p : Fin 12, (pairing ((coxeter^[p.val]) beta) gamma : K) *
      w ^ (-((n : ℤ) * p.val))) =
      12 * contraction w n * rootWeight (w ^ (n : ℤ)) beta *
        rootWeight (w ^ (-(n : ℤ))) gamma := by
  have ht : (w ^ (-(n : ℤ))) ^ 12 = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    rw [Coefficients.zpow_eq_of_mod w hw _ 0 (by omega), zpow_zero]
  have hp (p : ℕ) : (w ^ (-(n : ℤ))) ^ p = w ^ (-((n : ℤ) * p)) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  have hfirst : RootData.firstOrbitPolynomial (w ^ (-(n : ℤ))) =
      12 * contraction w n := by
    rw [RootData.firstOrbitPolynomial_eq]
    simp only [RootData.orbitPairingPolynomial, hp, contraction, orbitPairing]
    ring
  have h := RootData.orbitPairingPolynomial_eq_weights (w ^ (-(n : ℤ))) ht beta gamma
  simp only [RootData.orbitPairingPolynomial, hp] at h
  rw [hfirst] at h
  have hi : (w ^ (-(n : ℤ)))⁻¹ = w ^ (n : ℤ) := by rw [zpow_neg, inv_inv]
  rw [hi] at h
  exact h

noncomputable def tensorOrbitLog (w : K) (beta gamma : Lattice) :
    PowerSeries (LaurentSeries (Space K)) :=
  ∑ p : Fin 12,
    PowerSeries.C (algebraMap ℚ (LaurentSeries (Space K))
      (pairing ((coxeter^[p.val]) beta) gamma : ℚ)) *
        logOneSub (ratioMonomial w p.val)

noncomputable def tensorOrbitProduct (w : K) (beta gamma : Lattice) :
    PowerSeries (LaurentSeries (Space K)) :=
  ∏ p : Fin 12, binomialFactor
    (pairing ((coxeter^[p.val]) beta) gamma : ℚ) (ratioMonomial w p.val)

theorem coeff_tensorOrbitLog_summand (w : K) (beta gamma : Lattice)
    (p : Fin 12) (n : ℕ) (hn : n ≠ 0) :
    coeff n (PowerSeries.C (algebraMap ℚ (LaurentSeries (Space K))
      (pairing ((coxeter^[p.val]) beta) gamma : ℚ)) *
        logOneSub (ratioMonomial w p.val)) =
      HahnSeries.single (-(n : ℤ)) (MvPolynomial.C
        (-(pairing ((coxeter^[p.val]) beta) gamma : K) / (n : K) *
          w ^ (-((n : ℤ) * p.val)))) := by
  rw [coeff_C_mul, logOneSub, coeff_mk, if_neg hn, ratioMonomial_pow]
  rw [rat_laurent_embedding, rat_laurent_embedding]
  simp only [map_div₀, map_intCast, map_natCast, map_one]
  have hc : (pairing ((coxeter^[p.val]) beta) gamma : LaurentSeries (Space K)) =
      HahnSeries.C (MvPolynomial.C (pairing ((coxeter^[p.val]) beta) gamma : K)) := by simp
  rw [hc]
  rw [← map_neg, ← map_neg, ← mul_assoc, ← map_mul, ← map_mul,
    HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, ← map_mul]
  congr 2
  ring

theorem coeff_tensorWickLog_same (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta gamma : Lattice) (s : Fin 3) (n : ℕ) :
    coeff n (tensorWickLog w beta gamma s s) =
      HahnSeries.single (-(n : ℤ)) (MvPolynomial.C
        (-12 * contraction w n * rootWeight (w ^ (n : ℤ)) beta *
          rootWeight (w ^ (-(n : ℤ))) gamma / (n : K))) := by
  rw [tensorWickLog, coeff_mk]
  by_cases hn : IsMode n
  · simp only [if_pos hn, if_true]
    congr 2
    ring
  · have hk := (contraction_eq_zero_iff w hw n).mpr hn
    simp [hn, hk]

theorem tensorWickLog_same_eq_orbitLog (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta gamma : Lattice) (s : Fin 3) :
    tensorWickLog w beta gamma s s = tensorOrbitLog w beta gamma := by
  apply PowerSeries.ext
  intro n
  rw [coeff_tensorWickLog_same w hw, tensorOrbitLog, map_sum]
  by_cases hn : n = 0
  · subst n
    simp [coeff_zero_eq_constantCoeff]
  · simp_rw [coeff_tensorOrbitLog_summand w beta gamma _ n hn]
    apply HahnSeries.ext
    funext e
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_single]
    by_cases he : e = -(n : ℤ)
    · simp only [he, if_pos, ← map_sum]
      congr 1
      calc
        _ = (-1 / (n : K)) * ∑ p : Fin 12,
            (pairing ((coxeter^[p.val]) beta) gamma : K) *
              w ^ (-((n : ℤ) * p.val)) := by
          rw [orbitPairing_fourier w hw]
          ring
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring
    · simp [he]

/-- All exponents are the actual integral Cartan pairings. -/
theorem exponential_tensorWickLog_same (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta gamma : Lattice) (s : Fin 3) :
    exponential (tensorWickLog w beta gamma s s) = tensorOrbitProduct w beta gamma := by
  rw [tensorWickLog_same_eq_orbitLog w hw, tensorOrbitLog,
    exponential_sum _ _ (by intro p hp; simp)]
  simp only [tensorOrbitProduct, binomialFactor_eq_exponential]

theorem tensorTwoSummands_same_orbitProduct (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (beta gamma : Lattice) (s : Fin 3) (f : Space K) :
    tensorTwoSummands w beta gamma s s f =
      tensorNormalProduct w beta gamma s s f *
        (tensorOrbitProduct w beta gamma : LaurentSeries (LaurentSeries (Space K))) := by
  rw [tensorTwoSummands_normalOrdered, exponential_tensorWickLog_same w hw]

end KanadeRussell.Tsuchioka.Fock
