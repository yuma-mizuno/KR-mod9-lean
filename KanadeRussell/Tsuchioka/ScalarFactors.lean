import KanadeRussell.Tsuchioka.NormalOrdering
import KanadeRussell.Tsuchioka.BinomialFactors

/-! Identification of the constructed Wick factor with the source's binomial product. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

/-- The inner Laurent monomial in w^(-p) zeta_1/zeta_2.
The outer power-series variable supplies the remaining factor. -/
noncomputable def ratioMonomial (w : K) (p : ℕ) : LaurentSeries (Space K) :=
  HahnSeries.single (-1 : ℤ) (MvPolynomial.C (w ^ (-(p : ℤ))))

theorem ratioMonomial_pow (w : K) (p n : ℕ) :
    ratioMonomial w p ^ n =
      HahnSeries.single (-(n : ℤ)) (MvPolynomial.C (w ^ (-((n : ℤ) * p)))) := by
  rw [ratioMonomial, HahnSeries.single_pow, ← map_pow]
  congr 1
  · simp [nsmul_eq_mul]
  · congr 1
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring

noncomputable def orbitLog (w : K) : PowerSeries (LaurentSeries (Space K)) :=
  ∑ p : Fin 12, C (algebraMap ℚ (LaurentSeries (Space K)) ((orbitPairing p : ℚ) / 3)) *
    logOneSub (ratioMonomial w p.val)

noncomputable def orbitProduct (w : K) : PowerSeries (LaurentSeries (Space K)) :=
  ∏ p : Fin 12, binomialFactor ((orbitPairing p : ℚ) / 3) (ratioMonomial w p.val)

theorem rat_laurent_embedding (r : ℚ) :
    algebraMap ℚ (LaurentSeries (Space K)) r =
      HahnSeries.C (MvPolynomial.C (algebraMap ℚ K r)) := by
  exact (RingHom.map_rat_algebraMap
    ((HahnSeries.C : Space K →+* LaurentSeries (Space K)).comp MvPolynomial.C) r).symm

theorem coeff_scaled_log (w : K) (p : Fin 12) (n : ℕ) (hn : n ≠ 0) :
    coeff n
      (C (algebraMap ℚ (LaurentSeries (Space K)) ((orbitPairing p : ℚ) / 3)) *
        logOneSub (ratioMonomial w p.val)) =
      HahnSeries.single (-(n : ℤ))
        (MvPolynomial.C (-((orbitPairing p : K) / 3 / (n : K)) *
          w ^ (-((n : ℤ) * p.val)))) := by
  rw [coeff_C_mul, logOneSub, coeff_mk, if_neg hn, ratioMonomial_pow]
  rw [rat_laurent_embedding, rat_laurent_embedding]
  simp only [map_div₀, map_intCast, map_natCast, map_ofNat, map_one]
  rw [← map_neg, ← map_neg, ← mul_assoc, ← map_mul, ← map_mul,
    HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, ← map_mul]
  congr 2
  ring

theorem coeff_rootFactorLog (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : ℕ) :
    coeff n (rootFactorLog w) =
      HahnSeries.single (-(n : ℤ)) (MvPolynomial.C (-4 * contraction w n / (n : K))) := by
  rw [rootFactorLog, coeff_mk]
  by_cases hn : IsMode n
  · simp [hn]
  · have hk := (contraction_eq_zero_iff w hw n).mpr hn
    simp [hn, hk]

theorem rootFactorLog_eq_orbitLog (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    rootFactorLog w = orbitLog w := by
  apply PowerSeries.ext
  intro n
  rw [coeff_rootFactorLog w hw, orbitLog, map_sum]
  by_cases hn : n = 0
  · subst n
    simp [coeff_zero_eq_constantCoeff]
  · simp_rw [coeff_scaled_log w _ n hn]
    apply HahnSeries.ext
    funext e
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_single]
    by_cases he : e = -(n : ℤ)
    · simp only [he, if_pos, ← map_sum]
      congr 1
      rw [contraction]
      calc
        -4 * ((1 / 12 : K) * ∑ p : Fin 12,
          (orbitPairing p : K) * w ^ (-((n : ℤ) * p.val))) / (n : K) =
          (-1 / (3 * (n : K))) * ∑ p : Fin 12,
            (orbitPairing p : K) * w ^ (-((n : ℤ) * p.val)) := by
              simp [div_eq_mul_inv, mul_inv_rev]
              ring
        _ = ∑ p : Fin 12, -((orbitPairing p : K) / 3 / (n : K)) *
              w ^ (-((n : ℤ) * p.val)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          simp [div_eq_mul_inv, mul_inv_rev]
          ring
    · simp [he]

/-- Identification in every coefficient, using the full root orbit. -/
theorem rootFactor_eq_orbitProduct (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    rootFactor w = orbitProduct w := by
  rw [rootFactor, rootFactorLog_eq_orbitLog w hw, orbitLog,
    exponential_sum _ _ (by intro p hp; simp)]
  simp only [orbitProduct, binomialFactor_eq_exponential]

def firstRootExponents : Fin 6 → ℤ := ![2, 1, 1, 0, -1, -1]

/-- Exactly H_(a_0,...,a_5) from Section 3.2, as rational binomial series. -/
noncomputable def sourceH (w : K) (a : Fin 6 → ℤ) :
    PowerSeries (LaurentSeries (Space K)) :=
  ∏ p : Fin 6,
    binomialFactor ((a p : ℚ) / 3) (ratioMonomial w p.val) *
      binomialFactor (-((a p : ℚ) / 3)) (-ratioMonomial w p.val)

/-- The source's G1, with all six exponents kept explicitly. -/
noncomputable def sourceG1 (w : K) : PowerSeries (LaurentSeries (Space K)) :=
  sourceH w firstRootExponents

theorem root_pow_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) : w ^ 6 = -1 := by
  linear_combination (w ^ 2 + 1) * hw

theorem ratioMonomial_add_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (p : ℕ) :
    ratioMonomial w (6 + p) = -ratioMonomial w p := by
  have hz : w ^ (-6 : ℤ) = -1 := by
    rw [show (-6 : ℤ) = -(6 : ℕ) from rfl, zpow_neg, zpow_natCast, root_pow_six w hw]
    simp
  unfold ratioMonomial
  rw [Nat.cast_add, neg_add, zpow_add₀ (Coefficients.root_ne_zero w hw)]
  norm_num only [Nat.cast_ofNat]
  rw [hz]
  simp [map_neg, HahnSeries.single_neg]

theorem orbitPairing_first_half (p : Fin 6) :
    orbitPairing (Fin.castAdd 6 p) = firstRootExponents p := by
  fin_cases p <;> decide

theorem orbitPairing_second_half (p : Fin 6) :
    orbitPairing (Fin.natAdd 6 p) = -firstRootExponents p := by
  fin_cases p <;> decide

theorem orbitProduct_eq_sourceG1 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    orbitProduct w = sourceG1 w := by
  rw [orbitProduct, Fin.prod_univ_add (a := 6) (b := 6), ← Finset.prod_mul_distrib]
  unfold sourceG1 sourceH
  apply Finset.prod_congr rfl
  intro p hp
  rw [orbitPairing_first_half, orbitPairing_second_half]
  have hs : ratioMonomial w (p.val + 6) = -ratioMonomial w p.val := by
    simpa [Nat.add_comm] using ratioMonomial_add_six w hw p.val
  simp [hs, neg_div]

/-- The concrete Wick scalar is the whole binomial product G1 used by Tsuchioka. -/
theorem rootFactor_eq_sourceG1 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    rootFactor w = sourceG1 w :=
  (rootFactor_eq_orbitProduct w hw).trans (orbitProduct_eq_sourceG1 w hw)

/-- Same-position normal ordering with the actual source G1. -/
theorem annihilation_creation_same_source (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (s : Fin 3) :
    PowerSeries.map (annihilation w s) (creation (K := K) s) =
      PowerSeries.map HahnSeries.C (creation (K := K) s) * sourceG1 w ^ 2 := by
  rw [← rootFactor_eq_sourceG1 w hw]
  exact annihilation_creation_same w s

/-- Distinct-position normal ordering with the actual source G1. -/
theorem annihilation_creation_distinct_source (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (s t : Fin 3) (hst : s ≠ t) :
    PowerSeries.map (annihilation w s) (creation (K := K) t) * sourceG1 w =
      PowerSeries.map HahnSeries.C (creation (K := K) t) := by
  rw [← rootFactor_eq_sourceG1 w hw]
  exact annihilation_creation_distinct w s t hst

end KanadeRussell.Tsuchioka.Fock
