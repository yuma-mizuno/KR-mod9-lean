import KanadeRussell.Tsuchioka.MixedPhase

/-! Cyclic covariance of the creation part at the two mixed sixth-root poles. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

noncomputable def mixedCreationLog (w : K) (p : ℤ) (s t : Fin 3) : PowerSeries (Space K) :=
  rescale (MvPolynomial.C (w ^ (-p))) (creationLog s) + creationLog t

@[simp] theorem constantCoeff_mixedCreationLog (w : K) (p : ℤ) (s t : Fin 3) :
    constantCoeff (mixedCreationLog w p s t) = 0 := by
  simp only [mixedCreationLog, map_add, ← coeff_zero_eq_constantCoeff,
    coeff_rescale, pow_zero, one_mul]
  simp only [coeff_zero_eq_constantCoeff, constantCoeff_creationLog, add_zero]

theorem mixedCreationLog_cyclic (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    rescale (MvPolynomial.C (w ^ (-(2 * p)))) (mixedCreationLog w p s t) =
      mixedCreationLog w p t u := by
  apply PowerSeries.ext
  intro n
  simp only [mixedCreationLog, coeff_rescale, map_add, creationLog, coeff_mk]
  by_cases hn : IsMode n
  · simp only [dif_pos hn, ← map_pow]
    have he (q : ℤ) : (w ^ q) ^ n = w ^ (q * (n : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul]
    simp only [he, Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [← mul_assoc, ← add_mul, ← map_mul, ← map_add]
    congr 1
    congr 1
    exact by
      have h := mixed_phase_cycle_neg w hw p hp (⟨n, hn⟩ : Mode) i s t u hst hsu htu
      linear_combination (-4 / (n : K)) * h
  · simp [hn]

noncomputable def mixedCreation (w : K) (p : ℤ) (s t : Fin 3) : PowerSeries (Space K) :=
  rescale (MvPolynomial.C (w ^ (-p))) (creation s) * creation t

theorem mixedCreation_eq_exponential (w : K) (p : ℤ) (s t : Fin 3) :
    mixedCreation w p s t = exponential (mixedCreationLog w p s t) := by
  rw [mixedCreation, creation, rescale_exponential _ _ (constantCoeff_creationLog s)]
  change exponential _ * exponential (creationLog (K := K) t) = _
  rw [← exponential_add (by
    rw [← coeff_zero_eq_constantCoeff, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff, constantCoeff_creationLog]) (constantCoeff_creationLog t)]
  rfl

theorem mixedCreation_cyclic (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    rescale (MvPolynomial.C (w ^ (-(2 * p)))) (mixedCreation w p s t) =
      mixedCreation w p t u := by
  rw [mixedCreation_eq_exponential, mixedCreation_eq_exponential,
    rescale_exponential _ _ (constantCoeff_mixedCreationLog w p s t),
    mixedCreationLog_cyclic w hw p hp s t u hst hsu htu]

theorem mixedCreation_laurent (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (s t : Fin 3) :
    (mixedCreation w p s t : LaurentSeries (Space K)) =
      laurentRescale (phaseUnit w hw p) (creation (K := K) s : LaurentSeries (Space K)) *
        (creation (K := K) t : LaurentSeries (Space K)) := by
  rw [mixedCreation, PowerSeries.coe_mul, laurentRescale_powerSeries, phaseUnit_val]

theorem mixedCreation_laurent_cyclic (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    laurentRescale (phaseUnit w hw (2 * p))
        (laurentRescale (phaseUnit w hw p) (creation (K := K) s : LaurentSeries (Space K)) *
          (creation (K := K) t : LaurentSeries (Space K))) =
      laurentRescale (phaseUnit w hw p) (creation (K := K) t : LaurentSeries (Space K)) *
        (creation (K := K) u : LaurentSeries (Space K)) := by
  rw [← mixedCreation_laurent w hw p s t, laurentRescale_powerSeries, phaseUnit_val,
    mixedCreation_cyclic w hw p hp s t u hst hsu htu, mixedCreation_laurent]

end KanadeRussell.Tsuchioka.Fock
