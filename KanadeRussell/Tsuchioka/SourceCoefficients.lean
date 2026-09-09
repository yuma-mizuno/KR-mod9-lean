import KanadeRussell.Tsuchioka.SourceSeries

/-! Low source coefficients used in the pair straightening relations. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Scalar

open scoped BigOperators
open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

@[simp] theorem coeff_zero_G (w : K) (i : Fin 5) : coeff 0 (G w i) = 1 := by
  simp [G]

theorem coeff_one_H (w : K) (a : Fin 6 → ℤ) :
    coeff 1 (H w a) = ∑ p : Fin 6, -(2 : K) / 3 * a p * w ^ (-(p.val : ℤ)) := by
  norm_num [H, Fin.prod_univ_succ, Fin.sum_univ_succ, coeff_one_mul,
    coeff_binomialFactor, Ring.choose_one_right]
  ring

/-- The source definition of G6 retains its actual P/Q coefficient. -/
noncomputable def G6 (w : K) : PowerSeries K :=
  G w 3 - C (Coefficients.pCoeff w / Coefficients.qCoeff w) * G w 4

theorem coeff_zero_G6 (w : K) :
    coeff 0 (G6 w) = 1 - Coefficients.pCoeff w / Coefficients.qCoeff w := by
  simp [G6, G]


theorem coeff_one_G1 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    coeff 1 (G w 0) = (-6 - 4 * w + 2 * w ^ 3) / 3 := by
  rw [G, coeff_one_H, show exponents (0 : Fin 5) = (![2, 1, 1, 0, -1, -1] : Fin 6 → ℤ) by rfl]
  norm_num [exponents, Fin.sum_univ_succ, Coefficients.zpow_mod_twelve w hw, Int.toNat]
  linear_combination (-(2 / 3) * w ^ 7 - (2 / 3) * w ^ 6 - (2 / 3) * w ^ 5 + (2 / 3) * w ^ 3 + (2 / 3) * w ^ 2 + (4 / 3) * w + (2 / 3)) * hw

theorem coeff_one_G2 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    coeff 1 (G w 1) = (-4 * w + 2 * w ^ 3) / 3 := by
  rw [G, coeff_one_H, show exponents (1 : Fin 5) = (![-1, 1, 1, 0, -1, -1] : Fin 6 → ℤ) by rfl]
  norm_num [exponents, Fin.sum_univ_succ, Coefficients.zpow_mod_twelve w hw, Int.toNat]
  linear_combination (-(2 / 3) * w ^ 7 - (2 / 3) * w ^ 6 - (2 / 3) * w ^ 5 + (2 / 3) * w ^ 3 + (2 / 3) * w ^ 2 + (4 / 3) * w + (2 / 3)) * hw

theorem coeff_one_G3 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    coeff 1 (G w 2) = (6 - 4 * w + 2 * w ^ 3) / 3 := by
  rw [G, coeff_one_H, show exponents (2 : Fin 5) = (![-1, 1, -2, 0, 2, -1] : Fin 6 → ℤ) by rfl]
  norm_num [exponents, Fin.sum_univ_succ, Coefficients.zpow_mod_twelve w hw, Int.toNat]
  linear_combination (-(2 / 3) * w ^ 7 + (4 / 3) * w ^ 6 - (2 / 3) * w ^ 5 + (2 / 3) * w ^ 3 - (4 / 3) * w ^ 2 + (4 / 3) * w - (4 / 3)) * hw

theorem coeff_one_G4 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    coeff 1 (G w 3) = -(4 / 3) * w ^ 3 + (8 / 3) * w := by
  rw [G, coeff_one_H, show exponents (3 : Fin 5) = (![2, -2, -2, 0, 2, 2] : Fin 6 → ℤ) by rfl]
  norm_num [exponents, Fin.sum_univ_succ, Coefficients.zpow_mod_twelve w hw, Int.toNat]
  linear_combination ((4 / 3) * w ^ 7 + (4 / 3) * w ^ 6 + (4 / 3) * w ^ 5 - (4 / 3) * w ^ 3 - (4 / 3) * w ^ 2 - (8 / 3) * w - (4 / 3)) * hw

theorem coeff_one_G5 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    coeff 1 (G w 4) = -(4 / 3) * w ^ 3 + (8 / 3) * w - 2 := by
  rw [G, coeff_one_H, show exponents (4 : Fin 5) = (![2, -2, 1, 0, -1, 2] : Fin 6 → ℤ) by rfl]
  norm_num [exponents, Fin.sum_univ_succ, Coefficients.zpow_mod_twelve w hw, Int.toNat]
  linear_combination ((4 / 3) * w ^ 7 - (2 / 3) * w ^ 6 + (4 / 3) * w ^ 5 - (4 / 3) * w ^ 3 + (2 / 3) * w ^ 2 - (8 / 3) * w + (2 / 3)) * hw

/-- The corrected coefficient is proved for the actual source G6. -/
theorem coeff_zero_G6_corrected (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    coeff 0 (G6 w) = -1 - 2 * w + w ^ 3 := by
  rw [coeff_zero_G6, Coefficients.c60_corrected w hw]

theorem coeff_one_G6 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    coeff 1 (G6 w) = (4 * w - 2 * w ^ 3) / 3 := by
  rw [G6, map_sub, coeff_C_mul, coeff_one_G4 w hw, coeff_one_G5 w hw,
    Coefficients.pq_ratio w hw]
  linear_combination (-(4 / 3) * w ^ 2 + 4) * hw

end KanadeRussell.Tsuchioka.Scalar
