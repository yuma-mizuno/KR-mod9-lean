import KanadeRussell.Tsuchioka.FormalFourier

/-! Polynomial representatives of the twelve source phases. -/

namespace KanadeRussell.Tsuchioka.Scalar

/-- w^(-p), represented with degree at most three under the cyclotomic relation. -/
def phasePolynomial {A : Type*} [CommRing A] (w : A) (p : Fin 12) : A :=
  match p.val with
  | 0 => 1
  | 1 => -w ^ 3 + w
  | 2 => -w ^ 2 + 1
  | 3 => -w ^ 3
  | 4 => -w ^ 2
  | 5 => -w
  | 6 => -1
  | 7 => w ^ 3 - w
  | 8 => w ^ 2 - 1
  | 9 => w ^ 3
  | 10 => w ^ 2
  | _ => w

theorem map_phasePolynomial {A B : Type*} [CommRing A] [CommRing B]
    (h : A →+* B) (w : A) (p : Fin 12) :
    h (phasePolynomial w p) = phasePolynomial (h w) p := by
  fin_cases p <;> simp [phasePolynomial, map_sub, map_pow, map_neg]

variable {K : Type*} [Field K] [CharZero K]

theorem negative_phase (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (p : Fin 12) :
    w ^ (-(p.val : ℤ)) = phasePolynomial w p := by
  fin_cases p
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]
    linear_combination (w ^ 7 + w ^ 5 - w) * hw
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]
    linear_combination (w ^ 6 + w ^ 4 - 1) * hw
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]
    linear_combination (w ^ 5 + w ^ 3) * hw
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]
    linear_combination (w ^ 4 + w ^ 2) * hw
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]
    linear_combination (w ^ 3 + w) * hw
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]
    linear_combination (w ^ 2 + 1) * hw
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]
    linear_combination (w) * hw
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]
    linear_combination (1) * hw
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]
  · norm_num [phasePolynomial, Coefficients.zpow_mod_twelve w hw, Int.toNat]

theorem phasePolynomial_ne_zero (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (p : Fin 12) :
    phasePolynomial w p ≠ 0 := by
  rw [← negative_phase w hw p]
  exact zpow_ne_zero _ (Coefficients.root_ne_zero w hw)

theorem phasePolynomial_inverse (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (p : Fin 12) :
    (phasePolynomial w p)⁻¹ = w ^ p.val := by
  rw [← negative_phase w hw p, zpow_neg, inv_inv, zpow_natCast]

end KanadeRussell.Tsuchioka.Scalar
