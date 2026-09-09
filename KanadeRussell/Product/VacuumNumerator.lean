import KanadeRussell.Product.Defs

/-! The explicit product calculation in the level-three vacuum character route.
The six heights are those used for the proposed dual G2 affine denominator
specialized at (4,1,1), whose imaginary-root period is 9.
This file proves the product calculation only: it asserts neither an affine
root classification nor an equality with a representation character. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Product

noncomputable def levelThreeVacuumNumerator : PowerSeries ℤ :=
  (E 9)^2 * (([1,1,2,3,4,5] : List ℕ).map (fun h => P9 h * P9 (9-h))).prod

theorem levelThreeVacuumNumerator_cleared :
    levelThreeVacuumNumerator * (P9 2 * P9 3 * P9 6 * P9 7) = (E 1)^2 := by
  rw [E_one_split]
  norm_num [levelThreeVacuumNumerator, List.prod_cons, List.prod_nil]
  ring

theorem levelThreeVacuumNumerator_eq :
    levelThreeVacuumNumerator = (E 1)^2 * K₂ := by
  have hu : IsUnit (P9 2 * P9 3 * P9 6 * P9 7) :=
    (((isUnit_P9 2 (by decide)).mul (isUnit_P9 3 (by decide))).mul
      (isUnit_P9 6 (by decide))).mul (isUnit_P9 7 (by decide))
  change levelThreeVacuumNumerator = (E 1)^2 * bInv (P9 2 * P9 3 * P9 6 * P9 7)
  rw [← levelThreeVacuumNumerator_cleared, mul_assoc, hu.mul_bInv_cancel, mul_one]

theorem levelThreeVacuumNumerator_div_euler :
    bInv ((E 1)^2) * levelThreeVacuumNumerator = K₂ := by
  rw [levelThreeVacuumNumerator_eq, ← mul_assoc,
    ((isUnit_E 1 (by decide)).pow 2).bInv_mul_cancel, one_mul]

/-- The exact remaining character identity, with all product algebra discharged. -/
theorem vacuumCharacter_eq_K₂_iff (S : PowerSeries ℤ) :
    S = K₂ ↔ (E 1)^2 * S = levelThreeVacuumNumerator := by
  rw [levelThreeVacuumNumerator_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    exact mul_left_cancel₀ ((isUnit_E 1 (by decide)).pow 2).ne_zero h

end KanadeRussell.Product
