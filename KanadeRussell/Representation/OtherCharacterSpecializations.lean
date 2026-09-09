import KanadeRussell.Representation.CharacterSpecialization

/-! The other two level-three highest weights in Tsuchioka's Theorem 1.3.
For Lambda_0 + Lambda_1 and Lambda_2, adding rho to the Dynkin labels
specializes the dual affine denominator at (2,2,1) and (1,1,2), respectively.
The character inputs below use grading relative to the highest-weight vector;
the ambient degrees of the chosen tensor seeds are not part of this normalization.
The standard character formula remains an explicit hypothesis. -/
set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Product

/-- Positive-root heights for the numerator attached to Lambda_0 + Lambda_1. -/
theorem dualRootHeights_two_one :
    dualRootHeights 2 1 = [2,1,3,4,5,7] := rfl

/-- Positive-root heights for the numerator attached to Lambda_2. -/
theorem dualRootHeights_one_two :
    dualRootHeights 1 2 = [1,2,3,5,7,8] := rfl

theorem dualAffineDenominator_221_cleared :
    dualAffineDenominator 2 2 1 * (P9 1 * P9 3 * P9 6 * P9 8) = (E 1)^2 := by
  rw [E_one_split]
  norm_num [dualAffineDenominator, dualImaginaryPeriod, dualRootHeights_two_one,
    progressionProduct, P9, List.prod_cons, List.prod_nil]
  ring

theorem dualAffineDenominator_112_cleared :
    dualAffineDenominator 1 1 2 * (P9 3 * P9 4 * P9 5 * P9 6) = (E 1)^2 := by
  rw [E_one_split]
  norm_num [dualAffineDenominator, dualImaginaryPeriod, dualRootHeights_one_two,
    progressionProduct, P9, List.prod_cons, List.prod_nil]
  ring

theorem dualAffineDenominator_221 :
    dualAffineDenominator 2 2 1 = (E 1)^2 * K₁ := by
  rw [← dualAffineDenominator_221_cleared, mul_assoc,
    mul_comm (P9 1 * P9 3 * P9 6 * P9 8) K₁, K₁_mul, mul_one]

theorem dualAffineDenominator_112 :
    dualAffineDenominator 1 1 2 = (E 1)^2 * K₃ := by
  rw [← dualAffineDenominator_112_cleared, mul_assoc,
    mul_comm (P9 3 * P9 4 * P9 5 * P9 6) K₃, K₃_mul, mul_one]

theorem vacuumCharacter_eq_K₁_iff (S : PowerSeries ℤ) :
    S = K₁ ↔ (E 1)^2 * S = dualAffineDenominator 2 2 1 := by
  rw [dualAffineDenominator_221]
  constructor
  · intro h
    rw [h]
  · intro h
    exact mul_left_cancel₀ ((isUnit_E 1 (by decide)).pow 2).ne_zero h

theorem vacuumCharacter_eq_K₃_iff (S : PowerSeries ℤ) :
    S = K₃ ↔ (E 1)^2 * S = dualAffineDenominator 1 1 2 := by
  rw [dualAffineDenominator_112]
  constructor
  · intro h
    rw [h]
  · intro h
    exact mul_left_cancel₀ ((isUnit_E 1 (by decide)).pow 2).ne_zero h

/-- Normalized vacuum character for highest weight Lambda_0 + Lambda_1,
conditional only on the displayed standard character and Heisenberg equations. -/
theorem vacuum_eq_K₁_of_standard_character_formulas (C S : PowerSeries ℤ)
    (hchar : dualAffineDenominator 1 1 1 * C = dualAffineDenominator 2 2 1)
    (hHeisenberg : principalHeisenbergEuler * C = S) : S = K₁ := by
  apply (vacuumCharacter_eq_K₁_iff S).mpr
  rw [dualAffineDenominator_111, mul_assoc, hHeisenberg] at hchar
  exact hchar

/-- Normalized vacuum character for highest weight Lambda_2,
conditional only on the displayed standard character and Heisenberg equations. -/
theorem vacuum_eq_K₃_of_standard_character_formulas (C S : PowerSeries ℤ)
    (hchar : dualAffineDenominator 1 1 1 * C = dualAffineDenominator 1 1 2)
    (hHeisenberg : principalHeisenbergEuler * C = S) : S = K₃ := by
  apply (vacuumCharacter_eq_K₃_iff S).mpr
  rw [dualAffineDenominator_111, mul_assoc, hHeisenberg] at hchar
  exact hchar

end KanadeRussell.Product
