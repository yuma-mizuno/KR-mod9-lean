import KanadeRussell.Representation.OtherCharacterSpecializations
import KanadeRussell.Representation.RootPrincipalEulerSpecialization

/-! Cleared Jacobi-product targets for the three principal numerators.
The theta evaluations remain explicit hypotheses; all product algebra and
transport to the original highest-relative character are proved here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Product

theorem dualAffineDenominator_221_J_cleared :
    E 9*dualAffineDenominator 2 2 1 = E 1*J 2*J 4 := by
  apply mul_right_cancel₀ ((isUnit_E 3 (by decide)).mul (isUnit_J 1 (by decide) (by decide))).ne_zero
  rw [dualAffineDenominator_221]
  linear_combination (E 9*(E 1)^2)*K_one_J-(E 1)*J_product

theorem dualAffineDenominator_411_J_cleared :
    E 9*dualAffineDenominator 4 1 1 = E 1*J 1*J 4 := by
  apply mul_right_cancel₀ ((isUnit_E 3 (by decide)).mul (isUnit_J 2 (by decide) (by decide))).ne_zero
  rw [dualAffineDenominator_411, levelThreeVacuumNumerator_eq]
  linear_combination (E 9*(E 1)^2)*K_two_J-(E 1)*J_product

theorem dualAffineDenominator_112_J_cleared :
    E 9*dualAffineDenominator 1 1 2 = E 1*J 1*J 2 := by
  apply mul_right_cancel₀ ((isUnit_E 3 (by decide)).mul (isUnit_J 4 (by decide) (by decide))).ne_zero
  rw [dualAffineDenominator_112]
  linear_combination (E 9*(E 1)^2)*K_three_J-(E 1)*J_product

theorem numerator_eq_221_of_J_cleared (N : PowerSeries ℤ)
    (h : E 9*N = E 1*J 2*J 4) : N = dualAffineDenominator 2 2 1 := by
  exact mul_left_cancel₀ (isUnit_E 9 (by decide)).ne_zero
    (h.trans dualAffineDenominator_221_J_cleared.symm)

theorem numerator_eq_411_of_J_cleared (N : PowerSeries ℤ)
    (h : E 9*N = E 1*J 1*J 4) : N = dualAffineDenominator 4 1 1 := by
  exact mul_left_cancel₀ (isUnit_E 9 (by decide)).ne_zero
    (h.trans dualAffineDenominator_411_J_cleared.symm)

theorem numerator_eq_112_of_J_cleared (N : PowerSeries ℤ)
    (h : E 9*N = E 1*J 1*J 2) : N = dualAffineDenominator 1 1 2 := by
  exact mul_left_cancel₀ (isUnit_E 9 (by decide)).ne_zero
    (h.trans dualAffineDenominator_112_J_cleared.symm)

end KanadeRussell.Product

namespace KanadeRussell.Representation.PrincipalHighestWeightModule
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
open Product

private theorem cleared_rootNumerator_descends (M : PrincipalHighestWeightModule K V)
    (F : PowerSeries ℤ)
    (h : PowerSeries.map (Int.castRingHom K) (E 9)*
      rootPrincipalSpecialization (M.rootCharacter*principalRootEulerDenominator) =
        PowerSeries.map (Int.castRingHom K) F) :
    E 9*(M.character*dualAffineDenominator 1 1 1) = F := by
  rw [M.rootPrincipalSpecialization_rootNumerator, ← map_mul] at h
  exact PowerSeries.map_injective (Int.castRingHom K) Int.cast_injective h

/-- The (2,2,1) numerator evaluation gives the original normalized full-character target. -/
theorem character_eq_221_of_J_cleared (M : PrincipalHighestWeightModule K V)
    (h : PowerSeries.map (Int.castRingHom K) (E 9)*
      rootPrincipalSpecialization (M.rootCharacter*principalRootEulerDenominator) =
        PowerSeries.map (Int.castRingHom K) (E 1*J 2*J 4)) :
    dualAffineDenominator 1 1 1*M.character = dualAffineDenominator 2 2 1 := by
  rw [mul_comm]
  exact numerator_eq_221_of_J_cleared _ (M.cleared_rootNumerator_descends _ h)

/-- The (4,1,1) numerator evaluation gives the original normalized full-character target. -/
theorem character_eq_411_of_J_cleared (M : PrincipalHighestWeightModule K V)
    (h : PowerSeries.map (Int.castRingHom K) (E 9)*
      rootPrincipalSpecialization (M.rootCharacter*principalRootEulerDenominator) =
        PowerSeries.map (Int.castRingHom K) (E 1*J 1*J 4)) :
    dualAffineDenominator 1 1 1*M.character = dualAffineDenominator 4 1 1 := by
  rw [mul_comm]
  exact numerator_eq_411_of_J_cleared _ (M.cleared_rootNumerator_descends _ h)

/-- The (1,1,2) numerator evaluation gives the original normalized full-character target. -/
theorem character_eq_112_of_J_cleared (M : PrincipalHighestWeightModule K V)
    (h : PowerSeries.map (Int.castRingHom K) (E 9)*
      rootPrincipalSpecialization (M.rootCharacter*principalRootEulerDenominator) =
        PowerSeries.map (Int.castRingHom K) (E 1*J 1*J 2)) :
    dualAffineDenominator 1 1 1*M.character = dualAffineDenominator 1 1 2 := by
  rw [mul_comm]
  exact numerator_eq_112_of_J_cleared _ (M.cleared_rootNumerator_descends _ h)

end KanadeRussell.Representation.PrincipalHighestWeightModule
