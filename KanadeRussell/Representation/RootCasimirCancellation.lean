import KanadeRussell.Representation.PrincipalRootSeriesData
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! Cancellation of the recurrence and Euler logarithmic derivative in the
rho-shifted Casimir product rule. The two input equations are explicit here;
their concrete applications are supplied separately. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K]

theorem rootCasimir_product_of_recurrence_and_logarithmicDerivative
    (lambda : RootCoefficients) (C D : MvPowerSeries (Fin 3) K)
    (hC : rootCasimirOperator (fun i => lambda i+1) C =
      -∑ i : Fin 3, (symmetrizer i : K) •
        ((principalRootLambert i)*(rootWeightLabelOperator lambda i C)))
    (hD : ∀ i, rootEulerOperator i D = -D*principalRootLambert i) :
    rootCasimirOperator (fun i => lambda i+1) (C*D) =
      C*(rootCasimirOperator (fun _ => 1) D) := by
  rw [rootCasimirOperator_rho_mul, hC]
  simp only [hD, Fin.sum_univ_three, Algebra.smul_def]
  ring

theorem rootCasimir_product_eq_zero_iff
    (lambda : RootCoefficients) (C D : MvPowerSeries (Fin 3) K) (hC0 : C ≠ 0)
    (hC : rootCasimirOperator (fun i => lambda i+1) C =
      -∑ i : Fin 3, (symmetrizer i : K) •
        ((principalRootLambert i)*(rootWeightLabelOperator lambda i C)))
    (hD : ∀ i, rootEulerOperator i D = -D*principalRootLambert i) :
    rootCasimirOperator (fun i => lambda i+1) (C*D) = 0 ↔
      rootCasimirOperator (fun _ => 1) D = 0 := by
  rw [rootCasimir_product_of_recurrence_and_logarithmicDerivative lambda C D hC hD,
    mul_eq_zero, or_iff_right hC0]

namespace PrincipalHighestWeightModule
variable {V : Type*} [CharZero K] [AddCommGroup V] [Module K V]

theorem rootCharacter_ne_zero (M : PrincipalHighestWeightModule K V) : M.rootCharacter ≠ 0 := by
  intro h
  have he := congrArg MvPowerSeries.constantCoeff h
  rw [M.constantCoeff_rootCharacter, map_zero] at he
  exact one_ne_zero he

end PrincipalHighestWeightModule
end KanadeRussell.Representation
