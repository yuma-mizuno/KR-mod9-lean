import KanadeRussell.Representation.PrincipalRootDenominatorFactorization
import KanadeRussell.Representation.PrincipalRootComplementSymmetry

/-! Shifted Weyl antisymmetry of the actual multivariate Euler denominator. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K]

theorem rootCoefficient_principalRootEulerDenominator_reflection (i : Fin 3)
    (beta : RootCoefficients) :
    rootCoefficient (principalRootEulerDenominator (K := K))
      (simpleReflection (fun _ => 1) i beta) =
      -rootCoefficient (principalRootEulerDenominator (K := K)) beta := by
  rw [rootCoefficient_principalRootEulerDenominator i,
    rootCoefficient_principalRootEulerDenominator i,
    simpleReflection_rho_sub_simple]
  have h := rootCoefficient_principalRootComplementEuler_reflection (K := K) i
    (simpleReflection (fun _ => 1) i beta)
  rw [simpleReflection_zero_rho] at h
  rw [← h, rootCoefficient_principalRootComplementEuler_reflection]
  ring

end KanadeRussell.Representation
