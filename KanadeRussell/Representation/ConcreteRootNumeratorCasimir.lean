import KanadeRussell.Representation.RootCasimirCancellation
import KanadeRussell.Representation.PrincipalRootEulerProduct
import KanadeRussell.Representation.ConcreteRootCharacterEquation

/-! Actual character–Euler cancellation. The character recurrence and the
Euler logarithmic derivative are proved inputs, not hypotheses of these results. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem tensorPrincipalModule_rootNumerator_casimir
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val) :
    rootCasimirOperator (fun i => M.highestWeightLabels i+1)
      (M.rootCharacter * principalRootEulerDenominator) =
      M.rootCharacter * rootCasimirOperator (fun _ => 1) principalRootEulerDenominator :=
  rootCasimir_product_of_recurrence_and_logarithmicDerivative M.highestWeightLabels
    M.rootCharacter principalRootEulerDenominator
    (tensorPrincipalModule_rootCharacter_equation w hw seed M haction d hD)
    rootEulerOperator_principalRootEulerDenominator

theorem tensorPrincipalModule_rootNumerator_casimir_eq_zero_iff
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val) :
    rootCasimirOperator (fun i => M.highestWeightLabels i+1)
      (M.rootCharacter * principalRootEulerDenominator) = 0 ↔
      rootCasimirOperator (fun _ => 1) (principalRootEulerDenominator (K := K)) = 0 :=
  rootCasimir_product_eq_zero_iff M.highestWeightLabels M.rootCharacter
    principalRootEulerDenominator M.rootCharacter_ne_zero
    (tensorPrincipalModule_rootCharacter_equation w hw seed M haction d hD)
    rootEulerOperator_principalRootEulerDenominator

theorem skewPrincipalModule_rootNumerator_casimir (w : K) (hw : w^4-w^2+1=0) :
    rootCasimirOperator (fun i => (skewPrincipalModule w hw).highestWeightLabels i+1)
      ((skewPrincipalModule w hw).rootCharacter * principalRootEulerDenominator) =
      (skewPrincipalModule w hw).rootCharacter * rootCasimirOperator (fun _ => 1) principalRootEulerDenominator :=
  rootCasimir_product_of_recurrence_and_logarithmicDerivative (skewPrincipalModule w hw).highestWeightLabels
    (skewPrincipalModule w hw).rootCharacter principalRootEulerDenominator
    (skewPrincipalModule_rootCharacter_equation w hw)
    rootEulerOperator_principalRootEulerDenominator

theorem vacuumPrincipalModule_rootNumerator_casimir (w : K) (hw : w^4-w^2+1=0) :
    rootCasimirOperator (fun i => (vacuumPrincipalModule w hw).highestWeightLabels i+1)
      ((vacuumPrincipalModule w hw).rootCharacter * principalRootEulerDenominator) =
      (vacuumPrincipalModule w hw).rootCharacter * rootCasimirOperator (fun _ => 1) principalRootEulerDenominator :=
  rootCasimir_product_of_recurrence_and_logarithmicDerivative (vacuumPrincipalModule w hw).highestWeightLabels
    (vacuumPrincipalModule w hw).rootCharacter principalRootEulerDenominator
    (vacuumPrincipalModule_rootCharacter_equation w hw)
    rootEulerOperator_principalRootEulerDenominator

theorem alternatingPrincipalModule_rootNumerator_casimir (w : K) (hw : w^4-w^2+1=0) :
    rootCasimirOperator (fun i => (alternatingPrincipalModule w hw).highestWeightLabels i+1)
      ((alternatingPrincipalModule w hw).rootCharacter * principalRootEulerDenominator) =
      (alternatingPrincipalModule w hw).rootCharacter * rootCasimirOperator (fun _ => 1) principalRootEulerDenominator :=
  rootCasimir_product_of_recurrence_and_logarithmicDerivative (alternatingPrincipalModule w hw).highestWeightLabels
    (alternatingPrincipalModule w hw).rootCharacter principalRootEulerDenominator
    (alternatingPrincipalModule_rootCharacter_equation w hw)
    rootEulerOperator_principalRootEulerDenominator

end KanadeRussell.Representation
