import KanadeRussell.Representation.RootDenominatorPrincipalReduction
import KanadeRussell.Representation.ConcreteRootNumeratorUniqueness

/-! The actual tensor numerator equation reduced to the principal residual,
with the original action and normalized derivation retained. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
open AffineWeightLattice Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

theorem tensorPrincipalModule_rootNumerator_eq_zero_iff_principalResidual
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val) :
    rootCasimirOperator (fun i => M.highestWeightLabels i+1)
      (M.rootCharacter*principalRootEulerDenominator) = 0 ↔
      rootPrincipalSpecialization (principalRootLambertResidual (K := K)) = 0 :=
  (tensorPrincipalModule_rootNumerator_casimir_eq_zero_iff w hw seed M haction d hD).trans
    rootCasimir_denominator_eq_zero_iff_principalResidual

theorem tensorPrincipalModule_rootNumerator_unique_of_principalResidual
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (hresidual : rootPrincipalSpecialization (principalRootLambertResidual (K := K)) = 0)
    (b : RootCoefficients → K)
    (hsupport : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → b beta = 0)
    (hzero : b 0 = 1)
    (hanti : ∀ i beta, b (simpleReflection (fun j => M.highestWeightLabels j+1) i beta) = -b beta)
    (hcas : ∀ beta, (casimir (fun i => M.highestWeightLabels i+1) beta : K)*b beta = 0) :
    rootCoefficient (M.rootCharacter*principalRootEulerDenominator) = b :=
  tensorPrincipalModule_rootNumerator_unique w hw seed M haction d hD
    (rootCasimir_denominator_eq_zero_iff_principalResidual.mpr hresidual)
    b hsupport hzero hanti hcas

end KanadeRussell.Representation
