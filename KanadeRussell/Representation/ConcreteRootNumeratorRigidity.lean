import KanadeRussell.Representation.RootLambertIdentity
import KanadeRussell.Representation.ConcreteRootNumeratorUniqueness

/-! The actual tensor numerators satisfy the Casimir-zero equation. Identifying
them with a candidate now requires only that candidate's stated alternant
conditions; the root denominator equation is no longer an input. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
open AffineWeightLattice Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

theorem tensorPrincipalModule_rootNumerator_casimir_zero
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val+d • p.val) :
    rootCasimirOperator (fun i => M.highestWeightLabels i+1)
      (M.rootCharacter*principalRootEulerDenominator) = 0 := by
  rw [tensorPrincipalModule_rootNumerator_casimir w hw seed M haction d hD,
    rootCasimir_principalRootEulerDenominator_zero, mul_zero]

theorem tensorPrincipalModule_rootNumerator_eq_of_conditions
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val+d • p.val)
    (b : RootCoefficients → K)
    (hsupport : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → b beta = 0)
    (hzero : b 0 = 1)
    (hanti : ∀ i beta, b (simpleReflection (fun j => M.highestWeightLabels j+1) i beta) = -b beta)
    (hcas : ∀ beta, (casimir (fun i => M.highestWeightLabels i+1) beta : K)*b beta = 0) :
    rootCoefficient (M.rootCharacter*principalRootEulerDenominator) = b :=
  tensorPrincipalModule_rootNumerator_unique w hw seed M haction d hD
    rootCasimir_principalRootEulerDenominator_zero b hsupport hzero hanti hcas

theorem skewPrincipalModule_rootNumerator_casimir_zero (w : K) (hw : w^4-w^2+1=0) :
    rootCasimirOperator (fun i => (skewPrincipalModule w hw).highestWeightLabels i+1)
      ((skewPrincipalModule w hw).rootCharacter*principalRootEulerDenominator) = 0 :=
  tensorPrincipalModule_rootNumerator_casimir_zero w hw KanadeRussell.Sectors.skewSeed
    (skewPrincipalModule w hw) rfl 1
    (by simpa only [one_smul] using skewPrincipalModule_principalDerivation_val w hw)

theorem vacuumPrincipalModule_rootNumerator_casimir_zero (w : K) (hw : w^4-w^2+1=0) :
    rootCasimirOperator (fun i => (vacuumPrincipalModule w hw).highestWeightLabels i+1)
      ((vacuumPrincipalModule w hw).rootCharacter*principalRootEulerDenominator) = 0 :=
  tensorPrincipalModule_rootNumerator_casimir_zero w hw 1 (vacuumPrincipalModule w hw) rfl 0
    (by simpa only [zero_smul, add_zero] using vacuumPrincipalModule_principalDerivation_val w hw)

theorem alternatingPrincipalModule_rootNumerator_casimir_zero (w : K) (hw : w^4-w^2+1=0) :
    rootCasimirOperator (fun i => (alternatingPrincipalModule w hw).highestWeightLabels i+1)
      ((alternatingPrincipalModule w hw).rootCharacter*principalRootEulerDenominator) = 0 :=
  tensorPrincipalModule_rootNumerator_casimir_zero w hw alternatingSeed
    (alternatingPrincipalModule w hw) rfl 3 (alternatingPrincipalModule_principalDerivation_val w hw)
end KanadeRussell.Representation
