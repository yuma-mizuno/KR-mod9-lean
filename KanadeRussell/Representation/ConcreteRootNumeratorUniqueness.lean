import KanadeRussell.Representation.RootAlternantUniqueness
import KanadeRussell.Representation.ConcreteRootNumeratorAntisymmetry
import KanadeRussell.Representation.ConcreteRootNumeratorCasimir

/-! Conditional identification of actual numerator coefficients. The remaining
Casimir equation is an explicit hypothesis, not a denominator evaluation. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
open AffineWeightLattice Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem rootCoefficient_rootCasimirOperator (lambda : RootCoefficients)
    (f : MvPowerSeries (Fin 3) K) (beta : RootCoefficients) :
    rootCoefficient (rootCasimirOperator lambda f) beta =
      (casimir lambda beta : K) * rootCoefficient f beta := by
  by_cases hb : ∀ i, 0 ≤ beta i
  · rw [rootCoefficient_of_nonneg _ _ hb, rootCoefficient_of_nonneg _ _ hb,
      coeff_rootCasimirOperator, rootCoefficientsOfExponent_ofRoot beta hb]
  · rw [rootCoefficient_of_not_nonneg _ _ hb, rootCoefficient_of_not_nonneg _ _ hb, mul_zero]

namespace PrincipalHighestWeightModule
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Actual numerator uniqueness once its explicit Casimir-zero equation is known. -/
theorem rootNumerator_unique (M : PrincipalHighestWeightModule K V)
    (hcasimir : rootCasimirOperator (fun i => M.highestWeightLabels i+1)
      (M.rootCharacter * principalRootEulerDenominator) = 0)
    (b : RootCoefficients → K)
    (hsupport : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → b beta = 0)
    (hzero : b 0 = 1)
    (hanti : ∀ i beta, b (simpleReflection (fun j => M.highestWeightLabels j+1) i beta) = -b beta)
    (hcas : ∀ beta, (casimir (fun i => M.highestWeightLabels i+1) beta : K) * b beta = 0) :
    rootCoefficient (M.rootCharacter * principalRootEulerDenominator) = b := by
  apply rootAlternant_unique M.highestWeightLabels (fun i => Int.natCast_nonneg (M.highestWeight i))
    _ b M.rootNumerator_support hsupport
  · rw [M.rootNumerator_zero, hzero]
  · exact M.rootNumerator_antisymmetric
  · exact hanti
  · intro beta
    rw [← rootCoefficient_rootCasimirOperator, hcasimir, rootCoefficient_zero]
  · exact hcas

end PrincipalHighestWeightModule

/-- For an actual tensor module, only the root Euler denominator Casimir equation
remains in addition to the stated candidate conditions. -/
theorem tensorPrincipalModule_rootNumerator_unique
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (hdenominator : rootCasimirOperator (fun _ => 1) (principalRootEulerDenominator (K := K)) = 0)
    (b : RootCoefficients → K)
    (hsupport : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → b beta = 0)
    (hzero : b 0 = 1)
    (hanti : ∀ i beta, b (simpleReflection (fun j => M.highestWeightLabels j+1) i beta) = -b beta)
    (hcas : ∀ beta, (casimir (fun i => M.highestWeightLabels i+1) beta : K) * b beta = 0) :
    rootCoefficient (M.rootCharacter * principalRootEulerDenominator) = b := by
  apply M.rootNumerator_unique _ b hsupport hzero hanti hcas
  rw [tensorPrincipalModule_rootNumerator_casimir w hw seed M haction d hD,
    hdenominator, mul_zero]

end KanadeRussell.Representation
