import KanadeRussell.Representation.RootMultiplicityUniqueness
import KanadeRussell.Representation.RootMultiplicityFunction
import KanadeRussell.Representation.ConcreteRootMultiplicityRecurrence

/-! Conditional identification of a candidate root-multiplicity function.
The candidate's support, normalization, Weyl symmetry and explicit dominant
recurrence are premises; no candidate character evaluation is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

/-- The actual tensor module is the unique solution of the explicit recurrence,
among normalized, positive-cone-supported, ordinarily Weyl-symmetric functions. -/
theorem tensorPrincipalModule_rootMultiplicity_eq_of_recurrence
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (m : RootCoefficients → K)
    (hsupport : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → m beta = 0)
    (hzero : m 0 = 1)
    (hweyl : ∀ i beta, m (simpleReflection M.highestWeightLabels i beta) = m beta)
    (hrec : ∀ beta, beta ≠ 0 → (∀ i, 0 ≤ beta i) →
      (∀ i, 0 ≤ weightLabels M.highestWeightLabels beta i) →
      (casimir (fun i => M.highestWeightLabels i+1) beta : K) * m beta =
        ∑ delta ∈ (rootMultiplicityKernel (K := K) M.highestWeightLabels beta).support,
          rootMultiplicityKernel M.highestWeightLabels beta delta * m delta) :
    m = M.rootMultiplicity := by
  apply rootMultiplicity_unique M.highestWeightLabels
    (fun i => Int.natCast_nonneg (M.highestWeight i))
    (rootMultiplicityKernel M.highestWeightLabels)
    (rootMultiplicityKernel_support_degree_lt M.highestWeightLabels)
    m M.rootMultiplicity hsupport M.rootMultiplicity_eq_zero_of_not_nonneg
    (hzero.trans M.rootMultiplicity_zero.symm) hweyl M.rootMultiplicity_simpleReflection hrec
  intro beta _ _ _
  exact tensorPrincipalModule_rootMultiplicity_recurrence w hw seed M haction d hD beta

end KanadeRussell.Representation
