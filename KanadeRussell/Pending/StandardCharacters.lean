import KanadeRussell.Representation.FullCharacter

/-! Temporary standard-module character application inputs.

The quotient kernel must preserve every homogeneous component and leave the
chosen seed nonzero. Both characters are defined from the actual quotient
grade dimensions. The two equations are the specialized standard character
formula and the principal Heisenberg factorization. Existence of such a kernel
includes the standard-module application, which is not proved here.
These are propositions used as explicit theorem hypotheses, not axioms. -/
namespace KanadeRussell
open Tsuchioka Tsuchioka.Fock Representation
variable {K : Type*} [Field K] [CharZero K]

def StandardModuleCharacterApplication (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (s₀ s₁ s₂ : ℕ) : Prop :=
  ∃ (S : Submodule K (Space K)) (hS : ChevalleyStable w S),
    (∀ (m : ℤ) f, f ∈ S →
      MvPolynomial.weightedHomogeneousComponent variableWeight m f ∈ S) ∧
    seed ∉ S ∧
    Product.dualAffineDenominator 1 1 1 * shiftedQuotientFullCharacter w seed d S =
      Product.dualAffineDenominator s₀ s₁ s₂ ∧
    Product.principalHeisenbergEuler * shiftedQuotientFullCharacter w seed d S =
      shiftedQuotientVacuumCharacter w hw seed d S hS

/-- Three normalized character applications, ordered as the three KR identities.
The ambient degrees are 1, 0, 3; the numerator parameters are lambda + rho. -/
def StandardCharacters (w : K) (hw : w^4-w^2+1=0) : Prop :=
  StandardModuleCharacterApplication w hw Sectors.skewSeed 1 2 2 1 ∧
  StandardModuleCharacterApplication w hw 1 0 4 1 1 ∧
  StandardModuleCharacterApplication w hw alternatingSeed 3 1 1 2

end KanadeRussell
