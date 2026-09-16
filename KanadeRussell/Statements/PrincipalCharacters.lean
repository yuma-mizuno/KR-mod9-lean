import KanadeRussell.Representation.FullCharacter

/-! The three principally specialized character formulas for the actual cyclic
modules, proved by `KanadeRussell.principalCharacterFormulas` in Theorems.lean.
The full characters use their actual finite grade dimensions; the zero quotient
kernel changes no vector space. Heisenberg factorization is proved separately. -/
namespace KanadeRussell
open Tsuchioka Tsuchioka.Fock Representation
variable {K : Type*} [Field K] [CharZero K]

def PrincipalCharacterFormulas (w : K) : Prop :=
  Product.dualAffineDenominator 1 1 1 *
      shiftedQuotientFullCharacter w Sectors.skewSeed 1 ⊥ =
    Product.dualAffineDenominator 2 2 1 ∧
  Product.dualAffineDenominator 1 1 1 *
      shiftedQuotientFullCharacter w 1 0 ⊥ =
    Product.dualAffineDenominator 4 1 1 ∧
  Product.dualAffineDenominator 1 1 1 *
      shiftedQuotientFullCharacter w alternatingSeed 3 ⊥ =
    Product.dualAffineDenominator 1 1 2

end KanadeRussell
