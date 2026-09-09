import KanadeRussell.Representation.PrincipalHighestWeight
import KanadeRussell.Representation.CharacterSpecialization
import Mathlib.Analysis.Complex.Basic

/-! The established principal character theorem, retained as an explicit
universal input over complex representations and arbitrary dominant weights.
It contains no concrete seed, Coxeter phase, or Kanade–Russell series. -/
namespace KanadeRussell
open Representation
universe u

def PrincipalCharacterTheorem : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
    (M : PrincipalHighestWeightModule ℂ V),
    Product.dualAffineDenominator 1 1 1 * M.character =
      Product.dualAffineDenominator (M.highestWeight 0 + 1)
        (M.highestWeight 1 + 1) (M.highestWeight 2 + 1)

end KanadeRussell
