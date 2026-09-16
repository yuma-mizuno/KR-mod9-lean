import KanadeRussell.Representation.PrincipalHighestWeight
import KanadeRussell.Representation.CharacterSpecialization
import Mathlib.Analysis.Complex.Basic

/-! Universal principal character-formula statement over complex representations
and arbitrary dominant weights. It is retained as an explicit hypothesis for
FromPrincipalCharacterTheorem.lean, rather than proved in this library.
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
