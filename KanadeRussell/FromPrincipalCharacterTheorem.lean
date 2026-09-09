import KanadeRussell.FromPrincipalCharacters
import KanadeRussell.Pending.PrincipalCharacterTheorem
import KanadeRussell.Representation.ConcreteHighestWeight

/-! The universal principal character theorem applies to the three constructed
graded integrable highest-weight modules with every application hypothesis proved. -/
namespace KanadeRussell
open Representation Tsuchioka Tsuchioka.Fock

theorem principalCharacterFormulas_of_principalCharacterTheorem
    (h : PrincipalCharacterTheorem.{0}) : PrincipalCharacterFormulas complexPhase := by
  refine ⟨?_, ?_, ?_⟩
  · have hs := h _ (skewPrincipalModule complexPhase complexPhase_relation)
    change Product.dualAffineDenominator 1 1 1 *
      (skewPrincipalModule complexPhase complexPhase_relation).character =
        Product.dualAffineDenominator 2 2 1 at hs
    rwa [skewPrincipalModule_character] at hs
  · have hs := h _ (vacuumPrincipalModule complexPhase complexPhase_relation)
    change Product.dualAffineDenominator 1 1 1 *
      (vacuumPrincipalModule complexPhase complexPhase_relation).character =
        Product.dualAffineDenominator 4 1 1 at hs
    rwa [vacuumPrincipalModule_character] at hs
  · have hs := h _ (alternatingPrincipalModule complexPhase complexPhase_relation)
    change Product.dualAffineDenominator 1 1 1 *
      (alternatingPrincipalModule complexPhase complexPhase_relation).character =
        Product.dualAffineDenominator 1 1 2 at hs
    rwa [alternatingPrincipalModule_character] at hs

theorem lowerBounds_of_principalCharacterTheorem (h : PrincipalCharacterTheorem.{0}) : LowerBounds :=
  lowerBounds_of_principalCharacterFormulas complexPhase complexPhase_relation
    (principalCharacterFormulas_of_principalCharacterTheorem h)

theorem kanade_russell_of_principal_character_theorem (h : PrincipalCharacterTheorem.{0}) :
    A = K₁ ∧ B = K₂ ∧ C = K₃ :=
  kanade_russell_of_lowerBounds (lowerBounds_of_principalCharacterTheorem h)

end KanadeRussell
