import KanadeRussell.Representation.ConcreteRootNumeratorMasks
import KanadeRussell.Representation.PrincipalNumeratorProductTargets
import KanadeRussell.FromPrincipalCharacters

/-! Three explicit integral mask numerators and their exact connection to the
original Kanade--Russell identities. The final theorem assumes only their
three displayed scalar theta/product evaluations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KanadeRussell.Representation.LevelNineNumeratorMasks

/-- Principal numerator coefficients are finite sums of the proved signed root masks. -/
def principalNumerator (k : Fin 3) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ∑ b : PrincipalDegreeOccupation n, candidate k b.root

@[simp] theorem coeff_principalNumerator (k : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (principalNumerator k) =
      ∑ b : PrincipalDegreeOccupation n, candidate k b.root := by
  simp only [principalNumerator, PowerSeries.coeff_mk]

end KanadeRussell.Representation.LevelNineNumeratorMasks

namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock LevelNineNumeratorMasks
variable {K : Type*} [Field K] [CharZero K]

theorem skewPrincipalModule_principalNumerator (w : K) (hw : w^4-w^2+1=0) :
    rootPrincipalSpecialization ((skewPrincipalModule w hw).rootCharacter*principalRootEulerDenominator) =
      PowerSeries.map (Int.castRingHom K) (principalNumerator 0) := by
  ext n
  rw [skewPrincipalModule_principalNumerator_coeff, PowerSeries.coeff_map, coeff_principalNumerator]
  simp

theorem vacuumPrincipalModule_principalNumerator (w : K) (hw : w^4-w^2+1=0) :
    rootPrincipalSpecialization ((vacuumPrincipalModule w hw).rootCharacter*principalRootEulerDenominator) =
      PowerSeries.map (Int.castRingHom K) (principalNumerator 1) := by
  ext n
  rw [vacuumPrincipalModule_principalNumerator_coeff, PowerSeries.coeff_map, coeff_principalNumerator]
  simp

theorem alternatingPrincipalModule_principalNumerator (w : K) (hw : w^4-w^2+1=0) :
    rootPrincipalSpecialization ((alternatingPrincipalModule w hw).rootCharacter*principalRootEulerDenominator) =
      PowerSeries.map (Int.castRingHom K) (principalNumerator 2) := by
  ext n
  rw [alternatingPrincipalModule_principalNumerator_coeff, PowerSeries.coeff_map, coeff_principalNumerator]
  simp

/-- The integral skew numerator is the cleared actual highest-relative character. -/
theorem skewPrincipalModule_principalNumerator_integral (w : K) (hw : w^4-w^2+1=0) :
    (skewPrincipalModule w hw).character*Product.dualAffineDenominator 1 1 1 = principalNumerator 0 := by
  apply PowerSeries.map_injective (Int.castRingHom K) Int.cast_injective
  rw [← (skewPrincipalModule w hw).rootPrincipalSpecialization_rootNumerator]
  exact skewPrincipalModule_principalNumerator w hw

/-- The integral vacuum numerator is the cleared actual highest-relative character. -/
theorem vacuumPrincipalModule_principalNumerator_integral (w : K) (hw : w^4-w^2+1=0) :
    (vacuumPrincipalModule w hw).character*Product.dualAffineDenominator 1 1 1 = principalNumerator 1 := by
  apply PowerSeries.map_injective (Int.castRingHom K) Int.cast_injective
  rw [← (vacuumPrincipalModule w hw).rootPrincipalSpecialization_rootNumerator]
  exact vacuumPrincipalModule_principalNumerator w hw

/-- The integral alternating numerator is the cleared actual highest-relative character. -/
theorem alternatingPrincipalModule_principalNumerator_integral (w : K) (hw : w^4-w^2+1=0) :
    (alternatingPrincipalModule w hw).character*Product.dualAffineDenominator 1 1 1 = principalNumerator 2 := by
  apply PowerSeries.map_injective (Int.castRingHom K) Int.cast_injective
  rw [← (alternatingPrincipalModule w hw).rootPrincipalSpecialization_rootNumerator]
  exact alternatingPrincipalModule_principalNumerator w hw

end KanadeRussell.Representation

namespace KanadeRussell
open Representation Representation.LevelNineNumeratorMasks Product Tsuchioka
variable {K : Type*} [Field K] [CharZero K]

/-- The three scalar evaluations give the established character applications with no representation premises. -/
theorem principalCharacterFormulas_of_principal_mask_products (w : K) (hw : w^4-w^2+1=0)
    (h0 : E 9*principalNumerator 0 = E 1*J 2*J 4)
    (h1 : E 9*principalNumerator 1 = E 1*J 1*J 4)
    (h2 : E 9*principalNumerator 2 = E 1*J 1*J 2) : PrincipalCharacterFormulas w := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (skewPrincipalModule_principalNumerator_integral w hw).trans
      (numerator_eq_221_of_J_cleared _ h0)
    simpa only [skewPrincipalModule_character, mul_comm] using h
  · have h := (vacuumPrincipalModule_principalNumerator_integral w hw).trans
      (numerator_eq_411_of_J_cleared _ h1)
    simpa only [vacuumPrincipalModule_character, mul_comm] using h
  · have h := (alternatingPrincipalModule_principalNumerator_integral w hw).trans
      (numerator_eq_112_of_J_cleared _ h2)
    simpa only [alternatingPrincipalModule_character, mul_comm] using h

/-- The original three Kanade--Russell identities follow from three explicit integral theta/product evaluations. -/
theorem kanade_russell_of_principal_mask_products
    (h0 : E 9*principalNumerator 0 = E 1*J 2*J 4)
    (h1 : E 9*principalNumerator 1 = E 1*J 1*J 4)
    (h2 : E 9*principalNumerator 2 = E 1*J 1*J 2) : A = K₁ ∧ B = K₂ ∧ C = K₃ :=
  kanade_russell_of_principal_characters
    (principalCharacterFormulas_of_principal_mask_products complexPhase complexPhase_relation h0 h1 h2)

end KanadeRussell
