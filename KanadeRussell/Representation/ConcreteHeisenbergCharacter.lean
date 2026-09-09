import KanadeRussell.Representation.HeisenbergCharacter
import KanadeRussell.Representation.ConcreteCharacters

/-! Heisenberg factorization for the actual seed-normalized cyclic characters. -/
namespace KanadeRussell.Representation
open Heisenberg Tsuchioka Tsuchioka.Fock Sectors
variable {K : Type*} [Field K] [CharZero K]

theorem shiftedTensorCyclic_heisenberg_character (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ)
    (hlow : ∀ e : ℤ, e < d → tensorCyclicSpan w seed ⊓ grade e = ⊥) :
    Product.principalHeisenbergEuler * shiftedQuotientFullCharacter w seed d ⊥ =
      shiftedQuotientVacuumCharacter w hw seed d ⊥ (bot_chevalleyStable w) := by
  have h := principalHeisenbergEuler_mul_character
    (shiftedTensorCyclicGrading w hw seed d hlow) (fun _ => rfl)
    (shiftedTensorCyclicGrading_grade_finite w hw seed d hlow)
  rwa [shiftedTensorCyclicGrading_character_eq,
    shiftedTensorCyclicGrading_vacuumCharacter_eq] at h

theorem skew_heisenberg_character (w : K) (hw : w^4-w^2+1=0) :
    Product.principalHeisenbergEuler * shiftedQuotientFullCharacter w Sectors.skewSeed 1 ⊥ =
      shiftedQuotientVacuumCharacter w hw Sectors.skewSeed 1 ⊥ (bot_chevalleyStable w) :=
  shiftedTensorCyclic_heisenberg_character w hw Sectors.skewSeed 1
    (tensor_skew_grade_below_one w hw)

theorem vacuum_heisenberg_character (w : K) (hw : w^4-w^2+1=0) :
    Product.principalHeisenbergEuler * shiftedQuotientFullCharacter w 1 0 ⊥ =
      shiftedQuotientVacuumCharacter w hw 1 0 ⊥ (bot_chevalleyStable w) :=
  shiftedTensorCyclic_heisenberg_character w hw 1 0 (tensor_vacuum_grade_below_zero w)

theorem alternating_heisenberg_character (w : K) (hw : w^4-w^2+1=0) :
    Product.principalHeisenbergEuler * shiftedQuotientFullCharacter w alternatingSeed 3 ⊥ =
      shiftedQuotientVacuumCharacter w hw alternatingSeed 3 ⊥ (bot_chevalleyStable w) :=
  shiftedTensorCyclic_heisenberg_character w hw alternatingSeed 3
    (tensor_alternating_grade_below_three w hw)

end KanadeRussell.Representation
