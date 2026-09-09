import KanadeRussell.Heisenberg.FiniteVacuumCharacter
import KanadeRussell.Heisenberg.ShiftedPolynomialGrading
import KanadeRussell.Representation.FullCharacter

/-! The shifted oscillator characters are the actual quotient-by-zero characters. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock Heisenberg PowerSeries
variable {K : Type*} [Field K] [CharZero K]

theorem bot_chevalleyStable (w : K) : ChevalleyStable w (⊥ : Submodule K (Space K)) := by
  constructor
  · intro i p hp
    have hp' : p = 0 := by simpa using hp
    subst p
    simp
  constructor
  · intro i p hp
    have hp' : p = 0 := by simpa using hp
    subst p
    simp
  · intro i p hp
    have hp' : p = 0 := by simpa using hp
    subst p
    simp

theorem bot_mkQ_injective : Function.Injective (⊥ : Submodule K (Space K)).mkQ := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_mkQ _

theorem shiftedTensorCyclicGrading_grade_finite (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ)
    (hlow : ∀ e : ℤ, e < d → tensorCyclicSpan w seed ⊓ grade e = ⊥) (n : ℤ) :
    Module.Finite K ((shiftedTensorCyclicGrading w hw seed d hlow).grade n) := by
  let G := shiftedTensorCyclicGrading w hw seed d hlow
  letI := grade_finite (K := K) (n+d)
  letI : Module.Finite K ((G.grade n).map (tensorCyclicSpan w seed).subtype) := by
    rw [shiftedTensorCyclicGrading_grade_map]
    exact Submodule.finiteDimensional_of_le inf_le_right
  let e := Submodule.equivMapOfInjective (tensorCyclicSpan w seed).subtype
    (tensorCyclicSpan w seed).subtype_injective (G.grade n)
  exact Module.Finite.of_injective e.toLinearMap e.injective

theorem shiftedTensorCyclicGrading_character_eq (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ)
    (hlow : ∀ e : ℤ, e < d → tensorCyclicSpan w seed ⊓ grade e = ⊥) :
    (shiftedTensorCyclicGrading w hw seed d hlow).character =
      shiftedQuotientFullCharacter w seed d ⊥ := by
  ext n
  simp only [GradedSystem.character, shiftedQuotientFullCharacter, coeff_mk]
  congr 1
  have h1 := (Submodule.equivMapOfInjective (tensorCyclicSpan w seed).subtype
    (tensorCyclicSpan w seed).subtype_injective
    ((shiftedTensorCyclicGrading w hw seed d hlow).grade (n:ℤ))).finrank_eq
  rw [shiftedTensorCyclicGrading_grade_map, add_comm (n:ℤ) d] at h1
  have h2 := (Submodule.equivMapOfInjective (⊥ : Submodule K (Space K)).mkQ
    bot_mkQ_injective (tensorCyclicSpan w seed ⊓ grade (d+n))).finrank_eq
  exact h1.trans h2

theorem shiftedTensorCyclicGrading_vacuumCharacter_eq (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ)
    (hlow : ∀ e : ℤ, e < d → tensorCyclicSpan w seed ⊓ grade e = ⊥) :
    (shiftedTensorCyclicGrading w hw seed d hlow).vacuumCharacter =
      shiftedQuotientVacuumCharacter w hw seed d ⊥ (bot_chevalleyStable w) := by
  ext n
  simp only [GradedSystem.vacuumCharacter, shiftedQuotientVacuumCharacter, coeff_mk]
  rw [quotientHeisenberg_vacuum_eq]
  congr 1
  have he : (shiftedTensorCyclicGrading w hw seed d hlow).grade (n:ℤ) ⊓
      vacuum (shiftedTensorCyclicGrading w hw seed d hlow).annihilate =
      shiftedTensorVacuumGrade w hw seed d n := by
    change (tensorCyclicGrading w hw seed).grade ((n:ℤ)+d) ⊓ _ =
      (tensorCyclicGrading w hw seed).grade (d+n) ⊓ _
    rw [add_comm (n:ℤ) d]
    rfl
  rw [he]
  have h1 := (Submodule.equivMapOfInjective (tensorCyclicSpan w seed).subtype
    (tensorCyclicSpan w seed).subtype_injective (shiftedTensorVacuumGrade w hw seed d n)).finrank_eq
  rw [shiftedTensorVacuumGrade_map] at h1
  have h2 := (Submodule.equivMapOfInjective (⊥ : Submodule K (Space K)).mkQ
    bot_mkQ_injective ((tensorCyclicSpan w seed ⊓ heisenbergVacuum w) ⊓ grade (d+n))).finrank_eq
  rw [shiftedQuotientCyclicGrade_vacuum_eq w hw seed d ⊥ (bot_chevalleyStable w) n] at h2
  exact h1.trans h2

end KanadeRussell.Representation
