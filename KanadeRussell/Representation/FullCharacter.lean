import KanadeRussell.Representation.ShiftedSectorCharacters
import KanadeRussell.Representation.FiniteGrades

/-! The full character uses the dimensions of the actual quotient grade images,
with degree measured from the selected highest-weight vector. -/
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

noncomputable def shiftedQuotientFullCharacter (w : K) (seed : Space K) (d : ℤ)
    (S : Submodule K (Space K)) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    (Module.finrank K (shiftedQuotientCyclicGrade w seed d S n) : ℤ)

theorem coeff_shiftedQuotientFullCharacter (w : K) (seed : Space K) (d : ℤ)
    (S : Submodule K (Space K)) (n : ℕ) :
    PowerSeries.coeff n (shiftedQuotientFullCharacter w seed d S) =
      (Module.finrank K (shiftedQuotientCyclicGrade w seed d S n) : ℤ) :=
  PowerSeries.coeff_mk _ _

end KanadeRussell.Representation
