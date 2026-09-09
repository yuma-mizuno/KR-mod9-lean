import KanadeRussell.Representation.ChevalleyAction
import Mathlib.Algebra.DirectSum.Module

/-! Graded integrable cyclic highest-weight modules for the fixed affine Serre
presentation. This is representation data, with no character equation. -/
namespace KanadeRussell.Representation
attribute [local instance] LieRing.ofAssociativeRing

structure PrincipalHighestWeightModule (K V : Type*) [Field K]
    [AddCommGroup V] [Module K V] where
  action : ChevalleyAction K V
  grade : ℤ → Submodule K V
  grading_internal : DirectSum.IsInternal grade
  grade_negative : ∀ n, n < 0 → grade n = ⊥
  grade_finite : ∀ n, Module.Finite K (grade n)
  E_grade : ∀ i n v, v ∈ grade n → action.E i v ∈ grade (n-1)
  F_grade : ∀ i n v, v ∈ grade n → action.F i v ∈ grade (n+1)
  H_grade : ∀ i n v, v ∈ grade n → action.H i v ∈ grade n
  highestVector : V
  highestVector_ne_zero : highestVector ≠ 0
  highestVector_grade : highestVector ∈ grade 0
  highestWeight : Fin 3 → ℕ
  E_highestVector : ∀ i, action.E i highestVector = 0
  H_highestVector : ∀ i, action.H i highestVector = (highestWeight i : K) • highestVector
  E_locally_nilpotent : ∀ i v, ∃ n : ℕ, ((action.E i)^n) v = 0
  F_locally_nilpotent : ∀ i v, ∃ n : ℕ, ((action.F i)^n) v = 0
  cyclic : Submodule.span K ((fun a : Module.End K V => a highestVector) ''
    (Algebra.adjoin K (Set.range action.E ∪ (Set.range action.F ∪ Set.range action.H)) :
      Set (Module.End K V))) = ⊤

namespace PrincipalHighestWeightModule
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The principal character of the actual internal grading, normalized at the
nonzero highest-weight vector in degree zero. -/
noncomputable def character (M : PrincipalHighestWeightModule K V) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Module.finrank K (M.grade (n : ℤ)) : ℤ)

theorem coeff_character (M : PrincipalHighestWeightModule K V) (n : ℕ) :
    PowerSeries.coeff n M.character = (Module.finrank K (M.grade (n : ℤ)) : ℤ) :=
  PowerSeries.coeff_mk _ _

end PrincipalHighestWeightModule
end KanadeRussell.Representation
