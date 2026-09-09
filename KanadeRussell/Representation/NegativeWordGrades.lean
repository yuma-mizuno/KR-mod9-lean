import KanadeRussell.Representation.NegativeWords
import KanadeRussell.Representation.HomogeneousProjection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Exact homogeneous spanning and the normalized highest-weight line. -/
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

/-- Degree n is spanned by lowering words of length n. -/
theorem grade_eq_span_negativeWords (n : ℤ) :
    M.grade n = Submodule.span K
      (M.negativeWordValue '' {u : List (Fin 3) | (u.length : ℤ) = n}) :=
  M.grade_eq_span_homogeneous M.negativeWordValue (fun u => (u.length : ℤ))
    M.negativeWordValue_mem_grade M.negativeWordSpan_eq_top n

/-- The only lowering word in degree zero is the empty word. -/
theorem grade_zero_eq_highestLine :
    M.grade 0 = Submodule.span K {M.highestVector} := by
  rw [M.grade_eq_span_negativeWords]
  congr 1
  ext v
  simp

theorem finrank_grade_zero : Module.finrank K (M.grade 0) = 1 := by
  rw [M.grade_zero_eq_highestLine]
  exact finrank_span_singleton M.highestVector_ne_zero

theorem coeff_zero_character : PowerSeries.coeff 0 M.character = 1 := by
  rw [M.coeff_character]
  simp [M.finrank_grade_zero]

end KanadeRussell.Representation.PrincipalHighestWeightModule
