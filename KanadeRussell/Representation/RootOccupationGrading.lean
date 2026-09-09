import KanadeRussell.Representation.RootOccupationWeights
import KanadeRussell.Representation.FiniteWeightSpaces
import KanadeRussell.Representation.NegativeWordGrades

/-! The actual module is graded by integer simple-root occupations, supported
in the positive cone. Principal degree is the sum of these occupations. -/
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice
open scoped Classical
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

noncomputable def rootGrade (beta : RootCoefficients) : Submodule K V :=
  M.extendedWeightSpace (occupationWeight M.highestWeightLabels beta)

theorem negativeWordValue_mem_rootGrade (u : List (Fin 3)) :
    M.negativeWordValue u ∈ M.rootGrade (wordOccupation u) :=
  M.negativeWordValue_mem_occupationWeightSpace u

theorem rootGrade_iSupIndep : iSupIndep M.rootGrade :=
  M.extendedWeightSpace_iSupIndep.comp (occupationWeight_injective M.highestWeightLabels)

theorem rootGrade_iSup_eq_top : (⨆ beta, M.rootGrade beta) = ⊤ := by
  apply top_unique
  rw [← M.negativeWordSpan_eq_top]
  apply Submodule.span_le.mpr
  rintro v ⟨u, rfl⟩
  exact Submodule.mem_iSup_of_mem (wordOccupation u) (M.negativeWordValue_mem_rootGrade u)

theorem rootGrade_isInternal : DirectSum.IsInternal M.rootGrade :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    M.rootGrade_iSupIndep M.rootGrade_iSup_eq_top

theorem rootGrade_finite (beta : RootCoefficients) : Module.Finite K (M.rootGrade beta) :=
  M.extendedWeightSpace_finite _

theorem rootGrade_le_grade (beta : RootCoefficients) :
    M.rootGrade beta ≤ M.grade (totalDegree beta) :=
  M.extendedWeightSpace_le_grade _ _ rfl

theorem rootGrade_support (beta : RootCoefficients) (hbeta : M.rootGrade beta ≠ ⊥) :
    ∀ i, 0 ≤ beta i := by
  obtain ⟨gamma, hgamma, heq⟩ := M.extendedWeightSpace_occupation_support _ hbeta
  have hgb : gamma = beta := occupationWeight_injective M.highestWeightLabels heq
  simpa only [hgb] using hgamma

theorem rootGrade_eq_bot_of_negative (beta : RootCoefficients) (i : Fin 3)
    (hi : beta i < 0) : M.rootGrade beta = ⊥ := by
  by_contra h
  exact (not_lt_of_ge (M.rootGrade_support beta h i)) hi

/-- Summing root spaces of total occupation n gives exactly principal degree n. -/
theorem grade_eq_iSup_rootGrade (n : ℤ) :
    M.grade n = ⨆ beta : RootCoefficients, ⨆ (_ : totalDegree beta = n), M.rootGrade beta := by
  apply le_antisymm
  · rw [M.grade_eq_span_negativeWords]
    apply Submodule.span_le.mpr
    rintro v ⟨u, hu, rfl⟩
    exact Submodule.mem_iSup_of_mem (wordOccupation u)
      (Submodule.mem_iSup_of_mem (by simpa only [totalDegree_wordOccupation, Set.mem_setOf_eq] using hu)
        (M.negativeWordValue_mem_rootGrade u))
  · apply iSup_le
    intro beta
    apply iSup_le
    intro hbeta
    simpa only [hbeta] using M.rootGrade_le_grade beta

end KanadeRussell.Representation.PrincipalHighestWeightModule
