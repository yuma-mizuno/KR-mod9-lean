import KanadeRussell.Representation.WeylMultiplicity

/-! The actual root-grade dimensions as a scalar-valued multiplicity function.
Support, highest multiplicity and ordinary Weyl symmetry follow from the
proved highest-weight structure. No character evaluation is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

noncomputable def rootMultiplicity (beta : RootCoefficients) : K :=
  (Module.finrank K (M.rootGrade beta) : K)

theorem rootMultiplicity_eq_zero_of_not_nonneg (beta : RootCoefficients)
    (hbeta : ¬ (∀ i, 0 ≤ beta i)) : M.rootMultiplicity beta = 0 := by
  have hg : M.rootGrade beta = ⊥ := by
    by_contra hn
    exact hbeta (M.rootGrade_support beta hn)
  unfold rootMultiplicity
  rw [hg]
  simp

theorem rootGrade_zero_eq_highestLine :
    M.rootGrade 0 = Submodule.span K {M.highestVector} := by
  apply le_antisymm
  · simpa only [totalDegree, Pi.zero_apply, Finset.sum_const_zero,
      M.grade_zero_eq_highestLine] using M.rootGrade_le_grade 0
  · apply Submodule.span_le.mpr
    intro v hv
    have hv' : v = M.highestVector := Set.mem_singleton_iff.mp hv
    subst v
    change M.highestVector ∈ M.rootGrade 0
    simpa only [wordOccupation_nil, negativeWordValue_nil] using
      M.negativeWordValue_mem_rootGrade []

theorem rootMultiplicity_zero : M.rootMultiplicity 0 = 1 := by
  unfold rootMultiplicity
  rw [M.rootGrade_zero_eq_highestLine, finrank_span_singleton M.highestVector_ne_zero, Nat.cast_one]

theorem rootMultiplicity_simpleReflection (i : Fin 3) (beta : RootCoefficients) :
    M.rootMultiplicity (simpleReflection M.highestWeightLabels i beta) =
      M.rootMultiplicity beta := by
  exact congrArg (fun n : ℕ => (n : K)) (M.finrank_rootGrade_simpleReflection i beta).symm

theorem rootMultiplicity_reflectionWord (u : List (Fin 3)) (beta : RootCoefficients) :
    M.rootMultiplicity (u.foldr (simpleReflection M.highestWeightLabels) beta) =
      M.rootMultiplicity beta := by
  exact congrArg (fun n : ℕ => (n : K)) (M.finrank_rootGrade_reflectionWord u beta)

end KanadeRussell.Representation.PrincipalHighestWeightModule
