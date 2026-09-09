import KanadeRussell.Representation.AffineWeightLattice

/-! Dominant rigidity for the integer Casimir form. This is a root-lattice
statement; it does not assume or assert a Casimir identity on a representation. -/
namespace KanadeRussell.Representation.AffineWeightLattice
open Tsuchioka.Fock

theorem twice_casimir_rho (lambda beta : RootCoefficients) :
    2 * casimir (fun i => lambda i + 1) beta =
      -(∑ i : Fin 3, symmetrizer i * beta i *
        (lambda i + weightLabels lambda beta i + 2)) := by
  norm_num [casimir_eq, weightLabels, Fin.sum_univ_three, symmetrizer,
    affineCartanMatrix, Matrix.cons_val_two]
  ring

theorem casimir_rho_neg_of_dominant (lambda beta : RootCoefficients)
    (hlambda : ∀ i, 0 ≤ lambda i) (hbeta : ∀ i, 0 ≤ beta i)
    (hdominant : ∀ i, 0 ≤ weightLabels lambda beta i) (hne : beta ≠ 0) :
    casimir (fun i => lambda i + 1) beta < 0 := by
  have hex : ∃ i, beta i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hex
  have hpos : 0 < beta i := lt_of_le_of_ne (hbeta i) (Ne.symm hi)
  have hs : 0 < ∑ j : Fin 3, symmetrizer j * beta j *
      (lambda j + weightLabels lambda beta j + 2) := by
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg (mul_nonneg (le_of_lt (symmetrizer_positive j)) (hbeta j))
        (by linarith [hlambda j, hdominant j])
    · exact ⟨i, Finset.mem_univ i, mul_pos (mul_pos (symmetrizer_positive i) hpos)
        (by linarith [hlambda i, hdominant i])⟩
  have heq := twice_casimir_rho lambda beta
  omega

theorem eq_zero_of_casimir_rho_eq_zero_of_dominant (lambda beta : RootCoefficients)
    (hlambda : ∀ i, 0 ≤ lambda i) (hbeta : ∀ i, 0 ≤ beta i)
    (hdominant : ∀ i, 0 ≤ weightLabels lambda beta i)
    (hcasimir : casimir (fun i => lambda i + 1) beta = 0) : beta = 0 := by
  by_contra hne
  have := casimir_rho_neg_of_dominant lambda beta hlambda hbeta hdominant hne
  omega

end KanadeRussell.Representation.AffineWeightLattice
