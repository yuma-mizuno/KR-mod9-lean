import KanadeRussell.Tsuchioka.TensorAlternatingCoefficients

/-! The degree-three coefficient of the actual tensor creation exponential. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries
open RootData (Lattice rootWeight)
variable {K : Type*} [Field K] [CharZero K]

theorem coeff_three_tensorRootCreation (w : K) (beta : Lattice) (j : Fin 3) :
    coeff 3 (tensorRootCreation w beta j) =
      (288 * rootWeight (w ^ (-1 : ℤ)) beta ^ 3) • degreeOneVariable j ^ 3 := by
  have h1 := coeff_one_tensorRootCreation w beta j
  rw [tensorRootCreation, FormalSeries.coeff_one_exponential
    (constantCoeff_tensorRootCreationLog w beta j)] at h1
  have h := congrArg (coeff 2)
    (FormalSeries.derivative_exponential (constantCoeff_tensorRootCreationLog w beta j))
  have ha : Finset.antidiagonal 2 = {(0,2),(1,1),(2,0)} := rfl
  have hz2 : coeff 2 (tensorRootCreationLog w beta j) = 0 := by
    simp [tensorRootCreationLog, IsMode]
  have hz3 : coeff 3 (tensorRootCreationLog w beta j) = 0 := by
    simp [tensorRootCreationLog, IsMode]
  change coeff 2 (derivative (Space K) (tensorRootCreation w beta j)) =
    coeff 2 (tensorRootCreation w beta j * derivative (Space K) (tensorRootCreationLog w beta j)) at h
  rw [coeff_derivative, coeff_mul] at h
  norm_num [ha, Finset.sum_insert, Finset.sum_singleton, Prod.fst, Prod.snd,
    coeff_derivative, hz2, hz3, h1, Nat.reduceAdd,
    zero_mul, mul_zero, add_zero, zero_add, mul_one] at h
  have hr : (3 : K) • coeff 3 (tensorRootCreation w beta j) =
      coeff 2 (tensorRootCreation w beta j) *
        (MvPolynomial.C (12 * rootWeight (w ^ (-1 : ℤ)) beta) * degreeOneVariable j) := by
    convert h using 1 <;> norm_num [Algebra.smul_def, map_ofNat, map_mul] <;> ring
  have hh := congrArg (fun p : Space K => (1/3 : K) • p) hr
  rw [coeff_two_tensorRootCreation] at hh
  norm_num [smul_smul, smul_mul_assoc, MvPolynomial.C_eq_smul_one,
    mul_smul_comm, mul_one] at hh
  rw [hh]
  simp only [zpow_neg_one, ← pow_succ]
  congr 1 <;> ring

end KanadeRussell.Tsuchioka.Fock
