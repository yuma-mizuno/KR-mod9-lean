import KanadeRussell.Tsuchioka.TensorAlternatingCoefficients

/-! Root zero modes and positive modes on the alternating degree-three seed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries
open RootData (Lattice rootWeight)
variable {K : Type*} [Field K] [CharZero K]

private theorem creation_zero (w : K) (beta : Lattice) (j : Fin 3) :
    (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 0 = 1 := by
  exact (HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 0).trans
    (by simpa only [coeff_zero_eq_constantCoeff, tensorRootCreation] using
      FormalSeries.constantCoeff_exponential (constantCoeff_tensorRootCreationLog w beta j))

private theorem creation_one (w : K) (beta : Lattice) (j : Fin 3) :
    (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 =
      MvPolynomial.C (12 * rootWeight (w ^ (-1 : ℤ)) beta) * degreeOneVariable j :=
  (HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 1).trans
    (coeff_one_tensorRootCreation w beta j)

private theorem creation_two (w : K) (beta : Lattice) (j : Fin 3) :
    (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 2 =
      (72 * rootWeight (w ^ (-1 : ℤ)) beta ^ 2) • (degreeOneVariable j ^ 2) :=
  (HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 2).trans
    (coeff_two_tensorRootCreation w beta j)

theorem tensorRootSummand_zero_alternatingSeed (w : K) (beta : Lattice) (j : Fin 3) :
    (tensorRootSummand w beta j alternatingSeed).coeff 0 =
      alternatingSeed +
      (-12 * contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta) •
        (degreeOneVariable j * alternatingLinearCoefficient j) +
      (72 * (contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta)^2) •
        (degreeOneVariable j ^ 2 * alternatingQuadraticCoefficient j) := by
  rw [tensorRootSummand_alternatingSeed_coeff]
  simp only [zero_add, creation_zero, creation_one, creation_two,
    MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, smul_smul]
  module

theorem tensorRootMode_zero_alternatingSeed (w : K) (beta : Lattice) :
    tensorRootMode w beta 0 (alternatingSeed (K := K)) =
      (1/4 - 3 * contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta +
        6 * (contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta)^2) •
        alternatingSeed := by
  change ((1/12:K) • ∑ j : Fin 3,
    tensorRootSummand w beta j alternatingSeed).coeff 0 = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_sum, tensorRootSummand_zero_alternatingSeed,
    Finset.sum_add_distrib, ← Finset.smul_sum, sum_variable_alternatingLinearCoefficient,
    sum_variable_sq_alternatingQuadraticCoefficient, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul K 3 alternatingSeed]
  have hm : (3 : Space K) * alternatingSeed = (3 : K) • alternatingSeed := by
    norm_num [Algebra.smul_def, map_ofNat]
  rw [hm]
  module

theorem tensorRootSummand_one_alternatingSeed (w : K) (beta : Lattice) (j : Fin 3) :
    (tensorRootSummand w beta j alternatingSeed).coeff (-1) =
      (-contraction w 1 * rootWeight w beta) • alternatingLinearCoefficient j +
      (12 * rootWeight (w ^ (-1 : ℤ)) beta * (contraction w 1 * rootWeight w beta)^2) •
        (degreeOneVariable j * alternatingQuadraticCoefficient j) := by
  rw [tensorRootSummand_alternatingSeed_coeff]
  have hz : (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff (-1) = 0 := by
    simp [PowerSeries.coeff_coe]
  norm_num only [Int.reduceAdd, hz, creation_zero, creation_one, zero_mul, zero_add]
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, smul_smul]
  module

theorem tensorRootMode_one_alternatingSeed (w : K) (beta : Lattice) :
    tensorRootMode w beta 1 (alternatingSeed (K := K)) = 0 := by
  change ((1/12:K) • ∑ j : Fin 3,
    tensorRootSummand w beta j alternatingSeed).coeff (-1) = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_sum, tensorRootSummand_one_alternatingSeed,
    Finset.sum_add_distrib, ← Finset.smul_sum, sum_alternatingLinearCoefficient,
    sum_variable_alternatingQuadraticCoefficient, smul_zero, add_zero]

end KanadeRussell.Tsuchioka.Fock
