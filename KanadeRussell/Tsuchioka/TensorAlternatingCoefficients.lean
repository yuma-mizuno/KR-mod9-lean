import KanadeRussell.Tsuchioka.AlternatingSeed

/-! Exact Laurent coefficients of the tensor root action on the alternating seed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries
open RootData (Lattice rootWeight)
variable {K : Type*} [Field K] [CharZero K]

theorem coeff_two_tensorRootCreation (w : K) (beta : Lattice) (j : Fin 3) :
    coeff 2 (tensorRootCreation w beta j) =
      (72 * rootWeight (w ^ (-1 : ℤ)) beta ^ 2) • (degreeOneVariable j ^ 2) := by
  rw [tensorRootCreation, FormalSeries.coeff_two_exponential
    (constantCoeff_tensorRootCreationLog w beta j)]
  have h1 := coeff_one_tensorRootCreation w beta j
  rw [tensorRootCreation, FormalSeries.coeff_one_exponential
    (constantCoeff_tensorRootCreationLog w beta j)] at h1
  rw [h1]
  have h2 : coeff 2 (tensorRootCreationLog w beta j) = 0 := by
    simp [tensorRootCreationLog, IsMode]
  rw [h2, zero_add, IsScalarTower.algebraMap_apply ℚ K (Space K), MvPolynomial.algebraMap_eq]
  norm_num [MvPolynomial.C_eq_smul_one, mul_pow, smul_pow, smul_smul]
  module

theorem tensorRootAnnihilation_alternatingSeed (w : K) (beta : Lattice) (j : Fin 3) :
    tensorRootAnnihilation w beta j alternatingSeed =
      HahnSeries.C alternatingSeed +
      HahnSeries.single (-1 : ℤ)
        (MvPolynomial.C (-contraction w 1 * rootWeight w beta) * alternatingLinearCoefficient j) +
      HahnSeries.single (-2 : ℤ)
        (MvPolynomial.C ((contraction w 1 * rootWeight w beta)^2) * alternatingQuadraticCoefficient j) := by
  have hx (a : Fin 3) : tensorRootAnnihilation w beta j (degreeOneVariable a) =
      HahnSeries.C (degreeOneVariable a) +
        (if a = j then HahnSeries.single (-1 : ℤ)
          (MvPolynomial.C (-contraction w 1 * rootWeight w beta)) else 0) := by
    by_cases ha : a = j <;>
      simp [tensorRootAnnihilation, degreeOneVariable, firstMode, ha]
  have hp : tensorRootAnnihilation w beta j alternatingSeed =
      HahnSeries.C alternatingSeed +
      HahnSeries.single (-1 : ℤ) (MvPolynomial.C (-contraction w 1 * rootWeight w beta)) *
        HahnSeries.C (alternatingLinearCoefficient j) +
      HahnSeries.single (-1 : ℤ) (MvPolynomial.C (-contraction w 1 * rootWeight w beta)) ^ 2 *
        HahnSeries.C (alternatingQuadraticCoefficient j) := by
    simp only [alternatingSeed, map_mul, map_sub, hx]
    fin_cases j <;>
      simp only [alternatingLinearCoefficient, alternatingQuadraticCoefficient,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        map_sub, map_mul, map_add, map_neg, map_ofNat] <;>
      norm_num [Fin.ext_iff] <;>
      simp only [← HahnSeries.C_apply, map_add, map_mul, map_sub, map_pow,
        map_ofNat, map_neg] <;> ring
  rw [hp]
  simp only [HahnSeries.C_apply, pow_two, HahnSeries.single_mul_single]
  norm_num only [Int.reduceAdd, add_zero]
  congr 2
  rw [← map_mul]
  congr 2
  ring

theorem tensorRootSummand_alternatingSeed_coeff (w : K) (beta : Lattice) (j : Fin 3) (a : ℤ) :
    (tensorRootSummand w beta j alternatingSeed).coeff a =
      (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff a * alternatingSeed +
      (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff (a+1) *
        (MvPolynomial.C (-contraction w 1 * rootWeight w beta) * alternatingLinearCoefficient j) +
      (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff (a+2) *
        (MvPolynomial.C ((contraction w 1 * rootWeight w beta)^2) * alternatingQuadraticCoefficient j) := by
  change ((tensorRootCreation w beta j : LaurentSeries (Space K)) *
    tensorRootAnnihilation w beta j alternatingSeed).coeff a = _
  rw [tensorRootAnnihilation_alternatingSeed]
  simp only [mul_add, HahnSeries.C_apply, HahnSeries.coeff_add,
    HahnSeries.coeff_mul_single, sub_zero, sub_neg_eq_add]

end KanadeRussell.Tsuchioka.Fock
