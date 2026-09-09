import KanadeRussell.Tsuchioka.AlternatingInitialPolynomials
import KanadeRussell.Tsuchioka.TensorAlternatingCoefficients
import KanadeRussell.Tsuchioka.ChevalleyCoefficients

/-! Exact minimum-three Z-mode cancellations on the alternating highest-weight
vector. The degree-two coefficient vanishes by the cyclotomic contraction identity. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries
variable {K : Type*} [Field K] [CharZero K]

theorem summand_alternatingSeed_coeff (w : K) (hw : w^4-w^2+1=0) (j : Fin 3) (a : ℤ) :
    (summand w j alternatingSeed).coeff a =
      (creation (K := K) j : LaurentSeries (Space K)).coeff a * alternatingSeed +
      (creation (K := K) j : LaurentSeries (Space K)).coeff (a+1) *
        (MvPolynomial.C (-contraction w 1) * alternatingLinearCoefficient j) +
      (creation (K := K) j : LaurentSeries (Space K)).coeff (a+2) *
        (MvPolynomial.C ((contraction w 1)^2) * alternatingQuadraticCoefficient j) := by
  change ((creation (K := K) j : LaurentSeries (Space K)) * annihilation w j alternatingSeed).coeff a = _
  have he := tensorRootAnnihilation_eq_on_vacuum w hw (RootData.simpleRoot 0) j
    alternatingSeed (alternatingSeed_heisenbergVacuum w)
  rw [rootAnnihilation_first] at he
  rw [← he, tensorRootAnnihilation_alternatingSeed]
  simp only [RootData.rootWeight_first, mul_one, mul_add, HahnSeries.C_apply,
    HahnSeries.coeff_add, HahnSeries.coeff_mul_single, sub_zero, sub_neg_eq_add]

theorem summand_one_alternatingSeed (w : K) (hw : w^4-w^2+1=0) (j : Fin 3) :
    (summand w j alternatingSeed).coeff 1 =
      degreeOneCreation j * alternatingSeed -
      (contraction w 1 / 2) • (degreeOneCreation j ^ 2 * alternatingLinearCoefficient j) +
      ((contraction w 1)^2 / 6) • (degreeOneCreation j ^ 3 * alternatingQuadraticCoefficient j) := by
  rw [summand_alternatingSeed_coeff w hw]
  have hc (n : ℕ) : (creation (K := K) j : LaurentSeries (Space K)).coeff n = coeff n (creation j) :=
    HahnSeries.ofPowerSeries_apply_coeff (creation j) n
  have hc1 : (creation (K := K) j : LaurentSeries (Space K)).coeff 1 = coeff 1 (creation j) := hc 1
  have hc2 : (creation (K := K) j : LaurentSeries (Space K)).coeff 2 = coeff 2 (creation j) := hc 2
  have hc3 : (creation (K := K) j : LaurentSeries (Space K)).coeff 3 = coeff 3 (creation j) := hc 3
  norm_num only [Int.reduceAdd]
  rw [hc1, hc2, hc3, coeff_one_creation_linear, coeff_two_creation_linear, coeff_three_creation_linear]
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  module

theorem summand_two_alternatingSeed (w : K) (hw : w^4-w^2+1=0) (j : Fin 3) :
    (summand w j alternatingSeed).coeff 2 =
      (1/2 : K) • (degreeOneCreation j ^ 2 * alternatingSeed) -
      (contraction w 1 / 6) • (degreeOneCreation j ^ 3 * alternatingLinearCoefficient j) +
      ((contraction w 1)^2 / 24) • (degreeOneCreation j ^ 4 * alternatingQuadraticCoefficient j) := by
  rw [summand_alternatingSeed_coeff w hw]
  have hc (n : ℕ) : (creation (K := K) j : LaurentSeries (Space K)).coeff n = coeff n (creation j) :=
    HahnSeries.ofPowerSeries_apply_coeff (creation j) n
  have hc2 : (creation (K := K) j : LaurentSeries (Space K)).coeff 2 = coeff 2 (creation j) := hc 2
  have hc3 : (creation (K := K) j : LaurentSeries (Space K)).coeff 3 = coeff 3 (creation j) := hc 3
  have hc4 : (creation (K := K) j : LaurentSeries (Space K)).coeff 4 = coeff 4 (creation j) := hc 4
  norm_num only [Int.reduceAdd]
  rw [hc2, hc3, hc4, coeff_two_creation_linear, coeff_three_creation_linear, coeff_four_creation_linear]
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  module

theorem mode_neg_one_alternatingSeed (w : K) (hw : w^4-w^2+1=0) :
    mode w (-1) (alternatingSeed (K := K)) = 0 := by
  change ((1/12 : K) • ∑ j : Fin 3, summand w j alternatingSeed).coeff 1 = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_sum, summand_one_alternatingSeed w hw,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.sum_mul,
    sum_degreeOneCreation, sum_creation_sq_alternatingLinearCoefficient,
    sum_creation_cube_alternatingQuadraticCoefficient, zero_mul, smul_zero, sub_zero, add_zero]

theorem mode_neg_two_alternatingSeed_formula (w : K) (hw : w^4-w^2+1=0) :
    mode w (-2) (alternatingSeed (K := K)) =
      (4 * (6 * (contraction w 1)^2 - 6 * contraction w 1 + 1)) •
        (alternatingSeed * relativeQuadratic) := by
  change ((1/12 : K) • ∑ j : Fin 3, summand w j alternatingSeed).coeff 2 = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_sum, summand_two_alternatingSeed w hw,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
    sum_creation_sq_alternatingSeed, sum_creation_cube_alternatingLinearCoefficient,
    sum_creation_four_alternatingQuadraticCoefficient]
  have h96 (p : Space K) : (96 : Space K) * p = (96 : K) • p := by
    norm_num [Algebra.smul_def, map_ofNat]
  have h1728 (p : Space K) : (1728 : Space K) * p = (1728 : K) • p := by
    norm_num [Algebra.smul_def, map_ofNat]
  have h6912 (p : Space K) : (6912 : Space K) * p = (6912 : K) • p := by
    norm_num [Algebra.smul_def, map_ofNat]
  rw [h96, h1728, h6912]
  module

theorem contraction_one_quadratic (w : K) (hw : w^4-w^2+1=0) :
    6 * (contraction w 1)^2 - 6 * contraction w 1 + 1 = 0 := by
  rw [contraction_one w hw]
  grind only

theorem mode_neg_two_alternatingSeed (w : K) (hw : w^4-w^2+1=0) :
    mode w (-2) (alternatingSeed (K := K)) = 0 := by
  rw [mode_neg_two_alternatingSeed_formula w hw, contraction_one_quadratic w hw, mul_zero, zero_smul]

end KanadeRussell.Tsuchioka.Fock
