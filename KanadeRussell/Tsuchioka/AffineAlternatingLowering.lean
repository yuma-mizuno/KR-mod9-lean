import KanadeRussell.Tsuchioka.TensorThirdCoefficient
import KanadeRussell.Tsuchioka.AffineAlternatingHighestWeight

/-! The two zero-weight lowering equations on the alternating seed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries
open RootData (Lattice rootWeight)
variable {K : Type*} [Field K] [CharZero K]

theorem sum_variable_sq_alternatingLinearCoefficient :
    ∑ j : Fin 3, degreeOneVariable j ^ 2 * alternatingLinearCoefficient (K := K) j =
      2 * (diagonalCoordinate firstMode * alternatingSeed) := by
  norm_num [Fin.sum_univ_three, alternatingLinearCoefficient, alternatingSeed,
    diagonalCoordinate, degreeOneVariable, Matrix.cons_val_two]
  ring

theorem sum_variable_cube_alternatingQuadraticCoefficient :
    ∑ j : Fin 3, degreeOneVariable j ^ 3 * alternatingQuadraticCoefficient (K := K) j =
      diagonalCoordinate firstMode * alternatingSeed := by
  norm_num [Fin.sum_univ_three, alternatingQuadraticCoefficient, alternatingSeed,
    diagonalCoordinate, degreeOneVariable, Matrix.cons_val_two]
  ring

theorem tensorRootSummand_neg_one_alternatingSeed (w : K) (beta : Lattice) (j : Fin 3) :
    (tensorRootSummand w beta j alternatingSeed).coeff 1 =
      (12 * rootWeight (w ^ (-1 : ℤ)) beta) • (degreeOneVariable j * alternatingSeed) -
      (72 * contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta ^ 2) •
        (degreeOneVariable j ^ 2 * alternatingLinearCoefficient j) +
      (288 * (contraction w 1 * rootWeight w beta)^2 * rootWeight (w ^ (-1 : ℤ)) beta ^ 3) •
        (degreeOneVariable j ^ 3 * alternatingQuadraticCoefficient j) := by
  rw [tensorRootSummand_alternatingSeed_coeff]
  have hc (n : ℕ) : (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff n =
      coeff n (tensorRootCreation w beta j) :=
    HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) n
  have hc1 : (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 = coeff 1 (tensorRootCreation w beta j) := hc 1
  have hc2 : (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 2 = coeff 2 (tensorRootCreation w beta j) := hc 2
  have hc3 : (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 3 = coeff 3 (tensorRootCreation w beta j) := hc 3
  norm_num only [Int.reduceAdd]
  rw [hc1, hc2, hc3, coeff_one_tensorRootCreation, coeff_two_tensorRootCreation,
    coeff_three_tensorRootCreation]
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul]
  module

theorem tensorRootMode_neg_one_alternatingSeed (w : K) (beta : Lattice) :
    tensorRootMode w beta (-1) (alternatingSeed (K := K)) =
      (rootWeight (w ^ (-1 : ℤ)) beta -
        12 * contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta ^ 2 +
        24 * (contraction w 1 * rootWeight w beta)^2 * rootWeight (w ^ (-1 : ℤ)) beta ^ 3) •
      (diagonalCoordinate firstMode * alternatingSeed) := by
  change ((1/12 : K) • ∑ j : Fin 3, tensorRootSummand w beta j alternatingSeed).coeff 1 = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_sum,
    tensorRootSummand_neg_one_alternatingSeed, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.sum_mul,
    sum_variable_sq_alternatingLinearCoefficient,
    sum_variable_cube_alternatingQuadraticCoefficient]
  have hs : ∑ j : Fin 3, degreeOneVariable (K := K) j = diagonalCoordinate firstMode := rfl
  rw [hs]
  have htwo (p : Space K) : (2 : Space K) * p = (2 : K) • p := by
    norm_num [Algebra.smul_def, map_ofNat]
  rw [htwo]
  module

theorem chevalleyF_zero_alternatingSeed (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 0 (alternatingSeed (K := K)) = 0 := by
  have hh : heisenbergMode w (-1) (alternatingSeed (K := K)) =
      diagonalCoordinate firstMode * alternatingSeed := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    rfl
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorRootMode_neg_one_alternatingSeed, hh, smul_smul]
  have hz : chevalleyFCoordinates w 0 3 = 0 := rfl
  rw [hz, zero_smul, add_zero, ← add_smul, ← add_smul]
  suffices h : chevalleyFCoordinates w 0 0 *
      (rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 0) -
        12 * contraction w 1 * rootWeight w (RootData.simpleRoot 0) * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 0)^2 +
        24 * (contraction w 1 * rootWeight w (RootData.simpleRoot 0))^2 * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 0)^3) +
      chevalleyFCoordinates w 0 1 *
      (rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) -
        12 * contraction w 1 * rootWeight w (RootData.simpleRoot 1) * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1)^2 +
        24 * (contraction w 1 * rootWeight w (RootData.simpleRoot 1))^2 * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1)^3) +
      chevalleyFCoordinates w 0 2 = 0 by rw [h, zero_smul]
  clear hh hz
  have hi : rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) = -w^3+w^2-1 := by
    rw [RootData.rootWeight_second, Scalar.zpow_phasePolynomial w hw (-1)]
    norm_num [Scalar.phasePolynomial]
    grind only
  rw [hi]
  simp only [RootData.rootWeight_first, RootData.rootWeight_second, contraction_one w hw]
  norm_num [chevalleyFCoordinates, Matrix.cons_val_two, Matrix.cons_val_three]
  grind only

theorem chevalleyF_one_alternatingSeed (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 1 (alternatingSeed (K := K)) = 0 := by
  have hh : heisenbergMode w (-1) (alternatingSeed (K := K)) =
      diagonalCoordinate firstMode * alternatingSeed := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    rfl
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorRootMode_neg_one_alternatingSeed, hh, smul_smul]
  have hz : chevalleyFCoordinates w 1 3 = 0 := rfl
  rw [hz, zero_smul, add_zero, ← add_smul, ← add_smul]
  suffices h : chevalleyFCoordinates w 1 0 *
      (rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 0) -
        12 * contraction w 1 * rootWeight w (RootData.simpleRoot 0) * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 0)^2 +
        24 * (contraction w 1 * rootWeight w (RootData.simpleRoot 0))^2 * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 0)^3) +
      chevalleyFCoordinates w 1 1 *
      (rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) -
        12 * contraction w 1 * rootWeight w (RootData.simpleRoot 1) * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1)^2 +
        24 * (contraction w 1 * rootWeight w (RootData.simpleRoot 1))^2 * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1)^3) +
      chevalleyFCoordinates w 1 2 = 0 by rw [h, zero_smul]
  clear hh hz
  have hi : rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) = -w^3+w^2-1 := by
    rw [RootData.rootWeight_second, Scalar.zpow_phasePolynomial w hw (-1)]
    norm_num [Scalar.phasePolynomial]
    grind only
  rw [hi]
  simp only [RootData.rootWeight_first, RootData.rootWeight_second, contraction_one w hw]
  norm_num [chevalleyFCoordinates, Matrix.cons_val_two, Matrix.cons_val_three]
  grind only

end KanadeRussell.Tsuchioka.Fock
