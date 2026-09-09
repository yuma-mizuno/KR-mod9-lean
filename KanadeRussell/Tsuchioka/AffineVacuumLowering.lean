import KanadeRussell.Tsuchioka.AffineHighestWeight
import KanadeRussell.Tsuchioka.TensorDegreeOne

/-! Concrete simple-root lowering equations on the polynomial vacuum.
The calculation uses the actual tensor fields, not an integrability assumption. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries
open RootData (Lattice rootWeight)
variable {K : Type*} [Field K] [CharZero K]

/-- The first negative root mode on the vacuum comes from the linear creation term. -/
theorem tensorRootMode_neg_one_vacuum (w : K) (beta : Lattice) :
    tensorRootMode w beta (-1) (1 : Space K) =
      rootWeight (w ^ (-1 : ℤ)) beta • diagonalCoordinate firstMode := by
  have hs (j : Fin 3) : (tensorRootSummand w beta j (1 : Space K)).coeff 1 =
      MvPolynomial.C (12 * rootWeight (w ^ (-1 : ℤ)) beta) * degreeOneVariable j := by
    change ((tensorRootCreation w beta j : LaurentSeries (Space K)) *
      tensorRootAnnihilation w beta j 1).coeff 1 = _
    rw [map_one, mul_one]
    exact (HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 1).trans
      (coeff_one_tensorRootCreation w beta j)
  change ((1/12 : K) • ∑ j : Fin 3, tensorRootSummand w beta j (1 : Space K)).coeff 1 = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_add, hs, Fin.sum_univ_three,
    MvPolynomial.C_eq_smul_one, smul_mul_assoc, one_mul, smul_add, smul_smul]
  simp only [diagonalCoordinate, Fin.sum_univ_three, degreeOneVariable]
  module

/-- The zero Dynkin label at node 1 gives a proved lowering equation. -/
theorem chevalleyF_one_vacuum (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 1 (1 : Space K) = 0 := by
  have hs : chevalleyFCoordinates w 1 0 +
      chevalleyFCoordinates w 1 1 * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) +
      chevalleyFCoordinates w 1 2 = 0 := by
    rw [RootData.rootWeight_second, Scalar.zpow_phasePolynomial w hw (-1)]
    norm_num [chevalleyFCoordinates, Scalar.phasePolynomial, Matrix.cons_val_two, Matrix.cons_val_three]
    grind only
  have hh : heisenbergMode w (-1) (1 : Space K) = diagonalCoordinate firstMode := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    simp
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorRootMode_neg_one_vacuum, RootData.rootWeight_first,
    one_smul, hh, smul_smul]
  have hzero : chevalleyFCoordinates w 1 3 = 0 := rfl
  rw [hzero, zero_smul, add_zero, ← add_smul, ← add_smul, hs, zero_smul]

/-- The zero Dynkin label at node 2 gives a proved lowering equation. -/
theorem chevalleyF_two_vacuum (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 2 (1 : Space K) = 0 := by
  have hs : chevalleyFCoordinates w 2 0 +
      chevalleyFCoordinates w 2 1 * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) +
      chevalleyFCoordinates w 2 2 = 0 := by
    rw [RootData.rootWeight_second, Scalar.zpow_phasePolynomial w hw (-1)]
    norm_num [chevalleyFCoordinates, Scalar.phasePolynomial, Matrix.cons_val_two, Matrix.cons_val_three]
    grind only
  have hh : heisenbergMode w (-1) (1 : Space K) = diagonalCoordinate firstMode := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    simp
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorRootMode_neg_one_vacuum, RootData.rootWeight_first,
    one_smul, hh, smul_smul]
  have hzero : chevalleyFCoordinates w 2 3 = 0 := rfl
  rw [hzero, zero_smul, add_zero, ← add_smul, ← add_smul, hs, zero_smul]

end KanadeRussell.Tsuchioka.Fock
