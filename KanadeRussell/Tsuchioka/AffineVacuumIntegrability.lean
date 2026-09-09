import KanadeRussell.Tsuchioka.AffineVacuumLowering
import KanadeRussell.Tsuchioka.TensorAlternatingCoefficients
import KanadeRussell.Tsuchioka.AffineSkewLowering

/-! The remaining simple-root integrability relation on the tensor vacuum,
computed using squarefree polynomials in the first oscillator variables. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries
open RootData (Lattice rootWeight)
variable {K : Type*} [Field K] [CharZero K]

noncomputable def vacuumCubic : Space K :=
  degreeOneVariable 0 * degreeOneVariable 1 * degreeOneVariable 2

noncomputable def vacuumCubicComplement (j : Fin 3) : Space K :=
  ![degreeOneVariable 1 * degreeOneVariable 2,
    degreeOneVariable 0 * degreeOneVariable 2,
    degreeOneVariable 0 * degreeOneVariable 1] j

omit [CharZero K] in
theorem variable_mul_vacuumCubicComplement (j : Fin 3) :
    degreeOneVariable j * vacuumCubicComplement (K := K) j = vacuumCubic := by
  fin_cases j
  · change degreeOneVariable 0 * (degreeOneVariable 1 * degreeOneVariable 2) =
      degreeOneVariable (K := K) 0 * degreeOneVariable 1 * degreeOneVariable 2
    ring
  · change degreeOneVariable 1 * (degreeOneVariable 0 * degreeOneVariable 2) =
      degreeOneVariable (K := K) 0 * degreeOneVariable 1 * degreeOneVariable 2
    ring
  · change degreeOneVariable 2 * (degreeOneVariable 0 * degreeOneVariable 1) =
      degreeOneVariable (K := K) 0 * degreeOneVariable 1 * degreeOneVariable 2
    ring

omit [CharZero K] in
theorem tensorRootAnnihilation_vacuumCubic (w : K) (beta : Lattice) (j : Fin 3) :
    tensorRootAnnihilation w beta j vacuumCubic =
      HahnSeries.C vacuumCubic + HahnSeries.single (-1 : ℤ)
        (MvPolynomial.C (-contraction w 1 * rootWeight w beta) * vacuumCubicComplement j) := by
  have hx (a : Fin 3) : tensorRootAnnihilation w beta j (degreeOneVariable a) =
      HahnSeries.C (degreeOneVariable a) +
        (if a = j then HahnSeries.single (-1 : ℤ)
          (MvPolynomial.C (-contraction w 1 * rootWeight w beta)) else 0) := by
    by_cases ha : a = j <;>
      simp [tensorRootAnnihilation, degreeOneVariable, firstMode, ha]
  have hp : tensorRootAnnihilation w beta j vacuumCubic =
      HahnSeries.C vacuumCubic + HahnSeries.single (-1 : ℤ)
        (MvPolynomial.C (-contraction w 1 * rootWeight w beta)) *
          HahnSeries.C (vacuumCubicComplement j) := by
    simp only [vacuumCubic, map_mul, hx]
    fin_cases j <;>
      norm_num [vacuumCubicComplement, Fin.ext_iff, Matrix.cons_val_two] <;>
      simp only [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_apply, map_mul] <;> ring
  rw [hp]
  simp only [HahnSeries.C_apply, HahnSeries.single_mul_single]
  norm_num

theorem tensorRootSummand_neg_one_vacuumCubic (w : K) (beta : Lattice) (j : Fin 3) :
    (tensorRootSummand w beta j vacuumCubic).coeff 1 =
      (12 * rootWeight (w ^ (-1 : ℤ)) beta -
        72 * contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta ^ 2) •
          (degreeOneVariable j * vacuumCubic) := by
  change ((tensorRootCreation w beta j : LaurentSeries (Space K)) *
    tensorRootAnnihilation w beta j vacuumCubic).coeff 1 = _
  rw [tensorRootAnnihilation_vacuumCubic]
  simp only [mul_add, HahnSeries.C_apply, HahnSeries.coeff_add,
    HahnSeries.coeff_mul_single, sub_zero]
  change (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 * vacuumCubic +
    (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 2 *
      (MvPolynomial.C (-contraction w 1 * rootWeight w beta) * vacuumCubicComplement j) = _
  rw [show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 =
      coeff 1 (tensorRootCreation w beta j) from
      HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 1,
    show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 2 =
      coeff 2 (tensorRootCreation w beta j) from
      HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 2,
    coeff_one_tensorRootCreation, coeff_two_tensorRootCreation]
  have he : degreeOneVariable j ^ 2 * vacuumCubicComplement (K := K) j =
      degreeOneVariable j * vacuumCubic := by
    rw [pow_two, mul_assoc, variable_mul_vacuumCubicComplement]
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, smul_smul, he]
  module

theorem tensorRootMode_neg_one_vacuumCubic (w : K) (beta : Lattice) :
    tensorRootMode w beta (-1) (vacuumCubic : Space K) =
      (rootWeight (w ^ (-1 : ℤ)) beta -
        6 * contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta ^ 2) •
          (diagonalCoordinate firstMode * vacuumCubic) := by
  change ((1/12:K) • ∑ j : Fin 3, tensorRootSummand w beta j vacuumCubic).coeff 1 = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_add, Fin.sum_univ_three,
    tensorRootSummand_neg_one_vacuumCubic, smul_add, smul_smul]
  simp only [diagonalCoordinate, Fin.sum_univ_three, degreeOneVariable, add_mul]
  module

theorem chevalleyF_zero_vacuumCubic (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 0 (vacuumCubic : Space K) = 0 := by
  have hs : chevalleyFCoordinates w 0 0 * (1 - 6 * contraction w 1) +
      chevalleyFCoordinates w 0 1 *
        (rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) -
          6 * contraction w 1 * rootWeight w (RootData.simpleRoot 1) *
            rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1)^2) +
      chevalleyFCoordinates w 0 2 = 0 := by
    rw [RootData.rootWeight_second, RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw (-1)]
    norm_num [chevalleyFCoordinates, Scalar.phasePolynomial, Matrix.cons_val_two, Matrix.cons_val_three]
    grind only
  have hh : heisenbergMode w (-1) (vacuumCubic : Space K) =
      diagonalCoordinate firstMode * vacuumCubic := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    rfl
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorRootMode_neg_one_vacuumCubic, RootData.rootWeight_first,
    one_pow, mul_one, hh, smul_smul]
  have hz : chevalleyFCoordinates w 0 3 = 0 := rfl
  rw [hz, zero_smul, add_zero, ← add_smul, ← add_smul, hs, zero_smul]

noncomputable def vacuumQuadratic : Space K :=
  degreeOneVariable 0 * degreeOneVariable 1 +
    degreeOneVariable 0 * degreeOneVariable 2 + degreeOneVariable 1 * degreeOneVariable 2

theorem chevalleyF_zero_vacuum (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 0 (1 : Space K) = (3*w^3-6*w+9) • diagonalCoordinate firstMode := by
  have hh : heisenbergMode w (-1) (1 : Space K) = diagonalCoordinate firstMode := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    simp
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorRootMode_neg_one_vacuum, RootData.rootWeight_first,
    one_smul, hh, smul_smul]
  have hz : chevalleyFCoordinates w 0 3 = 0 := rfl
  rw [hz, zero_smul, add_zero, ← add_smul, ← add_smul,
    (chevalleyF_zero_coefficients w hw).1]

theorem chevalleyF_zero_diagonal_first (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 0 (diagonalCoordinate firstMode : Space K) =
      (2 * (3*w^3-6*w+9)) • vacuumQuadratic := by
  have hd : (diagonalCoordinate firstMode : Space K) =
      degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2 := by
    simp [diagonalCoordinate, Fin.sum_univ_three, degreeOneVariable]
  rw [hd, map_add, map_add, chevalleyF_zero_degreeOneVariable w hw,
    chevalleyF_zero_degreeOneVariable w hw, chevalleyF_zero_degreeOneVariable w hw,
    ← smul_add, ← smul_add]
  calc
    _ = (3*w^3-6*w+9) • (2 * vacuumQuadratic) := by
      congr 1
      dsimp [vacuumQuadratic]
      ring
    _ = _ := by rw [two_mul, smul_add]; module

theorem chevalleyF_zero_vacuumQuadratic (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 0 (vacuumQuadratic : Space K) =
      (3 * (3*w^3-6*w+9)) • vacuumCubic := by
  have h01 : chevalleyF w 0 (degreeOneVariable 0 * degreeOneVariable 1) =
      (3*w^3-6*w+9) • (vacuumCubic : Space K) := by
    rw [chevalleyF_zero_degreeOneVariable_mul w hw 0 1 (by decide)]
    congr 1
    dsimp [vacuumCubic]
    ring
  have h02 : chevalleyF w 0 (degreeOneVariable 0 * degreeOneVariable 2) =
      (3*w^3-6*w+9) • (vacuumCubic : Space K) := by
    rw [chevalleyF_zero_degreeOneVariable_mul w hw 0 2 (by decide)]
    congr 1
    dsimp [vacuumCubic]
    ring
  have h12 : chevalleyF w 0 (degreeOneVariable 1 * degreeOneVariable 2) =
      (3*w^3-6*w+9) • (vacuumCubic : Space K) := by
    rw [chevalleyF_zero_degreeOneVariable_mul w hw 1 2 (by decide)]
    congr 1
    dsimp [vacuumCubic]
    ring
  rw [vacuumQuadratic, map_add, map_add, h01, h02, h12]
  module

/-- The nonzero Dynkin label three gives the exact fourth-power lowering relation. -/
theorem chevalleyF_zero_pow_four_vacuum (w : K) (hw : w^4-w^2+1=0) :
    ((chevalleyF w 0)^4) (1 : Space K) = 0 := by
  have hp (f : Module.End K (Space K)) (v : Space K) :
      (f^4) v = f (f (f (f v))) := by
    simp only [show (4 : ℕ) = 2+2 from rfl, pow_add, pow_two, Module.End.mul_apply]
  rw [hp]
  simp only [chevalleyF_zero_vacuum w hw, map_smul, chevalleyF_zero_diagonal_first w hw,
    chevalleyF_zero_vacuumQuadratic w hw, chevalleyF_zero_vacuumCubic w hw, smul_zero]

/-- All three simple-root integrability relations hold on the concrete vacuum. -/
theorem chevalleyF_vacuum_integrability (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    ((chevalleyF w i)^(if i = 0 then 4 else 1)) (1 : Space K) = 0 := by
  by_cases hi : i = 0
  · subst i
    simp only [ite_true]
    exact chevalleyF_zero_pow_four_vacuum w hw
  · rw [if_neg hi, pow_one]
    have hi12 : i = 1 ∨ i = 2 := by omega
    rcases hi12 with rfl | rfl
    · exact chevalleyF_one_vacuum w hw
    · exact chevalleyF_two_vacuum w hw

end KanadeRussell.Tsuchioka.Fock
