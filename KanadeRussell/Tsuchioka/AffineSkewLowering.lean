import KanadeRussell.Tsuchioka.AffineSkewHighestWeight
import KanadeRussell.Tsuchioka.TensorAlternatingCoefficients

/-! The zero-weight Chevalley lowering relation on the degree-one skew seed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries Sectors
open RootData (Lattice rootWeight)
variable {K : Type*} [Field K] [CharZero K]

theorem tensorRootSummand_neg_one_degreeOneVariable (w : K) (beta : Lattice)
    (j a : Fin 3) :
    (tensorRootSummand w beta j (degreeOneVariable a)).coeff 1 =
      MvPolynomial.C (12 * rootWeight (w ^ (-1 : ℤ)) beta) * degreeOneVariable j * degreeOneVariable a +
      (72 * rootWeight (w ^ (-1 : ℤ)) beta ^ 2) • (degreeOneVariable j ^ 2) *
        MvPolynomial.C (if a = j then -contraction w 1 * rootWeight w beta else 0) := by
  simp only [tensorRootSummand, LinearMap.coe_mk, AddHom.coe_mk, degreeOneVariable,
    tensorRootAnnihilation, MvPolynomial.eval₂Hom_X', firstMode, mul_add, HahnSeries.C_apply,
    HahnSeries.coeff_add, HahnSeries.coeff_mul_single]
  change (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 * _ +
    (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 2 * _ = _
  rw [show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 =
      coeff 1 (tensorRootCreation w beta j) from
    HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 1,
    show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 2 =
      coeff 2 (tensorRootCreation w beta j) from
    HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 2,
    coeff_one_tensorRootCreation, coeff_two_tensorRootCreation]
  simp [degreeOneVariable, firstMode]

theorem tensorRootMode_neg_one_degreeOneVariable (w : K) (beta : Lattice) (a : Fin 3) :
    tensorRootMode w beta (-1) (degreeOneVariable a) =
      rootWeight (w ^ (-1 : ℤ)) beta •
        ((degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) * degreeOneVariable a) -
      (6 * contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta ^ 2) •
        (degreeOneVariable a ^ 2) := by
  change ((1/12:K) • ∑ j : Fin 3,
    tensorRootSummand w beta j (degreeOneVariable a)).coeff 1 = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_add,
    tensorRootSummand_neg_one_degreeOneVariable, Fin.sum_univ_three]
  fin_cases a <;> norm_num [Fin.ext_iff, MvPolynomial.C_eq_smul_one,
    smul_mul_assoc, mul_smul_comm, smul_smul, add_mul]
  all_goals
    try simp only [show degreeOneVariable (⟨2, by decide⟩ : Fin 3) =
      degreeOneVariable (K := K) (2 : Fin 3) from rfl]
    module

theorem chevalleyF_two_degreeOneVariable (w : K) (hw : w^4-w^2+1=0) (a : Fin 3) :
    chevalleyF w 2 (degreeOneVariable a) = 0 := by
  have hs : chevalleyFCoordinates w 2 0 +
      chevalleyFCoordinates w 2 1 * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) +
      chevalleyFCoordinates w 2 2 = 0 := by
    rw [RootData.rootWeight_second, Scalar.zpow_phasePolynomial w hw (-1)]
    norm_num [chevalleyFCoordinates, Scalar.phasePolynomial, Matrix.cons_val_two, Matrix.cons_val_three]
    grind only
  have hq : chevalleyFCoordinates w 2 0 * (6 * contraction w 1) +
      chevalleyFCoordinates w 2 1 * (6 * contraction w 1 *
        rootWeight w (RootData.simpleRoot 1) * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 2) = 0 := by
    rw [RootData.rootWeight_second, RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw (-1)]
    norm_num [chevalleyFCoordinates, Scalar.phasePolynomial, Matrix.cons_val_two, Matrix.cons_val_three]
    grind only
  have hh : heisenbergMode w (-1) (degreeOneVariable a) =
      (degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) * degreeOneVariable a := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    simp [heisenbergNegative_apply, diagonalCoordinate, Fin.sum_univ_three, degreeOneVariable]
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorRootMode_neg_one_degreeOneVariable, RootData.rootWeight_first,
    one_smul, one_pow, mul_one, hh, smul_sub, smul_smul]
  have hzero : chevalleyFCoordinates w 2 3 = 0 := rfl
  rw [hzero, zero_smul, add_zero]
  have he : chevalleyFCoordinates w 2 0 •
      ((degreeOneVariable (K := K) 0 + degreeOneVariable (K := K) 1 + degreeOneVariable (K := K) 2) * degreeOneVariable (K := K) a) -
      (chevalleyFCoordinates w 2 0 * (6 * contraction w 1)) • (degreeOneVariable (K := K) a ^ 2) +
      ((chevalleyFCoordinates w 2 1 * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1)) •
        ((degreeOneVariable (K := K) 0 + degreeOneVariable (K := K) 1 + degreeOneVariable (K := K) 2) * degreeOneVariable (K := K) a) -
       (chevalleyFCoordinates w 2 1 * (6 * contraction w 1 * rootWeight w (RootData.simpleRoot 1) *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 2)) • (degreeOneVariable (K := K) a ^ 2)) +
      chevalleyFCoordinates w 2 2 •
        ((degreeOneVariable (K := K) 0 + degreeOneVariable (K := K) 1 + degreeOneVariable (K := K) 2) * degreeOneVariable (K := K) a) =
      (chevalleyFCoordinates w 2 0 + chevalleyFCoordinates w 2 1 *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) + chevalleyFCoordinates w 2 2) •
        ((degreeOneVariable (K := K) 0 + degreeOneVariable (K := K) 1 + degreeOneVariable (K := K) 2) * degreeOneVariable (K := K) a) -
      (chevalleyFCoordinates w 2 0 * (6 * contraction w 1) + chevalleyFCoordinates w 2 1 *
        (6 * contraction w 1 * rootWeight w (RootData.simpleRoot 1) *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 2)) • (degreeOneVariable (K := K) a ^ 2) := by module
  rw [he, hs, hq]
  simp

/-- The zero Dynkin label at node two gives the concrete skew lowering relation. -/
theorem chevalleyF_two_skewSeed (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 2 (skewSeed (K := K)) = 0 := by
  rw [skewSeed, map_sub, chevalleyF_two_degreeOneVariable w hw,
    chevalleyF_two_degreeOneVariable w hw, sub_self]

theorem tensorRootSummand_neg_one_degreeOneVariable_mul (w : K) (beta : Lattice)
    (j a b : Fin 3) (hab : a ≠ b) :
    (tensorRootSummand w beta j (degreeOneVariable a * degreeOneVariable b)).coeff 1 =
      (12 * rootWeight (w ^ (-1 : ℤ)) beta) •
        (degreeOneVariable j * (degreeOneVariable a * degreeOneVariable b)) +
      (-72 * contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta ^ 2) •
        ((degreeOneVariable j ^ 2) *
          ((if a = j then degreeOneVariable b else 0) + (if b = j then degreeOneVariable a else 0))) := by
  have hx (a : Fin 3) : tensorRootAnnihilation w beta j (degreeOneVariable a) =
      HahnSeries.C (degreeOneVariable a) +
        (if a = j then HahnSeries.single (-1 : ℤ)
          (MvPolynomial.C (-contraction w 1 * rootWeight w beta)) else 0) := by
    by_cases ha : a = j <;> simp [tensorRootAnnihilation, degreeOneVariable, firstMode, ha]
  have hp : tensorRootAnnihilation w beta j (degreeOneVariable a * degreeOneVariable b) =
      HahnSeries.C (degreeOneVariable a * degreeOneVariable b) +
      HahnSeries.single (-1 : ℤ) (MvPolynomial.C (-contraction w 1 * rootWeight w beta) *
        ((if a = j then degreeOneVariable b else 0) + (if b = j then degreeOneVariable a else 0))) := by
    rw [map_mul, hx, hx]
    by_cases ha : a = j
    · have hb : b ≠ j := by intro hb; exact hab (ha.trans hb.symm)
      simp only [ha, if_true, if_neg hb, add_zero, add_mul, ← map_mul,
        HahnSeries.C_apply, HahnSeries.single_mul_single]
    · by_cases hb : b = j
      · simp only [hb, if_true, if_neg ha, zero_add, add_zero, mul_add, ← map_mul,
          HahnSeries.C_apply, HahnSeries.single_mul_single]
        congr 2 <;> ring
      · simp only [if_neg ha, if_neg hb, add_zero, zero_add, mul_zero, map_zero, map_mul]
  change ((tensorRootCreation w beta j : LaurentSeries (Space K)) * _).coeff 1 = _
  rw [hp]
  rw [mul_add, HahnSeries.coeff_add]
  simp only [HahnSeries.C_apply, HahnSeries.coeff_mul_single]
  change (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 * _ +
    (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 2 * _ = _
  rw [show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 =
      coeff 1 (tensorRootCreation w beta j) from
    HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 1,
    show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 2 =
      coeff 2 (tensorRootCreation w beta j) from
    HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 2,
    coeff_one_tensorRootCreation, coeff_two_tensorRootCreation]
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, smul_smul]
  module

theorem tensorRootMode_neg_one_degreeOneVariable_mul (w : K) (beta : Lattice)
    (a b : Fin 3) (hab : a ≠ b) :
    tensorRootMode w beta (-1) (degreeOneVariable a * degreeOneVariable b) =
      rootWeight (w ^ (-1 : ℤ)) beta •
        ((degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) *
          (degreeOneVariable a * degreeOneVariable b)) -
      (6 * contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta ^ 2) •
        (degreeOneVariable a ^ 2 * degreeOneVariable b + degreeOneVariable b ^ 2 * degreeOneVariable a) := by
  change ((1/12:K) • ∑ j : Fin 3,
    tensorRootSummand w beta j (degreeOneVariable a * degreeOneVariable b)).coeff 1 = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_add,
    tensorRootSummand_neg_one_degreeOneVariable_mul w beta _ a b hab, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> try exact (hab rfl).elim
  all_goals
    norm_num [Fin.ext_iff, add_mul]
    try simp only [show degreeOneVariable (⟨2, by decide⟩ : Fin 3) =
      degreeOneVariable (K := K) (2 : Fin 3) from rfl]
    module

theorem chevalleyF_zero_coefficients (w : K) (hw : w^4-w^2+1=0) :
    (chevalleyFCoordinates w 0 0 +
      chevalleyFCoordinates w 0 1 * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) +
      chevalleyFCoordinates w 0 2 = 3*w^3-6*w+9) ∧
    (chevalleyFCoordinates w 0 0 * (6 * contraction w 1) +
      chevalleyFCoordinates w 0 1 * (6 * contraction w 1 *
        rootWeight w (RootData.simpleRoot 1) * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 2) = 3*w^3-6*w+9) := by
  simp only [RootData.rootWeight_second, contraction_one w hw, Scalar.zpow_phasePolynomial w hw (-1)]
  norm_num [chevalleyFCoordinates, Scalar.phasePolynomial, Matrix.cons_val_two, Matrix.cons_val_three]
  constructor <;> grind only

theorem chevalleyF_zero_degreeOneVariable (w : K) (hw : w^4-w^2+1=0) (a : Fin 3) :
    chevalleyF w 0 (degreeOneVariable a) = (3*w^3-6*w+9) •
      ((degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) * (degreeOneVariable a) - (degreeOneVariable a ^ 2)) := by
  obtain ⟨hs,hq⟩ := chevalleyF_zero_coefficients w hw
  have hh : heisenbergMode w (-1) (degreeOneVariable a) =
      (degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) * (degreeOneVariable a) := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    simp [heisenbergNegative_apply, diagonalCoordinate, Fin.sum_univ_three, degreeOneVariable]
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorRootMode_neg_one_degreeOneVariable, RootData.rootWeight_first,
    one_smul, one_pow, mul_one, hh, smul_sub, smul_smul]
  have hzero : chevalleyFCoordinates w 0 3 = 0 := rfl
  rw [hzero, zero_smul, add_zero]
  calc
    _ = (chevalleyFCoordinates w 0 0 + chevalleyFCoordinates w 0 1 *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) + chevalleyFCoordinates w 0 2) •
        ((degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) * (degreeOneVariable a)) -
      (chevalleyFCoordinates w 0 0 * (6 * contraction w 1) + chevalleyFCoordinates w 0 1 *
        (6 * contraction w 1 * rootWeight w (RootData.simpleRoot 1) *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 2)) • (degreeOneVariable a ^ 2) := by module
    _ = _ := by rw [hs,hq]

theorem chevalleyF_zero_degreeOneVariable_mul (w : K) (hw : w^4-w^2+1=0) (a b : Fin 3) (hab : a ≠ b) :
    chevalleyF w 0 (degreeOneVariable a * degreeOneVariable b) = (3*w^3-6*w+9) •
      ((degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) * (degreeOneVariable a * degreeOneVariable b) - (degreeOneVariable a ^ 2 * degreeOneVariable b + degreeOneVariable b ^ 2 * degreeOneVariable a)) := by
  obtain ⟨hs,hq⟩ := chevalleyF_zero_coefficients w hw
  have hh : heisenbergMode w (-1) (degreeOneVariable a * degreeOneVariable b) =
      (degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) * (degreeOneVariable a * degreeOneVariable b) := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    simp [heisenbergNegative_apply, diagonalCoordinate, Fin.sum_univ_three, degreeOneVariable]
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorRootMode_neg_one_degreeOneVariable_mul w _ a b hab, RootData.rootWeight_first,
    one_smul, one_pow, mul_one, hh, smul_sub, smul_smul]
  have hzero : chevalleyFCoordinates w 0 3 = 0 := rfl
  rw [hzero, zero_smul, add_zero]
  calc
    _ = (chevalleyFCoordinates w 0 0 + chevalleyFCoordinates w 0 1 *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) + chevalleyFCoordinates w 0 2) •
        ((degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) * (degreeOneVariable a * degreeOneVariable b)) -
      (chevalleyFCoordinates w 0 0 * (6 * contraction w 1) + chevalleyFCoordinates w 0 1 *
        (6 * contraction w 1 * rootWeight w (RootData.simpleRoot 1) *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 2)) • (degreeOneVariable a ^ 2 * degreeOneVariable b + degreeOneVariable b ^ 2 * degreeOneVariable a) := by module
    _ = _ := by rw [hs,hq]

/-- The degree-one skew seed has a length-two node-zero lowering string. -/
theorem chevalleyF_zero_sq_skewSeed (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 0 (chevalleyF w 0 (skewSeed (K := K))) = 0 := by
  have hf : chevalleyF w 0 (skewSeed (K := K)) =
      (3*w^3-6*w+9) •
        (degreeOneVariable 0 * degreeOneVariable 2 - degreeOneVariable 1 * degreeOneVariable 2) := by
    rw [skewSeed, map_sub, chevalleyF_zero_degreeOneVariable w hw,
      chevalleyF_zero_degreeOneVariable w hw, ← smul_sub]
    congr 1
    ring
  have h02 : chevalleyF w 0 (degreeOneVariable 0 * degreeOneVariable 2) =
      (3*w^3-6*w+9) • (degreeOneVariable 0 * degreeOneVariable 1 * degreeOneVariable 2) := by
    rw [chevalleyF_zero_degreeOneVariable_mul w hw 0 2 (by decide)]
    congr 1
    ring
  have h12 : chevalleyF w 0 (degreeOneVariable 1 * degreeOneVariable 2) =
      (3*w^3-6*w+9) • (degreeOneVariable 0 * degreeOneVariable 1 * degreeOneVariable 2) := by
    rw [chevalleyF_zero_degreeOneVariable_mul w hw 1 2 (by decide)]
    congr 1
    ring
  rw [hf, map_smul, map_sub, h02, h12, sub_self, smul_zero]

end KanadeRussell.Tsuchioka.Fock
