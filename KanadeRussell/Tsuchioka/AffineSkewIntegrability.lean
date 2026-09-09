import KanadeRussell.Tsuchioka.AffineSkewLowering
import KanadeRussell.Tsuchioka.TensorThirdCoefficient

/-! The remaining node-one length-two lowering string for the skew seed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries Sectors
open RootData (Lattice rootWeight)
variable {K : Type*} [Field K] [CharZero K]

theorem tensorRootAnnihilation_degreeOneVariable_sq (w : K) (beta : Lattice)
    (j a : Fin 3) :
    tensorRootAnnihilation w beta j (degreeOneVariable a ^ 2) =
      HahnSeries.C (degreeOneVariable a ^ 2) +
      HahnSeries.single (-1 : ℤ) (2 * MvPolynomial.C
        (if a = j then -contraction w 1 * rootWeight w beta else 0) * degreeOneVariable a) +
      HahnSeries.single (-2 : ℤ) (MvPolynomial.C
        ((if a = j then -contraction w 1 * rootWeight w beta else 0) ^ 2)) := by
  have hx : tensorRootAnnihilation w beta j (degreeOneVariable a) =
      HahnSeries.C (degreeOneVariable a) + HahnSeries.single (-1 : ℤ)
        (MvPolynomial.C (if a = j then -contraction w 1 * rootWeight w beta else 0)) := by
    simp [tensorRootAnnihilation, degreeOneVariable, firstMode]
  rw [map_pow, hx]
  simp only [pow_two, two_mul, add_mul, mul_add, map_add, map_mul,
    HahnSeries.C_apply, HahnSeries.single_mul_single]
  norm_num only [Int.reduceAdd]
  apply HahnSeries.ext
  funext n
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_single]
  split_ifs <;> ring

theorem tensorRootSummand_neg_one_degreeOneVariable_sq (w : K) (beta : Lattice)
    (j a : Fin 3) :
    (tensorRootSummand w beta j (degreeOneVariable a ^ 2)).coeff 1 =
      (12 * rootWeight (w ^ (-1 : ℤ)) beta) • (degreeOneVariable j * degreeOneVariable a ^ 2) +
      (144 * rootWeight (w ^ (-1 : ℤ)) beta ^ 2 *
        (if a = j then -contraction w 1 * rootWeight w beta else 0)) •
        (degreeOneVariable j ^ 2 * degreeOneVariable a) +
      (288 * rootWeight (w ^ (-1 : ℤ)) beta ^ 3 *
        (if a = j then -contraction w 1 * rootWeight w beta else 0) ^ 2) •
        (degreeOneVariable j ^ 3) := by
  change ((tensorRootCreation w beta j : LaurentSeries (Space K)) * _).coeff 1 = _
  rw [tensorRootAnnihilation_degreeOneVariable_sq]
  simp only [mul_add, HahnSeries.C_apply, HahnSeries.coeff_add, HahnSeries.coeff_mul_single]
  change (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 * _ +
    (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 2 * _ +
    (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 3 * _ = _
  rw [show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 =
      coeff 1 (tensorRootCreation w beta j) from
    HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 1,
    show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 2 =
      coeff 2 (tensorRootCreation w beta j) from
    HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 2,
    show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 3 =
      coeff 3 (tensorRootCreation w beta j) from
    HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 3,
    coeff_one_tensorRootCreation, coeff_two_tensorRootCreation, coeff_three_tensorRootCreation]
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, smul_smul]
  simp only [show (2 : Space K) = (2 : K) • (1 : Space K) from by simp [Algebra.smul_def, map_ofNat]]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  module

theorem tensorRootMode_neg_one_degreeOneVariable_sq (w : K) (beta : Lattice) (a : Fin 3) :
    tensorRootMode w beta (-1) (degreeOneVariable a ^ 2) =
      rootWeight (w ^ (-1 : ℤ)) beta •
        ((degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) * degreeOneVariable a ^ 2) +
      (-12 * contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta ^ 2 +
        24 * (contraction w 1 * rootWeight w beta) ^ 2 * rootWeight (w ^ (-1 : ℤ)) beta ^ 3) •
        (degreeOneVariable a ^ 3) := by
  change ((1/12:K) • ∑ j : Fin 3,
    tensorRootSummand w beta j (degreeOneVariable a ^ 2)).coeff 1 = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_add,
    tensorRootSummand_neg_one_degreeOneVariable_sq, Fin.sum_univ_three]
  fin_cases a <;> norm_num [Fin.ext_iff, add_mul]
  all_goals
    try simp only [show degreeOneVariable (⟨2, by decide⟩ : Fin 3) =
      degreeOneVariable (K := K) (2 : Fin 3) from rfl]
    simp only [← pow_succ]
    module

theorem chevalleyF_one_coefficients (w : K) (hw : w^4-w^2+1=0) :
    (chevalleyFCoordinates w 1 0 +
      chevalleyFCoordinates w 1 1 * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) +
      chevalleyFCoordinates w 1 2 = 0) ∧
    (-(chevalleyFCoordinates w 1 0 * (6 * contraction w 1) +
      chevalleyFCoordinates w 1 1 * (6 * contraction w 1 *
        rootWeight w (RootData.simpleRoot 1) * rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 2)) = 3*w^3-6*w+9) ∧
    (chevalleyFCoordinates w 1 0 * (-12 * contraction w 1 + 24 * contraction w 1 ^ 2) +
      chevalleyFCoordinates w 1 1 * (-12 * contraction w 1 * rootWeight w (RootData.simpleRoot 1) *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 2 +
        24 * (contraction w 1 * rootWeight w (RootData.simpleRoot 1)) ^ 2 *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 3) = 0) := by
  simp only [RootData.rootWeight_second, contraction_one w hw, Scalar.zpow_phasePolynomial w hw (-1)]
  norm_num [chevalleyFCoordinates, Scalar.phasePolynomial, Matrix.cons_val_two, Matrix.cons_val_three]
  constructor
  · grind only
  constructor <;> grind only

theorem chevalleyF_one_degreeOneVariable (w : K) (hw : w^4-w^2+1=0) (a : Fin 3) :
    chevalleyF w 1 (degreeOneVariable a) = (3*w^3-6*w+9) • degreeOneVariable a ^ 2 := by
  obtain ⟨hs,hq,hc⟩ := chevalleyF_one_coefficients w hw
  have hh : heisenbergMode w (-1) (degreeOneVariable a) =
      (degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) * degreeOneVariable a := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    simp [heisenbergNegative_apply, diagonalCoordinate, Fin.sum_univ_three, degreeOneVariable]
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorRootMode_neg_one_degreeOneVariable, RootData.rootWeight_first,
    one_smul, one_pow, mul_one, hh, smul_sub, smul_smul]
  have hzero : chevalleyFCoordinates w 1 3 = 0 := rfl
  rw [hzero, zero_smul, add_zero]
  calc
    _ = (chevalleyFCoordinates w 1 0 + chevalleyFCoordinates w 1 1 *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) + chevalleyFCoordinates w 1 2) •
        ((degreeOneVariable 0 + degreeOneVariable 1 + degreeOneVariable 2) * degreeOneVariable a) +
      (-(chevalleyFCoordinates w 1 0 * (6 * contraction w 1) + chevalleyFCoordinates w 1 1 *
        (6 * contraction w 1 * rootWeight w (RootData.simpleRoot 1) *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 2))) • degreeOneVariable a ^ 2 := by module
    _ = _ := by rw [hs,hq,zero_smul,zero_add]

theorem chevalleyF_one_degreeOneVariable_sq (w : K) (hw : w^4-w^2+1=0) (a : Fin 3) :
    chevalleyF w 1 (degreeOneVariable (K := K) a ^ 2) = 0 := by
  obtain ⟨hs,hq,hc⟩ := chevalleyF_one_coefficients w hw
  have hh : heisenbergMode w (-1) (degreeOneVariable (K := K) a ^ 2) =
      (degreeOneVariable (K := K) 0 + degreeOneVariable (K := K) 1 + degreeOneVariable (K := K) 2) * degreeOneVariable (K := K) a ^ 2 := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    simp [heisenbergNegative_apply, diagonalCoordinate, Fin.sum_univ_three, degreeOneVariable]
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorRootMode_neg_one_degreeOneVariable_sq, RootData.rootWeight_first,
    one_smul, one_pow, mul_one, hh, smul_add, smul_smul]
  have hzero : chevalleyFCoordinates w 1 3 = 0 := rfl
  rw [hzero, zero_smul, add_zero]
  calc
    _ = (chevalleyFCoordinates w 1 0 + chevalleyFCoordinates w 1 1 *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) + chevalleyFCoordinates w 1 2) •
        ((degreeOneVariable (K := K) 0 + degreeOneVariable (K := K) 1 + degreeOneVariable (K := K) 2) * degreeOneVariable (K := K) a ^ 2) +
      (chevalleyFCoordinates w 1 0 * (-12 * contraction w 1 + 24 * contraction w 1 ^ 2) +
       chevalleyFCoordinates w 1 1 * (-12 * contraction w 1 * rootWeight w (RootData.simpleRoot 1) *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 2 +
        24 * (contraction w 1 * rootWeight w (RootData.simpleRoot 1)) ^ 2 *
        rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) ^ 3)) • degreeOneVariable (K := K) a ^ 3 := by
      module
    _ = 0 := by rw [hs,hc]; simp

/-- The node-one lowering string on the skew seed has length two. -/
theorem chevalleyF_one_sq_skewSeed (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 1 (chevalleyF w 1 (skewSeed (K := K))) = 0 := by
  rw [skewSeed, map_sub, chevalleyF_one_degreeOneVariable w hw,
    chevalleyF_one_degreeOneVariable w hw, map_sub, map_smul, map_smul,
    chevalleyF_one_degreeOneVariable_sq w hw, chevalleyF_one_degreeOneVariable_sq w hw]
  simp

/-- All three simple-root integrability equations for the weight (1,1,0) seed. -/
theorem chevalleyF_skewSeed_integrability (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    ((chevalleyF w i)^(if i = 2 then 1 else 2)) (skewSeed (K := K)) = 0 := by
  by_cases hi : i = 2
  · subst i
    simp only [ite_true, pow_one]
    exact chevalleyF_two_skewSeed w hw
  · rw [if_neg hi, pow_two, Module.End.mul_apply]
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · exact chevalleyF_zero_sq_skewSeed w hw
    · exact chevalleyF_one_sq_skewSeed w hw

end KanadeRussell.Tsuchioka.Fock
