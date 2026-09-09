import KanadeRussell.Tsuchioka.TensorVacuumWeights

/-! The tensor root zero modes act diagonally on every degree-one variable.
Their degree-one modes have the same value on each tensor factor, so they
annihilate differences of two such variables. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries
open RootData (Lattice rootWeight)
variable {K : Type*} [Field K] [CharZero K]

theorem coeff_one_tensorRootCreation (w : K) (beta : Lattice) (j : Fin 3) :
    coeff 1 (tensorRootCreation w beta j) =
      MvPolynomial.C (12 * rootWeight (w ^ (-1 : ℤ)) beta) * degreeOneVariable j := by
  rw [tensorRootCreation, FormalSeries.coeff_one_exponential
    (constantCoeff_tensorRootCreationLog w beta j)]
  simp [tensorRootCreationLog, IsMode, degreeOneVariable, firstMode]
  rfl

theorem tensorRootSummand_zero_degreeOneVariable (w : K) (beta : Lattice)
    (j a : Fin 3) :
    (tensorRootSummand w beta j (degreeOneVariable a)).coeff 0 =
      degreeOneVariable a +
        MvPolynomial.C (12 * rootWeight (w ^ (-1 : ℤ)) beta) * degreeOneVariable j *
          MvPolynomial.C (if a = j then -contraction w 1 * rootWeight w beta else 0) := by
  simp only [tensorRootSummand, LinearMap.coe_mk, AddHom.coe_mk, degreeOneVariable,
    tensorRootAnnihilation, MvPolynomial.eval₂Hom_X', firstMode, mul_add, HahnSeries.C_apply,
    HahnSeries.coeff_add, HahnSeries.coeff_mul_single]
  change (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 0 * _ +
    (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 * _ = _
  rw [show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 0 = 1 from by
    exact (HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 0).trans
      (by simpa only [coeff_zero_eq_constantCoeff, tensorRootCreation] using
        FormalSeries.constantCoeff_exponential (constantCoeff_tensorRootCreationLog w beta j))]
  rw [show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 1 =
      coeff 1 (tensorRootCreation w beta j) from
    HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 1,
    coeff_one_tensorRootCreation]
  simp [degreeOneVariable, firstMode]

theorem tensorRootMode_zero_degreeOneVariable (w : K) (beta : Lattice) (a : Fin 3) :
    tensorRootMode w beta 0 (degreeOneVariable a) =
      (1/4 - contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta) •
        degreeOneVariable a := by
  change ((1/12:K) • ∑ j : Fin 3,
    tensorRootSummand w beta j (degreeOneVariable a)).coeff 0 = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_add,
    tensorRootSummand_zero_degreeOneVariable, Fin.sum_univ_three]
  fin_cases a <;>
    norm_num [Fin.ext_iff, MvPolynomial.C_eq_smul_one, smul_smul]
  all_goals
    try simp only [show degreeOneVariable (⟨2, by decide⟩ : Fin 3) =
      degreeOneVariable (K := K) (2 : Fin 3) from rfl]
    module

theorem tensorRootSummand_one_degreeOneVariable (w : K) (beta : Lattice)
    (j a : Fin 3) :
    (tensorRootSummand w beta j (degreeOneVariable a)).coeff (-1) =
      MvPolynomial.C (if a = j then -contraction w 1 * rootWeight w beta else 0) := by
  simp only [tensorRootSummand, LinearMap.coe_mk, AddHom.coe_mk, degreeOneVariable,
    tensorRootAnnihilation, MvPolynomial.eval₂Hom_X', firstMode, mul_add, HahnSeries.C_apply,
    HahnSeries.coeff_add, HahnSeries.coeff_mul_single]
  change (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff (-1) * _ +
    (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 0 * _ = _
  rw [show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff (-1) = 0 from by
    simp [PowerSeries.coeff_coe]]
  rw [show (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 0 = 1 from by
    exact (HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 0).trans
      (by simpa only [coeff_zero_eq_constantCoeff, tensorRootCreation] using
        FormalSeries.constantCoeff_exponential (constantCoeff_tensorRootCreationLog w beta j))]
  simp

theorem tensorRootMode_one_degreeOneVariable (w : K) (beta : Lattice) (a : Fin 3) :
    tensorRootMode w beta 1 (degreeOneVariable a) =
      MvPolynomial.C (-contraction w 1 * rootWeight w beta / 12) := by
  change ((1/12:K) • ∑ j : Fin 3,
    tensorRootSummand w beta j (degreeOneVariable a)).coeff (-1) = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_add,
    tensorRootSummand_one_degreeOneVariable, Fin.sum_univ_three]
  fin_cases a <;>
    norm_num [Fin.ext_iff, MvPolynomial.C_eq_smul_one, smul_smul] <;> module

end KanadeRussell.Tsuchioka.Fock
