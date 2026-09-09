import KanadeRussell.Tsuchioka.Fock

/-! The first four creation coefficients, obtained from the actual creation
logarithm and the formal exponential differential equation. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries
variable {K : Type*} [Field K] [CharZero K]

noncomputable def degreeOneCreation (j : Fin 3) : Space K :=
  ∑ i : Fin 3, MvPolynomial.C (-4 * tensorExponent i j) * degreeOneVariable i

theorem coeff_one_creationLog (j : Fin 3) :
    coeff 1 (creationLog (K := K) j) = degreeOneCreation j := by
  simpa only [degreeOneCreation, creation, FormalSeries.coeff_one_exponential (constantCoeff_creationLog j)] using
    coeff_one_creation (K := K) j

theorem coeff_one_creation_linear (j : Fin 3) :
    coeff 1 (creation (K := K) j) = degreeOneCreation j := coeff_one_creation j

theorem coeff_two_creation_linear (j : Fin 3) :
    coeff 2 (creation (K := K) j) = (1/2 : K) • (degreeOneCreation j)^2 := by
  rw [coeff_two_creation, IsScalarTower.algebraMap_apply ℚ K (Space K), MvPolynomial.algebraMap_eq]
  norm_num only [map_div₀, map_one, map_ofNat]
  exact MvPolynomial.C_mul'

theorem creation_coefficient_recursion_two (j : Fin 3) :
    (3 : K) • coeff 3 (creation (K := K) j) = coeff 2 (creation j) * degreeOneCreation j := by
  have h := congrArg (coeff 2) (FormalSeries.derivative_exponential (constantCoeff_creationLog (K := K) j))
  have ha : Finset.antidiagonal 2 = {(0,2),(1,1),(2,0)} := rfl
  have hz2 : coeff 2 (creationLog (K := K) j) = 0 := by simp [creationLog, IsMode]
  have hz3 : coeff 3 (creationLog (K := K) j) = 0 := by simp [creationLog, IsMode]
  change coeff 2 (derivative (Space K) (creation j)) =
    coeff 2 (creation j * derivative (Space K) (creationLog j)) at h
  rw [coeff_derivative, coeff_mul] at h
  norm_num [ha, Finset.sum_insert, Finset.sum_singleton, Prod.fst, Prod.snd,
    coeff_derivative, hz2, hz3, coeff_one_creationLog, Nat.reduceAdd,
    zero_mul, mul_zero, add_zero, zero_add, mul_one] at h
  convert h using 1
  norm_num [Algebra.smul_def, map_ofNat]
  ring

theorem coeff_three_creation_linear (j : Fin 3) :
    coeff 3 (creation (K := K) j) = (1/6 : K) • (degreeOneCreation j)^3 := by
  have h := congrArg (fun p : Space K => (1/3 : K) • p) (creation_coefficient_recursion_two (K := K) j)
  rw [coeff_two_creation_linear] at h
  norm_num [smul_smul, smul_mul_assoc] at h
  rw [h]
  congr 1 <;> ring

theorem creation_coefficient_recursion_three (j : Fin 3) :
    (4 : K) • coeff 4 (creation (K := K) j) = coeff 3 (creation j) * degreeOneCreation j := by
  have h := congrArg (coeff 3) (FormalSeries.derivative_exponential (constantCoeff_creationLog (K := K) j))
  have ha : Finset.antidiagonal 3 = {(0,3),(1,2),(2,1),(3,0)} := rfl
  have hz2 : coeff 2 (creationLog (K := K) j) = 0 := by simp [creationLog, IsMode]
  have hz3 : coeff 3 (creationLog (K := K) j) = 0 := by simp [creationLog, IsMode]
  have hz4 : coeff 4 (creationLog (K := K) j) = 0 := by simp [creationLog, IsMode]
  change coeff 3 (derivative (Space K) (creation j)) =
    coeff 3 (creation j * derivative (Space K) (creationLog j)) at h
  rw [coeff_derivative, coeff_mul] at h
  norm_num [ha, Finset.sum_insert, Finset.sum_singleton, Prod.fst, Prod.snd,
    coeff_derivative, hz2, hz3, hz4, coeff_one_creationLog, Nat.reduceAdd,
    zero_mul, mul_zero, add_zero, zero_add, mul_one] at h
  convert h using 1
  norm_num [Algebra.smul_def, map_ofNat]
  ring

theorem coeff_four_creation_linear (j : Fin 3) :
    coeff 4 (creation (K := K) j) = (1/24 : K) • (degreeOneCreation j)^4 := by
  have h := congrArg (fun p : Space K => (1/4 : K) • p) (creation_coefficient_recursion_three (K := K) j)
  rw [coeff_three_creation_linear] at h
  norm_num [smul_smul, smul_mul_assoc] at h
  rw [h]
  congr 1 <;> ring

end KanadeRussell.Tsuchioka.Fock
