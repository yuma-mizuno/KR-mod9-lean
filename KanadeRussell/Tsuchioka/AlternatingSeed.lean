import KanadeRussell.Tsuchioka.TensorDegreeOne

/-! The alternating degree-three polynomial in the three degree-one tensor
coordinates, and its exact single-coordinate Taylor coefficients. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KanadeRussell.Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

noncomputable def alternatingSeed : Space K :=
  (degreeOneVariable 0 - degreeOneVariable 1) *
    (degreeOneVariable 0 - degreeOneVariable 2) *
    (degreeOneVariable 1 - degreeOneVariable 2)

noncomputable def alternatingLinearCoefficient : Fin 3 → Space K :=
  ![(2 * degreeOneVariable 0 - degreeOneVariable 1 - degreeOneVariable 2) *
      (degreeOneVariable 1 - degreeOneVariable 2),
    (degreeOneVariable 0 - degreeOneVariable 2) *
      (degreeOneVariable 0 - 2 * degreeOneVariable 1 + degreeOneVariable 2),
    -(degreeOneVariable 0 - degreeOneVariable 1) *
      (degreeOneVariable 0 + degreeOneVariable 1 - 2 * degreeOneVariable 2)]

noncomputable def alternatingQuadraticCoefficient : Fin 3 → Space K :=
  ![degreeOneVariable 1 - degreeOneVariable 2,
    degreeOneVariable 2 - degreeOneVariable 0,
    degreeOneVariable 0 - degreeOneVariable 1]

theorem alternatingSeed_ne_zero : alternatingSeed (K := K) ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval fun s : Fin 3 × Mode => (s.1.val : K)) h
  norm_num [alternatingSeed, degreeOneVariable] at he

theorem alternatingSeed_grade : alternatingSeed (K := K) ∈ grade 3 := by
  have hx (a : Fin 3) : degreeOneVariable (K := K) a ∈ grade 1 :=
    MvPolynomial.isWeightedHomogeneous_X K variableWeight (a, firstMode)
  have hd (a b : Fin 3) : degreeOneVariable (K := K) a - degreeOneVariable b ∈ grade 1 :=
    (grade 1).sub_mem (hx a) (hx b)
  exact MvPolynomial.IsWeightedHomogeneous.mul
    (MvPolynomial.IsWeightedHomogeneous.mul (hd 0 1) (hd 0 2)) (hd 1 2)

theorem alternatingSeed_heisenbergVacuum (w : K) : alternatingSeed (K := K) ∈ heisenbergVacuum w := by
  rw [mem_heisenbergVacuum]
  intro n
  simp [heisenbergPositive_apply, alternatingSeed, degreeOneVariable,
    Derivation.leibniz, diagonalDerivative_X]

theorem sum_alternatingLinearCoefficient :
    ∑ j : Fin 3, alternatingLinearCoefficient (K := K) j = 0 := by
  norm_num [Fin.sum_univ_three, alternatingLinearCoefficient, Matrix.cons_val_two]
  ring

theorem sum_variable_alternatingLinearCoefficient :
    ∑ j : Fin 3, degreeOneVariable j * alternatingLinearCoefficient (K := K) j =
      3 * alternatingSeed := by
  norm_num [Fin.sum_univ_three, alternatingLinearCoefficient, alternatingSeed, Matrix.cons_val_two]
  ring

theorem sum_alternatingQuadraticCoefficient :
    ∑ j : Fin 3, alternatingQuadraticCoefficient (K := K) j = 0 := by
  norm_num [Fin.sum_univ_three, alternatingQuadraticCoefficient, Matrix.cons_val_two] <;> ring

theorem sum_variable_alternatingQuadraticCoefficient :
    ∑ j : Fin 3, degreeOneVariable j * alternatingQuadraticCoefficient (K := K) j = 0 := by
  norm_num [Fin.sum_univ_three, alternatingQuadraticCoefficient, Matrix.cons_val_two] <;> ring

theorem sum_variable_sq_alternatingQuadraticCoefficient :
    ∑ j : Fin 3, degreeOneVariable j ^ 2 * alternatingQuadraticCoefficient (K := K) j =
      alternatingSeed := by
  norm_num [Fin.sum_univ_three, alternatingQuadraticCoefficient, alternatingSeed, Matrix.cons_val_two]
  ring

end KanadeRussell.Tsuchioka.Fock
