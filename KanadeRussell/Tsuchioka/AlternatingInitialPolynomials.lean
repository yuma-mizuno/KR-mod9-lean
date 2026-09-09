import KanadeRussell.Tsuchioka.LowCreationCoefficients
import KanadeRussell.Tsuchioka.AlternatingSeed

/-! Polynomial cancellations for the first two Z creation modes on the
alternating seed. All coefficients are checked exactly in the polynomial ring. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

noncomputable def relativeQuadratic : Space K :=
  degreeOneVariable 0 ^ 2 + degreeOneVariable 1 ^ 2 + degreeOneVariable 2 ^ 2 -
    degreeOneVariable 0 * degreeOneVariable 1 - degreeOneVariable 0 * degreeOneVariable 2 -
    degreeOneVariable 1 * degreeOneVariable 2

theorem sum_degreeOneCreation : ∑ j : Fin 3, degreeOneCreation (K := K) j = 0 := by
  norm_num [degreeOneCreation, Fin.sum_univ_three, tensorExponent, map_ofNat]
  ring

theorem sum_creation_sq_alternatingLinearCoefficient :
    ∑ j : Fin 3, degreeOneCreation j ^ 2 * alternatingLinearCoefficient (K := K) j = 0 := by
  norm_num [degreeOneCreation, alternatingLinearCoefficient, Fin.sum_univ_three,
    tensorExponent, Matrix.cons_val_two, map_ofNat]
  ring

theorem sum_creation_cube_alternatingQuadraticCoefficient :
    ∑ j : Fin 3, degreeOneCreation j ^ 3 * alternatingQuadraticCoefficient (K := K) j = 0 := by
  norm_num [degreeOneCreation, alternatingQuadraticCoefficient, Fin.sum_univ_three,
    tensorExponent, Matrix.cons_val_two, map_ofNat]
  ring

theorem sum_creation_sq_alternatingSeed :
    ∑ j : Fin 3, degreeOneCreation j ^ 2 * alternatingSeed (K := K) =
      96 * (alternatingSeed * relativeQuadratic) := by
  norm_num [degreeOneCreation, alternatingSeed, relativeQuadratic, Fin.sum_univ_three,
    tensorExponent, map_ofNat]
  ring

theorem sum_creation_cube_alternatingLinearCoefficient :
    ∑ j : Fin 3, degreeOneCreation j ^ 3 * alternatingLinearCoefficient (K := K) j =
      1728 * (alternatingSeed * relativeQuadratic) := by
  norm_num [degreeOneCreation, alternatingLinearCoefficient, alternatingSeed, relativeQuadratic,
    Fin.sum_univ_three, tensorExponent, Matrix.cons_val_two, map_ofNat]
  ring

theorem sum_creation_four_alternatingQuadraticCoefficient :
    ∑ j : Fin 3, degreeOneCreation j ^ 4 * alternatingQuadraticCoefficient (K := K) j =
      6912 * (alternatingSeed * relativeQuadratic) := by
  norm_num [degreeOneCreation, alternatingQuadraticCoefficient, alternatingSeed, relativeQuadratic,
    Fin.sum_univ_three, tensorExponent, Matrix.cons_val_two, map_ofNat]
  ring

end KanadeRussell.Tsuchioka.Fock
