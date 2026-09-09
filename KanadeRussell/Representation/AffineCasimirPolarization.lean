import KanadeRussell.Representation.AffineWeightLattice

/-! Polarization and translation of the affine root Casimir. These are
integer lattice identities, without a denominator or character equation. -/
set_option autoImplicit false
namespace KanadeRussell.Representation.AffineWeightLattice
open Tsuchioka.Fock

def rootBilinear (alpha gamma : RootCoefficients) : ℤ :=
  ∑ i : Fin 3, symmetrizer i * gamma i * ∑ j : Fin 3, affineCartanMatrix i j * alpha j

theorem rootBilinear_eq (alpha gamma : RootCoefficients) :
    rootBilinear alpha gamma =
      2*alpha 0*gamma 0 + 2*alpha 1*gamma 1 + 6*alpha 2*gamma 2 -
      alpha 0*gamma 1-alpha 1*gamma 0-3*alpha 1*gamma 2-3*alpha 2*gamma 1 := by
  norm_num [rootBilinear, Fin.sum_univ_three, symmetrizer, affineCartanMatrix, Matrix.cons_val_two]
  ring

theorem rootBilinear_symmetric (alpha gamma : RootCoefficients) :
    rootBilinear alpha gamma = rootBilinear gamma alpha := by
  simp only [rootBilinear_eq]
  ring

theorem rootBilinear_add_left (alpha beta gamma : RootCoefficients) :
    rootBilinear (alpha+beta) gamma = rootBilinear alpha gamma + rootBilinear beta gamma := by
  simp only [rootBilinear_eq, Pi.add_apply]
  ring

theorem rootBilinear_add_right (alpha beta gamma : RootCoefficients) :
    rootBilinear alpha (beta+gamma) = rootBilinear alpha beta + rootBilinear alpha gamma := by
  simp only [rootBilinear_eq, Pi.add_apply]
  ring

theorem rootQuadratic_add (alpha gamma : RootCoefficients) :
    rootQuadratic (alpha+gamma) = rootQuadratic alpha + rootQuadratic gamma + rootBilinear alpha gamma := by
  simp only [rootQuadratic_eq, rootBilinear_eq, Pi.add_apply]
  ring

theorem rootBilinear_self (alpha : RootCoefficients) :
    rootBilinear alpha alpha = 2*rootQuadratic alpha := by
  rw [rootBilinear_eq, rootQuadratic_eq]
  ring

theorem casimir_add (lambda alpha gamma : RootCoefficients) :
    casimir lambda (alpha+gamma) = casimir lambda alpha + casimir lambda gamma + rootBilinear alpha gamma := by
  simp only [casimir_eq, rootBilinear_eq, Pi.add_apply]
  ring

/-- The cross term in a rho-shifted Casimir convolution is the negative
pairing of the translated highest labels with the second root occupation. -/
theorem casimir_rho_translation (lambda alpha gamma : RootCoefficients) :
    casimir (fun i => lambda i+1) (alpha+gamma) -
      casimir (fun i => lambda i+1) alpha - casimir (fun _ => 1) gamma =
      -(∑ i : Fin 3, symmetrizer i * gamma i * weightLabels lambda alpha i) := by
  norm_num [casimir_eq, Pi.add_apply, weightLabels, Fin.sum_univ_three,
    symmetrizer, affineCartanMatrix, Matrix.cons_val_two]
  ring

/-- The rho-shifted Casimir is invariant under the corresponding shifted
reflection on root occupations. -/
theorem casimir_rho_simpleReflection (lambda beta : RootCoefficients) (i : Fin 3) :
    casimir (fun j => lambda j+1) (simpleReflection (fun j => lambda j+1) i beta) =
      casimir (fun j => lambda j+1) beta :=
  casimir_simpleReflection (fun j => lambda j+1) beta i

end KanadeRussell.Representation.AffineWeightLattice
