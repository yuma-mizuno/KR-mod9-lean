import KanadeRussell.Representation.RootReflectionConvolution
import KanadeRussell.Representation.PrincipalRootDenominatorAntisymmetry
import KanadeRussell.Representation.ConcreteHighestWeight

/-! Shifted antisymmetry of the actual root-character numerator, from actual
Weyl symmetry and the proved root Euler denominator reflection identity. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

namespace PrincipalHighestWeightModule

/-- The actual numerator has shifted Weyl antisymmetry on the entire integer root lattice. -/
theorem rootNumerator_antisymmetric (M : PrincipalHighestWeightModule K V)
    (i : Fin 3) (beta : RootCoefficients) :
    rootCoefficient (M.rootCharacter * principalRootEulerDenominator)
      (simpleReflection (fun j => M.highestWeightLabels j+1) i beta) =
      -rootCoefficient (M.rootCharacter * principalRootEulerDenominator) beta := by
  have h := rootFunctionConvolution_antisymmetric M.highestWeightLabels (fun _ => 1) i
    (rootCoefficient M.rootCharacter) (rootCoefficient (principalRootEulerDenominator (K := K)))
    (fun alpha => by simpa only [rootCoefficient_rootCharacter] using M.rootMultiplicity_simpleReflection i alpha)
    (rootCoefficient_principalRootEulerDenominator_reflection (K := K) i) beta
  have hadd : M.highestWeightLabels+(fun _ => 1) = (fun j => M.highestWeightLabels j+1) := rfl
  rw [hadd] at h
  simpa only [rootCoefficient_mul, rootFunctionConvolution] using h
@[simp] theorem rootNumerator_constantCoeff (M : PrincipalHighestWeightModule K V) :
    MvPowerSeries.constantCoeff (M.rootCharacter * principalRootEulerDenominator) = 1 := by
  simp

@[simp] theorem rootNumerator_zero (M : PrincipalHighestWeightModule K V) :
    rootCoefficient (M.rootCharacter * principalRootEulerDenominator) 0 = 1 := by
  change rootCoefficient _ (rootCoefficientsOfExponent 0) = _
  rw [rootCoefficient_ofExponent, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    M.rootNumerator_constantCoeff]

omit [CharZero K] in
theorem rootNumerator_support (M : PrincipalHighestWeightModule K V)
    (beta : RootCoefficients) (hbeta : ¬ (∀ i, 0 ≤ beta i)) :
    rootCoefficient (M.rootCharacter * principalRootEulerDenominator) beta = 0 :=
  rootCoefficient_of_not_nonneg _ beta hbeta

end PrincipalHighestWeightModule

theorem skewPrincipalModule_rootNumerator_antisymmetric (w : K) (hw : w^4-w^2+1=0)
    (i : Fin 3) (beta : RootCoefficients) :
    rootCoefficient ((skewPrincipalModule w hw).rootCharacter * principalRootEulerDenominator)
      (simpleReflection (fun j => (skewPrincipalModule w hw).highestWeightLabels j+1) i beta) =
      -rootCoefficient ((skewPrincipalModule w hw).rootCharacter * principalRootEulerDenominator) beta :=
  (skewPrincipalModule w hw).rootNumerator_antisymmetric i beta

theorem vacuumPrincipalModule_rootNumerator_antisymmetric (w : K) (hw : w^4-w^2+1=0)
    (i : Fin 3) (beta : RootCoefficients) :
    rootCoefficient ((vacuumPrincipalModule w hw).rootCharacter * principalRootEulerDenominator)
      (simpleReflection (fun j => (vacuumPrincipalModule w hw).highestWeightLabels j+1) i beta) =
      -rootCoefficient ((vacuumPrincipalModule w hw).rootCharacter * principalRootEulerDenominator) beta :=
  (vacuumPrincipalModule w hw).rootNumerator_antisymmetric i beta

theorem alternatingPrincipalModule_rootNumerator_antisymmetric (w : K) (hw : w^4-w^2+1=0)
    (i : Fin 3) (beta : RootCoefficients) :
    rootCoefficient ((alternatingPrincipalModule w hw).rootCharacter * principalRootEulerDenominator)
      (simpleReflection (fun j => (alternatingPrincipalModule w hw).highestWeightLabels j+1) i beta) =
      -rootCoefficient ((alternatingPrincipalModule w hw).rootCharacter * principalRootEulerDenominator) beta :=
  (alternatingPrincipalModule w hw).rootNumerator_antisymmetric i beta

end KanadeRussell.Representation
