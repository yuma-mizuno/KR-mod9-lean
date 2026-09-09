import KanadeRussell.Representation.RootInvariantConvolutionCancellation
import KanadeRussell.Representation.RootLambertReflection
import KanadeRussell.Representation.RootInvariantSpecialization

/-! The actual denominator residual is Weyl invariant and supported on the
null ray. Its principal specialization therefore retains the entire equation. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K] [CharZero K]

/-- Ordinary Weyl invariance of the actual Lambert residual. -/
theorem rootCoefficient_principalRootLambertResidual_reflection (i : Fin 3)
    (beta : RootCoefficients) :
    rootCoefficient (principalRootLambertResidual (K := K)) (simpleReflection 0 i beta) =
      rootCoefficient (principalRootLambertResidual (K := K)) beta := by
  apply rootCoefficient_invariant_of_mul (linearRootReflection i)
    (principalRootComplementEuler i) principalRootLambertResidual
  · change rootCoefficient _ (rootCoefficientsOfExponent 0) = _
    rw [rootCoefficient_ofExponent, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_principalRootComplementEuler]
  · exact rootCoefficient_principalRootComplementEuler_reflection i
  · exact rootCoefficient_complement_mul_residual_reflection i

theorem principalRootLambertResidual_nonzero_eq_null (beta : RootCoefficients)
    (hbeta : rootCoefficient (principalRootLambertResidual (K := K)) beta ≠ 0) :
    ∃ n : ℕ, beta = (n : ℤ) • marks :=
  invariant_nonzero_eq_nat_smul_marks (rootCoefficient (principalRootLambertResidual (K := K)))
    (rootCoefficient_of_not_nonneg _) rootCoefficient_principalRootLambertResidual_reflection beta hbeta

theorem principalRootLambertResidual_off_null (beta : RootCoefficients)
    (hbeta : ¬ ∃ n : ℕ, beta = (n : ℤ) • marks) :
    rootCoefficient (principalRootLambertResidual (K := K)) beta = 0 := by
  by_contra h
  exact hbeta (principalRootLambertResidual_nonzero_eq_null beta h)

theorem coeff_rootPrincipalSpecialization_residual_null (n : ℕ) :
    PowerSeries.coeff (4*n) (rootPrincipalSpecialization (principalRootLambertResidual (K := K))) =
      rootCoefficient (principalRootLambertResidual (K := K)) ((n : ℤ) • marks) :=
  coeff_rootPrincipalSpecialization_of_invariant _ rootCoefficient_principalRootLambertResidual_reflection n

/-- The remaining multivariate denominator equation is equivalent to a single
principal series identity; all invariance hypotheses have been proved. -/
theorem rootCasimir_denominator_eq_zero_iff_principalResidual :
    rootCasimirOperator (fun _ => 1) (principalRootEulerDenominator (K := K)) = 0 ↔
      rootPrincipalSpecialization (principalRootLambertResidual (K := K)) = 0 := by
  rw [rootCasimir_principalRootEulerDenominator_eq_zero_iff]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply rootPrincipalSpecialization_injective_on_invariant _ 0
      rootCoefficient_principalRootLambertResidual_reflection
    · intro i beta
      rw [rootCoefficient_zero, rootCoefficient_zero]
    · simpa only [map_zero] using h

end KanadeRussell.Representation
