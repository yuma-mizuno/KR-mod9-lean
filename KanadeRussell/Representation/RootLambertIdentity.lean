import KanadeRussell.Representation.TorsionScalarIdentity
import KanadeRussell.Representation.RootLambertFieldTransport
import KanadeRussell.Representation.RootLambertDenominatorCriterion
import KanadeRussell.Infra.ComplexTorsionWitness
import KanadeRussell.Infra.LaurentTorsionCertificate

/-! The actual scalar Lambert identity and root-denominator Casimir equation.
The proof uses the twelve actual torsion relations, faithful Laurent descent,
and integral coefficient transport. No character formula is assumed. -/
set_option autoImplicit false
namespace KanadeRussell.Representation

theorem principalScalar_lambert_identity_complex :
    (principalScalarT (K := ℂ))^2+2 • principalScalarT+3 • principalScalarU^2 =
      PowerSeries.map (Int.castRingHom ℂ)
        (2 • Product.lambert 1+6 • Product.lambert 3+4 • Product.lambert 4-
          24 • Product.lambert 6-12 • Product.lambert 12) := by
  obtain ⟨w,a,_,hw,ha⟩ := Infra.exists_complex_torsion_units
  exact principalScalar_identity_of_torsion_square w hw
    (Infra.LaurentTorsionCertificate.mixed_square w a hw ha)

theorem integralPrincipalScalar_lambert_identity :
    integralPrincipalScalarT^2+2 • integralPrincipalScalarT+3 • integralPrincipalScalarU^2 =
      2 • Product.lambert 1+6 • Product.lambert 3+4 • Product.lambert 4-
        24 • Product.lambert 6-12 • Product.lambert 12 :=
  integralPrincipalScalar_lambert_identity_of_complex principalScalar_lambert_identity_complex
theorem principalScalar_lambert_identity {K : Type*} [Field K] :
    (principalScalarT (K := K))^2+2 • principalScalarT+3 • principalScalarU^2 =
      PowerSeries.map (Int.castRingHom K)
        (2 • Product.lambert 1+6 • Product.lambert 3+4 • Product.lambert 4-
          24 • Product.lambert 6-12 • Product.lambert 12) :=
  principalScalar_lambert_identity_of_complex principalScalar_lambert_identity_complex

theorem rootCasimir_principalRootEulerDenominator_zero {K : Type*} [Field K] [CharZero K] :
    rootCasimirOperator (fun _ => 1) (principalRootEulerDenominator (K := K)) = 0 :=
  rootCasimir_denominator_eq_zero_iff_lambert_identity.mpr principalScalar_lambert_identity

theorem principalRootLambertResidual_eq_zero {K : Type*} [Field K] [CharZero K] :
    principalRootLambertResidual (K := K) = 0 :=
  rootCasimir_principalRootEulerDenominator_eq_zero_iff.mp rootCasimir_principalRootEulerDenominator_zero

end KanadeRussell.Representation
