import KanadeRussell.Representation.RootLambertDenominatorCriterion
import Mathlib.Analysis.Complex.Basic

/-! Integral forms of the two scalar root moments and faithful descent of
an explicitly supplied complex Lambert identity. The transport result proves
no complex identity by itself. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KanadeRussell.Representation

/-- The same finite divisor-coefficient transform, with integral coefficients. -/
def integralScalarLambertTransform (f : ℕ → ℕ → ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ∑ h ∈ Finset.range n, ∑ k ∈ Finset.range (n+1),
    if (k+1)*(h+1)=n then f h k else 0

@[simp] theorem coeff_integralScalarLambertTransform (f : ℕ → ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff n (integralScalarLambertTransform f) =
      ∑ h ∈ Finset.range n, ∑ k ∈ Finset.range (n+1),
        if (k+1)*(h+1)=n then f h k else 0 := by
  simp only [integralScalarLambertTransform, PowerSeries.coeff_mk]

/-- The integral coefficient series underlying the original scalar T. -/
def integralPrincipalScalarT : PowerSeries ℤ := integralScalarLambertTransform fun h _ =>
  -principalRootMomentA (positiveModeResidue h)-principalRootMomentB (positiveModeResidue h)

/-- The integral coefficient series underlying the original scalar U. -/
def integralPrincipalScalarU : PowerSeries ℤ := integralScalarLambertTransform fun h _ =>
  principalRootMomentA (positiveModeResidue h)-principalRootMomentB (positiveModeResidue h)

variable {K : Type*} [Field K]

theorem map_integralScalarLambertTransform (f : ℕ → ℕ → ℤ) :
    PowerSeries.map (Int.castRingHom K) (integralScalarLambertTransform f) =
      scalarLambertTransform (fun h k => (f h k : K)) := by
  classical
  ext n
  rw [PowerSeries.coeff_map, coeff_integralScalarLambertTransform, coeff_scalarLambertTransform]
  simp

theorem map_integralPrincipalScalarT :
    PowerSeries.map (Int.castRingHom K) integralPrincipalScalarT = principalScalarT := by
  exact map_integralScalarLambertTransform _

theorem map_integralPrincipalScalarU :
    PowerSeries.map (Int.castRingHom K) integralPrincipalScalarU = principalScalarU := by
  exact map_integralScalarLambertTransform _

/-- A complex identity descends to the actual integral T/U series by coefficient injectivity. -/
theorem integralPrincipalScalar_lambert_identity_of_complex
    (hComplex : (principalScalarT (K := ℂ))^2+2 • principalScalarT+3 • principalScalarU^2 =
      PowerSeries.map (Int.castRingHom ℂ)
        (2 • Product.lambert 1+6 • Product.lambert 3+4 • Product.lambert 4-
          24 • Product.lambert 6-12 • Product.lambert 12)) :
    integralPrincipalScalarT^2+2 • integralPrincipalScalarT+3 • integralPrincipalScalarU^2 =
      2 • Product.lambert 1+6 • Product.lambert 3+4 • Product.lambert 4-
        24 • Product.lambert 6-12 • Product.lambert 12 := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  simpa only [map_add, map_pow, map_nsmul, map_integralPrincipalScalarT,
    map_integralPrincipalScalarU] using hComplex

/-- An integral scalar identity transports to every coefficient field, including positive characteristic. -/
theorem principalScalar_lambert_identity_of_integral
    (hIntegral : integralPrincipalScalarT^2+2 • integralPrincipalScalarT+3 • integralPrincipalScalarU^2 =
      2 • Product.lambert 1+6 • Product.lambert 3+4 • Product.lambert 4-
        24 • Product.lambert 6-12 • Product.lambert 12) :
    (principalScalarT (K := K))^2+2 • principalScalarT+3 • principalScalarU^2 =
      PowerSeries.map (Int.castRingHom K)
        (2 • Product.lambert 1+6 • Product.lambert 3+4 • Product.lambert 4-
          24 • Product.lambert 6-12 • Product.lambert 12) := by
  have h := congrArg (PowerSeries.map (Int.castRingHom K)) hIntegral
  simpa only [map_add, map_pow, map_nsmul, map_integralPrincipalScalarT,
    map_integralPrincipalScalarU] using h

/-- This theorem has the complex Lambert identity as an explicit premise; it introduces no axiom. -/
theorem principalScalar_lambert_identity_of_complex
    (hComplex : (principalScalarT (K := ℂ))^2+2 • principalScalarT+3 • principalScalarU^2 =
      PowerSeries.map (Int.castRingHom ℂ)
        (2 • Product.lambert 1+6 • Product.lambert 3+4 • Product.lambert 4-
          24 • Product.lambert 6-12 • Product.lambert 12)) :
    (principalScalarT (K := K))^2+2 • principalScalarT+3 • principalScalarU^2 =
      PowerSeries.map (Int.castRingHom K)
        (2 • Product.lambert 1+6 • Product.lambert 3+4 • Product.lambert 4-
          24 • Product.lambert 6-12 • Product.lambert 12) :=
  principalScalar_lambert_identity_of_integral
    (integralPrincipalScalar_lambert_identity_of_complex hComplex)

end KanadeRussell.Representation
