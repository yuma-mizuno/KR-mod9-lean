import KanadeRussell.Representation.RootLambertCharacterSeries
import KanadeRussell.Representation.RootLambertDivisorBridge
import KanadeRussell.Representation.RootDenominatorPrincipalReduction

/-! The remaining denominator equation expressed in the original integer
Lambert series and the two exact character Lambert combinations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
variable {K : Type*} [Field K]

theorem principalScalarNorm_lambert : principalScalarNorm (K := K) =
    PowerSeries.map (Int.castRingHom K)
      (5 • Product.lambert 1 - 3 • Product.lambert 2 - 3 • Product.lambert 3 +
        Product.lambert 4 + 3 • Product.lambert 6 - 3 • Product.lambert 12) := by
  unfold principalScalarNorm
  simp only [map_add, map_sub, map_nsmul]
  rw [← scalarLambertTransform_repetition_divisor 1 (by decide),
    ← scalarLambertTransform_repetition_divisor 2 (by decide),
    ← scalarLambertTransform_repetition_divisor 3 (by decide),
    ← scalarLambertTransform_repetition_divisor 4 (by decide),
    ← scalarLambertTransform_repetition_divisor 6 (by decide),
    ← scalarLambertTransform_repetition_divisor 12 (by decide)]
  simp only [← map_nsmul, ← map_add, ← map_sub]
  congr 1
  ext h k
  simp [principalRootMomentNorm_dvd, mul_sub, mul_add, mul_ite]
  simp only [add_mul, one_mul, mul_comm]

theorem principalScalarHeight_lambert : principalScalarHeight (K := K) =
    PowerSeries.map (Int.castRingHom K)
      (3 • Product.lambert 1 - 2 • Product.lambert 2 - 3 • Product.lambert 3 +
        6 • Product.lambert 6) := by
  have h : principalScalarHeight (K := K) =
      3 • scalarLambertTransform (fun h _ => if 1 ∣ h+1 then ((h+1 : ℕ) : K) else 0) -
        scalarLambertTransform (fun h _ => if 2 ∣ h+1 then ((h+1 : ℕ) : K) else 0) -
        scalarLambertTransform (fun h _ => if 3 ∣ h+1 then ((h+1 : ℕ) : K) else 0) +
        scalarLambertTransform (fun h _ => if 6 ∣ h+1 then ((h+1 : ℕ) : K) else 0) := by
    unfold principalScalarHeight
    simp only [← map_nsmul, ← map_add, ← map_sub]
    congr 1
    ext h k
    simp [principalRootMomentCount_dvd, mul_sub, mul_add, mul_ite]
    ring
  rw [h, scalarLambertTransform_height_divisor 1 (by decide),
    scalarLambertTransform_height_divisor 2 (by decide),
    scalarLambertTransform_height_divisor 3 (by decide),
    scalarLambertTransform_height_divisor 6 (by decide)]
  simp only [map_add, map_sub, map_nsmul, Nat.cast_one, one_smul]
  simp only [Nat.cast_smul_eq_nsmul]

theorem rootPrincipalSpecialization_residual_lambert :
    4 • rootPrincipalSpecialization (principalRootLambertResidual (K := K)) =
      (principalScalarT)^2 + 2 • principalScalarT + 3 • (principalScalarU)^2 -
        PowerSeries.map (Int.castRingHom K)
          (2 • Product.lambert 1 + 6 • Product.lambert 3 + 4 • Product.lambert 4 -
            24 • Product.lambert 6 - 12 • Product.lambert 12) := by
  rw [rootPrincipalSpecialization_residual_scalar, principalScalarNorm_lambert,
    principalScalarHeight_lambert]
  simp only [map_add, map_sub, nsmul_eq_mul, map_mul, map_natCast]
  ring

variable [CharZero K]

/-- This is an equivalence with the remaining explicit scalar identity, not
a proof or assumption of that identity. -/
theorem rootCasimir_denominator_eq_zero_iff_lambert_identity :
    rootCasimirOperator (fun _ => 1) (principalRootEulerDenominator (K := K)) = 0 ↔
      (principalScalarT)^2 + 2 • principalScalarT + 3 • (principalScalarU)^2 =
        PowerSeries.map (Int.castRingHom K)
          (2 • Product.lambert 1 + 6 • Product.lambert 3 + 4 • Product.lambert 4 -
            24 • Product.lambert 6 - 12 • Product.lambert 12) := by
  rw [rootCasimir_denominator_eq_zero_iff_principalResidual]
  have h := rootPrincipalSpecialization_residual_lambert (K := K)
  constructor
  · intro hz
    rw [hz, smul_zero] at h
    exact sub_eq_zero.mp h.symm
  · intro heq
    rw [heq, sub_self, nsmul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (by
      intro hz
      have hc := congrArg (PowerSeries.constantCoeff (R := K)) hz
      simp only [map_natCast, map_zero] at hc
      norm_num at hc)

end KanadeRussell.Representation
