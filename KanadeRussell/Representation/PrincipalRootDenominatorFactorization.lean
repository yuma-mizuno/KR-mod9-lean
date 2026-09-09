import KanadeRussell.Representation.PrincipalRootComplementEuler
import KanadeRussell.Representation.RootCoefficientFunction

/-! Removing one simple root from the actual stabilized Euler denominator. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
variable {K : Type*} [Field K]

@[simp] theorem positiveModeExponent_zero (i : Fin 3) :
    positiveModeExponent 0 i = Finsupp.single i 1 := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp only [positiveModeExponent_apply, Finsupp.single_apply] <;> decide

@[simp] theorem principalRootEulerFactor_zero (i : Fin 3) :
    principalRootEulerFactor (K := K) 0 i = 1-MvPowerSeries.X i := by
  have h : principalWeightSlotActive (positiveModeResidue 0) i := by
    fin_cases i <;> decide
  simp only [principalRootEulerFactor, if_pos h, positiveModeExponent_zero, MvPowerSeries.X]

theorem principalRootEulerPartial_factorization (i : Fin 3) (B : ℕ) :
    principalRootEulerPartial (K := K) (B+1) =
      (1-MvPowerSeries.X i)*principalRootComplementPartial i (B+1) := by
  classical
  induction B with
  | zero =>
    simp only [Nat.zero_add, principalRootEulerPartial, principalRootComplementPartial,
      Finset.prod_range_one]
    fin_cases i <;>
      simp [Fin.prod_univ_succ, principalRootComplementFactor, principalRootEulerFactor_zero] <;>
      ring
  | succ B ih =>
    have hf : ∀ r : Fin 3, principalRootComplementFactor (K := K) i (B+1) r =
        principalRootEulerFactor (B+1) r := by
      intro r
      simp [principalRootComplementFactor]
    simp only [principalRootEulerPartial, principalRootComplementPartial,
      Finset.prod_range_succ] at ih ⊢
    rw [ih]
    simp only [hf, mul_assoc]

theorem principalRootEulerDenominator_factorization (i : Fin 3) :
    principalRootEulerDenominator (K := K) =
      (1-MvPowerSeries.X i)*principalRootComplementEuler i := by
  ext e
  let B := rootExponentDegree e + 1
  have hB : rootExponentDegree e ≤ B := Nat.le_succ _
  rw [coeff_principalRootEulerDenominator e B hB]
  rw [principalRootEulerPartial_factorization]
  exact ((RootCoeffAgree.refl (1-MvPowerSeries.X i)).mul
    (principalRootComplementEuler_agree i e B hB) e le_rfl).symm

theorem rootCoefficient_principalRootEulerDenominator (i : Fin 3)
    (beta : AffineWeightLattice.RootCoefficients) :
    rootCoefficient (principalRootEulerDenominator (K := K)) beta =
      rootCoefficient (principalRootComplementEuler i) beta -
        rootCoefficient (principalRootComplementEuler i) (beta-Pi.single i 1) := by
  rw [principalRootEulerDenominator_factorization i, sub_mul, one_mul]
  change rootCoefficientLinear beta (_-_) = _
  rw [map_sub]
  exact congrArg₂ (fun a b : K => a-b) rfl (rootCoefficient_simpleRoot_mul i _ beta)

end KanadeRussell.Representation
