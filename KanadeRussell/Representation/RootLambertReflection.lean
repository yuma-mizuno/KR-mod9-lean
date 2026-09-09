import KanadeRussell.Representation.PrincipalRootDenominatorAntisymmetry
import KanadeRussell.Representation.RootEulerCasimirReduction

/-! Root-string division of shifted antisymmetry, without defining an infinite
Weyl action on the completed power-series ring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K] [CharZero K]

private theorem integer_difference_antisymmetry (b : ℤ → K) (N : ℤ)
    (h : ∀ x, b (N+1-x)-b (N-x) = -(b x-b (x-1))) :
    ∀ x, b (N-x)=b x := by
  let d : ℤ → K := fun x => b (N-x)-b x
  have hs (x : ℤ) : d (x+1)=d x := by
    have hh := h (x+1)
    have h1 : N+1-(x+1)=N-x := by omega
    have h2 : (x+1)-1=x := by omega
    rw [h1,h2] at hh
    dsimp [d]
    linear_combination -hh
  have hc (x : ℤ) : d x=d 0 := by
    induction x using Int.induction_on with
    | zero => rfl
    | succ n ih => exact (hs n).trans ih
    | pred n ih =>
      have hh := hs (-(n:ℤ)-1)
      rw [sub_add_cancel] at hh
      convert hh.symm.trans ih using 1
  intro x
  have hh := (hc x).trans (hc (N-x)).symm
  dsimp [d] at hh
  have hn : N-(N-x)=x := by omega
  rw [hn] at hh
  linear_combination hh / 2

private theorem reflection_single (i : Fin 3) (x : ℤ) :
    simpleReflection 0 i (Pi.single i x) = Pi.single i (-x) := by
  have hd : Tsuchioka.Fock.affineCartanMatrix i i = 2 := by
    fin_cases i <;> norm_num [Tsuchioka.Fock.affineCartanMatrix, Matrix.cons_val_two]
  ext j
  by_cases hj : j=i
  · subst j
    simp [simpleReflection, weightLabels, Pi.single_apply, hd]
    ring
  · simp [simpleReflection, hj]

private theorem reflection_slice (i : Fin 3) (beta : RootCoefficients) (x : ℤ) :
    simpleReflection (fun _ => 1) i (beta+Pi.single i x) =
      beta+Pi.single i (weightLabels 0 beta i+1-x) := by
  rw [simpleReflection_rho_eq, simpleReflection_zero_add, reflection_single]
  change (beta+Pi.single i (weightLabels 0 beta i))+Pi.single i (-x)+Pi.single i 1 = _
  ext j
  by_cases hj : i=j
  · subst j
    simp
    ring
  · simp [hj]

private theorem slice_sub (i : Fin 3) (beta : RootCoefficients) (x : ℤ) :
    beta+Pi.single i x-Pi.single i 1 = beta+Pi.single i (x-1) := by
  ext j
  by_cases hj : i=j
  · subst j
    simp
    ring
  · simp [hj]

omit [CharZero K] in
theorem rootCoefficient_one_sub_X_mul (i : Fin 3)
    (B : MvPowerSeries (Fin 3) K) (beta : RootCoefficients) :
    rootCoefficient ((1-MvPowerSeries.X i)*B) beta =
      rootCoefficient B beta-rootCoefficient B (beta-Pi.single i 1) := by
  rw [sub_mul, one_mul]
  change rootCoefficientLinear beta (B-MvPowerSeries.X i*B) = _
  rw [map_sub, rootCoefficientLinear_apply, rootCoefficientLinear_apply,
    rootCoefficient_simpleRoot_mul]

/-- Division by the simple-root factor converts rho antisymmetry to ordinary symmetry. -/
theorem rootCoefficient_reflection_of_one_sub_X_antisymmetry
    (i : Fin 3) (B : MvPowerSeries (Fin 3) K)
    (h : ∀ beta, rootCoefficient ((1-MvPowerSeries.X i)*B)
      (simpleReflection (fun _ => 1) i beta) =
        -rootCoefficient ((1-MvPowerSeries.X i)*B) beta) (beta : RootCoefficients) :
    rootCoefficient B (simpleReflection 0 i beta) = rootCoefficient B beta := by
  have hb := integer_difference_antisymmetry
    (fun x => rootCoefficient B (beta+Pi.single i x)) (weightLabels 0 beta i) (by
      intro x
      have hh := h (beta+Pi.single i x)
      rw [rootCoefficient_one_sub_X_mul, rootCoefficient_one_sub_X_mul,
        reflection_slice, slice_sub, slice_sub] at hh
      have he : weightLabels 0 beta i+1-x-1=weightLabels 0 beta i-x := by omega
      rwa [he] at hh) 0
  simpa only [sub_zero, Pi.single_zero, add_zero, simpleReflection] using hb

omit [CharZero K] in
private theorem rootCoefficient_rootCasimirOperator (lambda : RootCoefficients)
    (f : MvPowerSeries (Fin 3) K) (beta : RootCoefficients) :
    rootCoefficient (rootCasimirOperator lambda f) beta =
      (casimir lambda beta : K) * rootCoefficient f beta := by
  by_cases hb : ∀ i, 0 ≤ beta i
  · rw [rootCoefficient_of_nonneg _ _ hb, coeff_rootCasimirOperator,
      rootCoefficient_of_nonneg _ _ hb, rootCoefficientsOfExponent_ofRoot beta hb]
  · rw [rootCoefficient_of_not_nonneg _ _ hb, rootCoefficient_of_not_nonneg _ _ hb, mul_zero]

omit [CharZero K] in
theorem rootCoefficient_casimirDenominator_reflection (i : Fin 3) (beta : RootCoefficients) :
    rootCoefficient (rootCasimirOperator (fun _ => 1) (principalRootEulerDenominator (K := K)))
      (simpleReflection (fun _ => 1) i beta) =
      -rootCoefficient (rootCasimirOperator (fun _ => 1) (principalRootEulerDenominator (K := K))) beta := by
  rw [rootCoefficient_rootCasimirOperator, rootCoefficient_rootCasimirOperator,
    casimir_simpleReflection, rootCoefficient_principalRootEulerDenominator_reflection]
  ring

theorem rootCoefficient_complement_mul_residual_reflection (i : Fin 3) (beta : RootCoefficients) :
    rootCoefficient ((principalRootComplementEuler (K := K) i)*principalRootLambertResidual)
      (simpleReflection 0 i beta) =
      rootCoefficient ((principalRootComplementEuler (K := K) i)*principalRootLambertResidual) beta := by
  apply rootCoefficient_reflection_of_one_sub_X_antisymmetry
  intro alpha
  have he : (1-MvPowerSeries.X i)*
      ((principalRootComplementEuler (K := K) i)*principalRootLambertResidual) =
      rootCasimirOperator (fun _ => 1) principalRootEulerDenominator := by
    rw [← mul_assoc, ← principalRootEulerDenominator_factorization,
      rootCasimir_principalRootEulerDenominator_eq]
  rw [he]
  exact rootCoefficient_casimirDenominator_reflection i alpha

end KanadeRussell.Representation
