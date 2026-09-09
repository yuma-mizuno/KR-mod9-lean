import KanadeRussell.Representation.PrincipalRootEulerProduct
import KanadeRussell.Representation.RootCasimirCancellation

/-! An exact Lambert-series reduction of the remaining denominator Casimir
identity. Writing `S_i = principalRootLambert i` and `theta_i = rootEulerOperator i`,
the residual is
`S_0^2 + S_1^2 + 3 S_2^2 - S_0 S_1 - 3 S_1 S_2
 - theta_0 S_0 - theta_1 S_1 - 3 theta_2 S_2
 + theta_0 S_1 + 3 theta_1 S_2 + S_0 + S_1 + 3 S_2`.
The theorem proves `L_rho D = D * residual` and equivalence of the two vanishing
statements. The residual's vanishing is not assumed or proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K]

private theorem rootCasimirOperator_rho_expand (f : MvPowerSeries (Fin 3) K) :
    rootCasimirOperator (fun _ => 1) f =
      rootEulerOperator 0 (rootEulerOperator 0 f) + rootEulerOperator 1 (rootEulerOperator 1 f) +
      3 • rootEulerOperator 2 (rootEulerOperator 2 f) - rootEulerOperator 0 (rootEulerOperator 1 f) -
      3 • rootEulerOperator 1 (rootEulerOperator 2 f) - rootEulerOperator 0 f -
      rootEulerOperator 1 f - 3 • rootEulerOperator 2 f := by
  ext e
  simp only [map_add, map_sub, map_nsmul, coeff_rootCasimirOperator, coeff_rootEulerOperator]
  norm_num [casimir_eq, rootCoefficientsOfExponent]
  ring

/-- The exact rank-two Lambert expression whose vanishing remains to be proved. -/
noncomputable def principalRootLambertResidual : MvPowerSeries (Fin 3) K :=
  (principalRootLambert 0)^2 + (principalRootLambert 1)^2 + 3 • (principalRootLambert 2)^2 -
    principalRootLambert 0 * principalRootLambert 1 - 3 • (principalRootLambert 1 * principalRootLambert 2) -
    rootEulerOperator 0 (principalRootLambert 0) - rootEulerOperator 1 (principalRootLambert 1) -
    3 • rootEulerOperator 2 (principalRootLambert 2) + rootEulerOperator 0 (principalRootLambert 1) +
    3 • rootEulerOperator 1 (principalRootLambert 2) + principalRootLambert 0 + principalRootLambert 1 +
    3 • principalRootLambert 2

theorem rootCasimir_principalRootEulerDenominator_eq :
    rootCasimirOperator (fun _ => 1) (principalRootEulerDenominator (K := K)) =
      principalRootEulerDenominator * principalRootLambertResidual := by
  rw [rootCasimirOperator_rho_expand]
  simp only [rootEulerOperator_principalRootEulerDenominator, neg_mul, map_neg,
    rootEulerOperator_mul]
  unfold principalRootLambertResidual
  simp only [nsmul_eq_mul]
  ring

theorem principalRootEulerDenominator_ne_zero :
    (principalRootEulerDenominator (K := K)) ≠ 0 := by
  intro h
  have hc := congrArg MvPowerSeries.constantCoeff h
  rw [constantCoeff_principalRootEulerDenominator, map_zero] at hc
  exact one_ne_zero hc

/-- Harmonicity of the denominator is exactly the explicit Lambert identity. -/
theorem rootCasimir_principalRootEulerDenominator_eq_zero_iff :
    rootCasimirOperator (fun _ => 1) (principalRootEulerDenominator (K := K)) = 0 ↔
      principalRootLambertResidual (K := K) = 0 := by
  rw [rootCasimir_principalRootEulerDenominator_eq, mul_eq_zero,
    or_iff_right principalRootEulerDenominator_ne_zero]

end KanadeRussell.Representation
