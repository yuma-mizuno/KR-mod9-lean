import KanadeRussell.Representation.LevelNineSmallProductTarget
import KanadeRussell.Infra.G2JacobiFunctionalEquations
import KanadeRussell.Infra.A2CoefficientResidues

/-! Exact finite-product specialization of the six G2 Jacobi factors to
the three affine denominators, with the fourth Euler power retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Representation.CooperProductSpecialization
open Product Infra.G2JacobiFunctionalEquations
open Product.CubicScalarExtension (L p eval)
open LevelNineSmallProductTarget (eval_E eval_J)

theorem denominator221_six_J :
    (E 9)^4*dualAffineDenominator 2 2 1 =
      Product.J 1*Product.J 2*Product.J 3*Product.J 4*Product.J 5*Product.J 7 := by
  norm_num [dualAffineDenominator,dualImaginaryPeriod,dualRootHeights,
    dualPositiveRootCoordinates,progressionProduct,Product.J,P9]
  ring

theorem denominator411_six_J :
    (E 9)^4*dualAffineDenominator 4 1 1 =
      Product.J 1*Product.J 1*Product.J 2*Product.J 3*Product.J 4*Product.J 5 := by
  norm_num [dualAffineDenominator,dualImaginaryPeriod,dualRootHeights,
    dualPositiveRootCoordinates,progressionProduct,Product.J,P9]
  ring

theorem denominator112_six_J :
    (E 9)^4*dualAffineDenominator 1 1 2 =
      Product.J 2*Product.J 1*Product.J 3*Product.J 5*Product.J 7*Product.J 8 := by
  norm_num [dualAffineDenominator,dualImaginaryPeriod,dualRootHeights,
    dualPositiveRootCoordinates,progressionProduct,Product.J,P9]
  ring

theorem eval_denominator221_g2 :
    eval (E 9)^4*eval (dualAffineDenominator 2 2 1) =
      g2Product (p^9) (p^2) (p^4) := by
  have h := congrArg eval denominator221_six_J
  simp only [map_mul,map_pow] at h
  rw [eval_J 1 (by decide),eval_J 2 (by decide),eval_J 3 (by decide),
    eval_J 4 (by decide),eval_J 5 (by decide),eval_J 7 (by decide)] at h
  simpa only [g2Product,← pow_mul,← pow_add,Nat.reduceMul,Nat.reduceAdd] using h

theorem eval_denominator411_g2 :
    eval (E 9)^4*eval (dualAffineDenominator 4 1 1) =
      g2Product (p^9) (p^2) (p^2) := by
  have h := congrArg eval denominator411_six_J
  simp only [map_mul,map_pow] at h
  rw [eval_J 1 (by decide),eval_J 2 (by decide),eval_J 3 (by decide),
    eval_J 4 (by decide),eval_J 5 (by decide)] at h
  simpa only [g2Product,← pow_mul,← pow_add,Nat.reduceMul,Nat.reduceAdd] using h

theorem eval_denominator112_g2 :
    eval (E 9)^4*eval (dualAffineDenominator 1 1 2) =
      g2Product (p^9) (p^4) (p^2) := by
  have h := congrArg eval denominator112_six_J
  simp only [map_mul,map_pow] at h
  rw [eval_J 1 (by decide),eval_J 2 (by decide),eval_J 3 (by decide),
    eval_J 5 (by decide),eval_J 7 (by decide),eval_J 8 (by decide)] at h
  simpa only [g2Product,← pow_mul,← pow_add,Nat.reduceMul,Nat.reduceAdd] using h

theorem eval_euler_ninth : Infra.A2CoefficientResidues.euler (p^9) = eval (E 9) := by
  rw [eval_E 9 (by decide)]
  simp only [Infra.A2CoefficientResidues.euler,Units.val_pow_eq_pow_val,← pow_mul,
    Nat.reduceMul]

/-- Faithful evaluation and a proved Euler unit recover the first integral denominator. -/
theorem numerator_eq_221_of_eval_g2 (N : PowerSeries ℤ)
    (h : eval (E 9)^4*eval N = g2Product (p^9) (p^2) (p^4)) :
    N = dualAffineDenominator 2 2 1 := by
  apply Product.CubicScalarExtension.eval_injective
  exact (((isUnit_E 9 (by decide)).map eval).pow 4).mul_left_cancel
    (h.trans eval_denominator221_g2.symm)

/-- Faithful evaluation and a proved Euler unit recover the second integral denominator. -/
theorem numerator_eq_411_of_eval_g2 (N : PowerSeries ℤ)
    (h : eval (E 9)^4*eval N = g2Product (p^9) (p^2) (p^2)) :
    N = dualAffineDenominator 4 1 1 := by
  apply Product.CubicScalarExtension.eval_injective
  exact (((isUnit_E 9 (by decide)).map eval).pow 4).mul_left_cancel
    (h.trans eval_denominator411_g2.symm)

/-- Faithful evaluation and a proved Euler unit recover the third integral denominator. -/
theorem numerator_eq_112_of_eval_g2 (N : PowerSeries ℤ)
    (h : eval (E 9)^4*eval N = g2Product (p^9) (p^4) (p^2)) :
    N = dualAffineDenominator 1 1 2 := by
  apply Product.CubicScalarExtension.eval_injective
  exact (((isUnit_E 9 (by decide)).map eval).pow 4).mul_left_cancel
    (h.trans eval_denominator112_g2.symm)
end KanadeRussell.Representation.CooperProductSpecialization
