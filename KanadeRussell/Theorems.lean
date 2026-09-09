import KanadeRussell.Representation.PrincipalCooperEvaluation
import KanadeRussell.Representation.CooperProductSpecialization

/-! The three original Kanade--Russell identities, including convergence.
The actual tensor characters are evaluated by the proved G2 denominator sum.
Tsuchioka's concrete spanning bounds then give the lower bounds used by the
source/product norm and positive-coefficient rigidity proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity

namespace KanadeRussell.Representation.LevelNineNumeratorMasks
open CooperProductSpecialization PrincipalCooperEvaluation Product

theorem principalNumerator_zero_eq : principalNumerator 0 = dualAffineDenominator 2 2 1 := by
  apply numerator_eq_221_of_eval_g2
  simpa [labels,Matrix.cons_val_succ,zpow_ofNat] using eval_principalNumerator_g2 0

theorem principalNumerator_one_eq : principalNumerator 1 = dualAffineDenominator 4 1 1 := by
  apply numerator_eq_411_of_eval_g2
  simpa [labels,Matrix.cons_val_succ,zpow_ofNat] using eval_principalNumerator_g2 1

theorem principalNumerator_two_eq : principalNumerator 2 = dualAffineDenominator 1 1 2 := by
  apply numerator_eq_112_of_eval_g2
  simpa [labels,Matrix.cons_val_succ,zpow_ofNat] using eval_principalNumerator_g2 2

theorem principalNumerator_zero_product : E 9*principalNumerator 0 = E 1*J 2*J 4 := by
  rw [principalNumerator_zero_eq]
  exact dualAffineDenominator_221_J_cleared

theorem principalNumerator_one_product : E 9*principalNumerator 1 = E 1*J 1*J 4 := by
  rw [principalNumerator_one_eq]
  exact dualAffineDenominator_411_J_cleared

theorem principalNumerator_two_product : E 9*principalNumerator 2 = E 1*J 1*J 2 := by
  rw [principalNumerator_two_eq]
  exact dualAffineDenominator_112_J_cleared

end KanadeRussell.Representation.LevelNineNumeratorMasks

namespace KanadeRussell
open Representation.LevelNineNumeratorMasks Tsuchioka

/-- The three actual principally specialized character formulas are proved. -/
theorem principalCharacterFormulas {K : Type*} [Field K] [CharZero K]
    (w : K) (hw : w^4-w^2+1=0) : PrincipalCharacterFormulas w :=
  principalCharacterFormulas_of_principal_mask_products w hw
    principalNumerator_zero_product principalNumerator_one_product principalNumerator_two_product

/-- The standard-module applications hold for the actual three cyclic modules. -/
theorem standardCharacters {K : Type*} [Field K] [CharZero K]
    (w : K) (hw : w^4-w^2+1=0) : StandardCharacters w hw :=
  standardCharacters_of_principalCharacterFormulas w hw (principalCharacterFormulas w hw)

/-- Tsuchioka's concrete spanning bounds and the evaluated characters give all three lower bounds. -/
theorem lowerBounds : LowerBounds :=
  lowerBounds_of_principalCharacterFormulas complexPhase complexPhase_relation
    (principalCharacterFormulas complexPhase complexPhase_relation)

/-- The three original Kanade--Russell identities modulo nine. -/
theorem kanade_russell : A = K₁ ∧ B = K₂ ∧ C = K₃ :=
  kanade_russell_of_lowerBounds lowerBounds

theorem kanade_russell₁ : A = K₁ := kanade_russell.1

theorem kanade_russell₂ : B = K₂ := kanade_russell.2.1

theorem kanade_russell₃ : C = K₃ := kanade_russell.2.2

/-- The original first double sum converges to its reciprocal product. -/
theorem kanade_russell_hasSum₁ : HasSum (sourceTerm 0 0) K₁ := by
  rw [← kanade_russell₁]
  exact (summable_sourceTerm 0 0).hasSum

/-- The original second double sum converges to its reciprocal product. -/
theorem kanade_russell_hasSum₂ : HasSum (sourceTerm 1 3) K₂ := by
  rw [← kanade_russell₂]
  exact (summable_sourceTerm 1 3).hasSum

/-- The original third double sum converges to its reciprocal product. -/
theorem kanade_russell_hasSum₃ : HasSum (sourceTerm 2 3) K₃ := by
  rw [← kanade_russell₃]
  exact (summable_sourceTerm 2 3).hasSum

end KanadeRussell
