import KanadeRussell.Tsuchioka.AffineHighestWeight
import KanadeRussell.Tsuchioka.TensorLieDerivation

/-! Principal-degree brackets for the concrete affine Chevalley generators. -/

set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem principalDerivation_chevalleyE (w : K) (i : Fin 3) :
    ⁅principalDerivation (K := K), chevalleyE w i⁆ = chevalleyE w i := by
  have hc : chevalleyECoordinates w i 3 = 0 := by
    fin_cases i <;> norm_num [chevalleyECoordinates, Matrix.cons_val_two, Matrix.cons_val_three]
  simpa only [chevalleyE, Int.cast_one, one_smul, hc, mul_zero, zero_smul, sub_zero] using
    principalDerivation_tensorModeEvaluate_lie w 1 (chevalleyECoordinates w i)

theorem principalDerivation_chevalleyF (w : K) (i : Fin 3) :
    ⁅principalDerivation (K := K), chevalleyF w i⁆ = -chevalleyF w i := by
  have hc : chevalleyFCoordinates w i 3 = 0 := by
    fin_cases i <;> norm_num [chevalleyFCoordinates, Matrix.cons_val_two, Matrix.cons_val_three]
  have h : ⁅principalDerivation (K := K), chevalleyF w i⁆ = (-1 : K) • chevalleyF w i := by
    simpa only [chevalleyF, Int.cast_neg, Int.cast_one,
      hc, mul_zero, zero_smul, sub_zero] using
        principalDerivation_tensorModeEvaluate_lie w (-1) (chevalleyFCoordinates w i)
  exact h.trans (neg_one_smul K (chevalleyF w i))

theorem principalDerivation_chevalleyH (w : K) (i : Fin 3) :
    ⁅principalDerivation (K := K), chevalleyH w i⁆ = 0 := by
  simpa only [chevalleyH, Int.cast_zero, zero_smul, zero_mul, sub_zero] using
    principalDerivation_tensorModeEvaluate_lie w 0 (chevalleyHCoordinates w i)

end KanadeRussell.Tsuchioka.Fock
