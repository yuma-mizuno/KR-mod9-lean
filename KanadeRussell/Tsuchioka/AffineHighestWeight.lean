import KanadeRussell.Tsuchioka.AffineChevalley
import KanadeRussell.Tsuchioka.TensorVacuumWeights

/-! The constructed affine Chevalley action has level three and polynomial
vacuum of highest weight (3,0,0). This does not assert a character formula. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem chevalleyE_vacuum (w : K) (i : Fin 3) :
    chevalleyE w i (1 : Space K) = 0 := by
  have hc : chevalleyECoordinates w i 3 = 0 := by
    fin_cases i <;> norm_num [chevalleyECoordinates, Matrix.cons_val_two, Matrix.cons_val_three]
  simp only [chevalleyE, tensorModeEvaluate_apply, LinearMap.add_apply, LinearMap.smul_apply,
    tensorRootMode_vacuum_pos w _ 1 (by decide), heisenbergMode_vacuum_pos w 1 (by decide),
    hc, zero_smul, smul_zero, add_zero]

theorem chevalleyH_vacuum (w : K) (i : Fin 3) :
    chevalleyH w i (1 : Space K) = (if i=0 then (3 : K) else 0) • (1 : Space K) := by
  simp only [chevalleyH, tensorModeEvaluate_apply, LinearMap.add_apply, LinearMap.smul_apply,
    tensorRootMode_vacuum_zero, heisenbergMode_zero, LinearMap.zero_apply,
    Module.End.one_apply, smul_zero, add_zero, smul_smul]
  fin_cases i <;> norm_num [chevalleyHCoordinates, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    module

/-- The source dual marks (1,2,3) give the actual scalar level three. -/
theorem chevalley_central_level (w : K) :
    chevalleyH w 0 + (2 : K) • chevalleyH w 1 + (3 : K) • chevalleyH w 2 =
      (3 : K) • (1 : Module.End K (Space K)) := by
  simp only [chevalleyH, tensorModeEvaluate_apply, heisenbergMode_zero, smul_zero, add_zero]
  norm_num [chevalleyHCoordinates, Matrix.cons_val_two, Matrix.cons_val_three]
  module

theorem chevalley_central_eq (w : K) :
    chevalleyH w 0 + (2 : K) • chevalleyH w 1 + (3 : K) • chevalleyH w 2 =
      (centralOperator : Module.End K (Space K)) :=
  chevalley_central_level w

theorem principalDerivation_vacuum : principalDerivation (1 : Space K) = 0 := by
  change -(degreeOperator (1 : Space K)) = 0
  rw [degreeOperator_eq_of_grade 0 1 (MvPolynomial.isWeightedHomogeneous_one K variableWeight)]
  simp

/-- Highest-weight conditions for the explicit level-three affine tensor action. -/
theorem tensor_vacuum_highest_weight (w : K) :
    (1 : Space K) ≠ 0 ∧
    (∀ i : Fin 3, chevalleyE w i (1 : Space K) = 0) ∧
    (∀ i : Fin 3, chevalleyH w i (1 : Space K) =
      (if i=0 then (3 : K) else 0) • (1 : Space K)) ∧
    principalDerivation (1 : Space K) = 0 :=
  ⟨one_ne_zero, chevalleyE_vacuum w, chevalleyH_vacuum w, principalDerivation_vacuum⟩

end KanadeRussell.Tsuchioka.Fock
