import KanadeRussell.Tsuchioka.TensorDegreeOne
import KanadeRussell.Tsuchioka.AffineHighestWeight
import KanadeRussell.Sectors.SkewSeed

/-! The degree-one difference of two tensor coordinates is a nonzero affine
highest-weight vector of weight Lambda_0 + Lambda_1 and principal degree -1. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KanadeRussell.Tsuchioka.Fock
open Sectors
variable {K : Type*} [Field K] [CharZero K]

theorem tensorFirstRoot_zero_degreeOneVariable (w : K) (hw : w^4-w^2+1=0) (a : Fin 3) :
    tensorRootMode w (RootData.simpleRoot 0) 0 (degreeOneVariable a) =
      (w^3/6-w/3-1/4) • degreeOneVariable a := by
  rw [tensorRootMode_zero_degreeOneVariable, RootData.rootWeight_first,
    RootData.rootWeight_first, contraction_one w hw]
  congr 1
  ring

theorem tensorSecondRoot_zero_degreeOneVariable (w : K) (hw : w^4-w^2+1=0) (a : Fin 3) :
    tensorRootMode w (RootData.simpleRoot 1) 0 (degreeOneVariable a) =
      (-w^3/6+w/3-1/4) • degreeOneVariable a := by
  rw [tensorRootMode_zero_degreeOneVariable, RootData.rootWeight_second,
    RootData.rootWeight_second, contraction_one w hw]
  congr 1
  rw [Scalar.zpow_phasePolynomial w hw (-1)]
  norm_num [Scalar.phasePolynomial]
  grind only

theorem chevalleyH_degreeOneVariable (w : K) (hw : w^4-w^2+1=0) (i a : Fin 3) :
    chevalleyH w i (degreeOneVariable a) =
      (if i = 2 then (0 : K) else 1) • degreeOneVariable a := by
  have hc : chevalleyHCoordinates w i 0 * (w^3/6-w/3-1/4) +
      chevalleyHCoordinates w i 1 * (-w^3/6+w/3-1/4) +
      chevalleyHCoordinates w i 3 = (if i = 2 then (0 : K) else 1) := by
    fin_cases i <;> norm_num [chevalleyHCoordinates,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only
  simp only [chevalleyH, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorFirstRoot_zero_degreeOneVariable w hw,
    tensorSecondRoot_zero_degreeOneVariable w hw, heisenbergMode_zero,
    LinearMap.zero_apply, smul_zero, add_zero, Module.End.one_apply, smul_smul]
  rw [← add_smul, ← add_smul, hc]

theorem chevalleyH_skewSeed (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    chevalleyH w i (skewSeed (K := K)) =
      (if i = 2 then (0 : K) else 1) • skewSeed := by
  rw [skewSeed, map_sub, chevalleyH_degreeOneVariable w hw,
    chevalleyH_degreeOneVariable w hw, smul_sub]

theorem tensorRootMode_one_skewSeed (w : K) (beta : RootData.Lattice) :
    tensorRootMode w beta 1 (skewSeed (K := K)) = 0 := by
  rw [skewSeed, map_sub, tensorRootMode_one_degreeOneVariable,
    tensorRootMode_one_degreeOneVariable, sub_self]

theorem heisenbergMode_skewSeed_pos (w : K) (a : ℤ) (ha : 0 < a) :
    heisenbergMode w a (skewSeed (K := K)) = 0 := by
  by_cases hm : IsMode a.natAbs
  · simp only [heisenbergMode, dif_pos hm, if_pos ha]
    exact (mem_heisenbergVacuum w skewSeed).mp (skewSeed_heisenbergVacuum w) ⟨a.natAbs,hm⟩
  · simp [heisenbergMode, hm]

theorem chevalleyE_skewSeed (w : K) (i : Fin 3) :
    chevalleyE w i (skewSeed (K := K)) = 0 := by
  have hc : chevalleyECoordinates w i 3 = 0 := by
    fin_cases i <;> norm_num [chevalleyECoordinates, Matrix.cons_val_two, Matrix.cons_val_three]
  simp only [chevalleyE, tensorModeEvaluate_apply, LinearMap.add_apply, LinearMap.smul_apply,
    tensorRootMode_one_skewSeed, heisenbergMode_skewSeed_pos w 1 (by decide),
    hc, zero_smul, smul_zero, add_zero]

theorem principalDerivation_skewSeed :
    principalDerivation (skewSeed (K := K)) = -skewSeed := by
  change -(degreeOperator (skewSeed (K := K))) = _
  rw [degreeOperator_eq_of_grade 1 skewSeed skewSeed_grade]
  simp

/-- The second required affine highest weight, constructed inside the same tensor Fock space. -/
theorem tensor_skew_highest_weight (w : K) (hw : w^4-w^2+1=0) :
    skewSeed (K := K) ≠ 0 ∧
    (∀ i : Fin 3, chevalleyE w i (skewSeed (K := K)) = 0) ∧
    (∀ i : Fin 3, chevalleyH w i (skewSeed (K := K)) =
      (if i=2 then (0 : K) else 1) • skewSeed) ∧
    principalDerivation (skewSeed (K := K)) = -skewSeed :=
  ⟨skewSeed_ne_zero, chevalleyE_skewSeed w, chevalleyH_skewSeed w hw,
    principalDerivation_skewSeed⟩

end KanadeRussell.Tsuchioka.Fock
