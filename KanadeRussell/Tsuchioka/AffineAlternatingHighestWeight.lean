import KanadeRussell.Tsuchioka.TensorAlternatingWeights
import KanadeRussell.Tsuchioka.AffineHighestWeight

/-! The alternating degree-three tensor polynomial has affine highest weight
Lambda_2 and principal derivation eigenvalue -3. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

theorem tensorFirstRoot_zero_alternatingSeed (w : K) (hw : w^4-w^2+1=0) :
    tensorRootMode w (RootData.simpleRoot 0) 0 (alternatingSeed (K := K)) =
      (-w^3/2+w+3/4) • alternatingSeed := by
  rw [tensorRootMode_zero_alternatingSeed, RootData.rootWeight_first,
    RootData.rootWeight_first, contraction_one w hw]
  congr 1
  grind only

theorem tensorSecondRoot_zero_alternatingSeed (w : K) (hw : w^4-w^2+1=0) :
    tensorRootMode w (RootData.simpleRoot 1) 0 (alternatingSeed (K := K)) =
      (w^3/2-w+3/4) • alternatingSeed := by
  rw [tensorRootMode_zero_alternatingSeed, RootData.rootWeight_second,
    RootData.rootWeight_second]
  have hc : contraction w 1 * (w^3-w^2) * ((w ^ (-1 : ℤ))^3-(w ^ (-1 : ℤ))^2) =
      w^3/6-w/3+1/2 := by
    rw [contraction_one w hw, Scalar.zpow_phasePolynomial w hw (-1)]
    norm_num [Scalar.phasePolynomial]
    grind only
  congr 1
  calc
    _ = 1/4 - 3 * (contraction w 1 * (w^3-w^2) *
      ((w ^ (-1 : ℤ))^3-(w ^ (-1 : ℤ))^2)) +
      6 * (contraction w 1 * (w^3-w^2) *
      ((w ^ (-1 : ℤ))^3-(w ^ (-1 : ℤ))^2))^2 := by ring
    _ = _ := by rw [hc]; grind only

theorem chevalleyH_alternatingSeed (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    chevalleyH w i (alternatingSeed (K := K)) =
      (if i = 2 then (1 : K) else 0) • alternatingSeed := by
  have hc : chevalleyHCoordinates w i 0 * (-w^3/2+w+3/4) +
      chevalleyHCoordinates w i 1 * (w^3/2-w+3/4) +
      chevalleyHCoordinates w i 3 = (if i = 2 then (1 : K) else 0) := by
    fin_cases i <;> norm_num [chevalleyHCoordinates,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only
  simp only [chevalleyH, tensorModeEvaluate_apply, LinearMap.add_apply,
    LinearMap.smul_apply, tensorFirstRoot_zero_alternatingSeed w hw,
    tensorSecondRoot_zero_alternatingSeed w hw, heisenbergMode_zero,
    LinearMap.zero_apply, smul_zero, add_zero, Module.End.one_apply, smul_smul]
  rw [← add_smul, ← add_smul, hc]

theorem heisenbergMode_alternatingSeed_pos (w : K) (a : ℤ) (ha : 0 < a) :
    heisenbergMode w a (alternatingSeed (K := K)) = 0 := by
  by_cases hm : IsMode a.natAbs
  · simp only [heisenbergMode, dif_pos hm, if_pos ha]
    exact (mem_heisenbergVacuum w alternatingSeed).mp
      (alternatingSeed_heisenbergVacuum w) ⟨a.natAbs,hm⟩
  · simp [heisenbergMode, hm]

theorem chevalleyE_alternatingSeed (w : K) (i : Fin 3) :
    chevalleyE w i (alternatingSeed (K := K)) = 0 := by
  have hc : chevalleyECoordinates w i 3 = 0 := by
    fin_cases i <;> norm_num [chevalleyECoordinates, Matrix.cons_val_two, Matrix.cons_val_three]
  simp only [chevalleyE, tensorModeEvaluate_apply, LinearMap.add_apply, LinearMap.smul_apply,
    tensorRootMode_one_alternatingSeed, heisenbergMode_alternatingSeed_pos w 1 (by decide),
    hc, zero_smul, smul_zero, add_zero]

theorem principalDerivation_alternatingSeed :
    principalDerivation (alternatingSeed (K := K)) = (-3 : K) • alternatingSeed := by
  change -(degreeOperator (alternatingSeed (K := K))) = _
  rw [degreeOperator_eq_of_grade 3 alternatingSeed alternatingSeed_grade]
  simp

/-- The third required affine highest weight, with a concrete nonzero vacuum seed. -/
theorem tensor_alternating_highest_weight (w : K) (hw : w^4-w^2+1=0) :
    alternatingSeed (K := K) ≠ 0 ∧
    (∀ i : Fin 3, chevalleyE w i (alternatingSeed (K := K)) = 0) ∧
    (∀ i : Fin 3, chevalleyH w i (alternatingSeed (K := K)) =
      (if i=2 then (1 : K) else 0) • alternatingSeed) ∧
    principalDerivation (alternatingSeed (K := K)) = (-3 : K) • alternatingSeed :=
  ⟨alternatingSeed_ne_zero, chevalleyE_alternatingSeed w,
    chevalleyH_alternatingSeed w hw, principalDerivation_alternatingSeed⟩

end KanadeRussell.Tsuchioka.Fock
