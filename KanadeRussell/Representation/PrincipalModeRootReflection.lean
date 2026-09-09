import KanadeRussell.Representation.PrincipalRootSlotEnumeration

/-! Reflections permute the counted positive principal-root slots after the
unique simple-root slot is removed. The two copies of the repeated imaginary
root remain distinct. No abstract root classification or dimension theorem
is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Representation
open AffineWeightLattice

def principalRootSimpleIndex (i : Fin 3) : Fin 28 := ![0, 1, 2] i
def principalRootPartnerIndex (i : Fin 3) : Fin 28 := ![24, 23, 25] i

def principalRootReflectionIndex (i : Fin 3) (j : Fin 28) : Fin 28 :=
  ![![24, 4, 2, 5, 1, 3, 9, 14, 8, 6, 13, 17, 15, 10, 7, 12, 19, 11, 18, 16, 22, 23, 20, 21, 0, 25, 26, 27],
    ![4, 23, 7, 6, 0, 10, 3, 2, 8, 13, 5, 11, 16, 9, 14, 20, 12, 25, 18, 22, 15, 24, 19, 1, 21, 17, 26, 27],
    ![0, 3, 25, 1, 5, 4, 6, 11, 8, 9, 12, 7, 10, 15, 17, 13, 16, 14, 18, 19, 21, 20, 23, 22, 24, 2, 26, 27]] i j

def principalRootReflectionCarry (i : Fin 3) (j : Fin 28) : ℤ :=
  if j = principalRootSimpleIndex i then -1
  else if j = principalRootPartnerIndex i then 1 else 0

theorem principalRootReflectionIndex_twice (i : Fin 3) (j : Fin 28) :
    principalRootReflectionIndex i (principalRootReflectionIndex i j) = j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem principalRootReflectionCarry_reflected (i : Fin 3) (j : Fin 28) :
    principalRootReflectionCarry i (principalRootReflectionIndex i j) =
      -principalRootReflectionCarry i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem principalRootReflectionIndex_simple (i : Fin 3) :
    principalRootReflectionIndex i (principalRootSimpleIndex i) = principalRootPartnerIndex i := by
  fin_cases i <;> rfl

theorem principalRootReflectionCarry_partner (i : Fin 3) :
    principalRootReflectionCarry i (principalRootPartnerIndex i) = 1 := by
  fin_cases i <;> decide

theorem principalRootBase_reflection (i : Fin 3) (j : Fin 28) :
    simpleReflection 0 i (principalRootBase j) =
      principalRootBase (principalRootReflectionIndex i j) +
        principalRootReflectionCarry i j • (![3, 6, 3] : RootCoefficients) := by
  fin_cases i <;> fin_cases j <;> decide

theorem principalRoot_period_reflection (i : Fin 3) (beta : RootCoefficients) (q : ℤ) :
    simpleReflection 0 i (beta+q • (![3, 6, 3] : RootCoefficients)) =
      simpleReflection 0 i beta+q • (![3, 6, 3] : RootCoefficients) := by
  have hperiod : (![3, 6, 3] : RootCoefficients) = (3 : ℤ) • marks := by decide
  rw [hperiod, smul_smul]
  unfold simpleReflection
  rw [weightLabels_add_marks]
  abel

theorem principalRootBase_degree_pos (j : Fin 28) : 0 < totalDegree (principalRootBase j) := by
  fin_cases j <;> decide

theorem principalRootBase_eq_simple_iff (i : Fin 3) (j : Fin 28) :
    principalRootBase j = Pi.single i 1 ↔ j = principalRootSimpleIndex i := by
  fin_cases i <;> fin_cases j <;> decide

theorem principalRootSlotOccupation_degree (p : ℕ × Fin 28) :
    totalDegree (principalRootSlotOccupation p) = totalDegree (principalRootBase p.2)+12*(p.1:ℤ) := by
  simp only [principalRootSlotOccupation, totalDegree, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  norm_num [Fin.sum_univ_three, Matrix.cons_val_two]
  ring

theorem principalRootSlotOccupation_eq_simple_iff (i : Fin 3) (p : ℕ × Fin 28) :
    principalRootSlotOccupation p = Pi.single i 1 ↔ p = (0, principalRootSimpleIndex i) := by
  rcases p with ⟨q, j⟩
  constructor
  · intro h
    have hd := congrArg totalDegree h
    rw [principalRootSlotOccupation_degree] at hd
    have hs : totalDegree (Pi.single i 1) = 1 := by simp [totalDegree, Pi.single_apply]
    rw [hs] at hd
    have hj := principalRootBase_degree_pos j
    have hq : q = 0 := by dsimp only at hd; omega
    subst q
    have hb : principalRootBase j = Pi.single i 1 := by
      simpa only [principalRootSlotOccupation, Nat.cast_zero, zero_smul, add_zero] using h
    rw [(principalRootBase_eq_simple_iff i j).mp hb]
  · intro h
    rw [h]
    simpa only [principalRootSlotOccupation, Nat.cast_zero, zero_smul, add_zero] using
      (principalRootBase_eq_simple_iff i (principalRootSimpleIndex i)).mpr rfl

def principalRootSlotReflection (i : Fin 3) (p : ℕ × Fin 28) : ℕ × Fin 28 :=
  (((p.1:ℤ)+principalRootReflectionCarry i p.2).toNat, principalRootReflectionIndex i p.2)

theorem principalRootSlotReflection_nonneg (i : Fin 3) (p : ℕ × Fin 28)
    (hp : p ≠ (0, principalRootSimpleIndex i)) :
    0 ≤ (p.1:ℤ)+principalRootReflectionCarry i p.2 := by
  unfold principalRootReflectionCarry
  split_ifs with hj
  · have hq : p.1 ≠ 0 := by
      intro hq
      exact hp (Prod.ext hq hj)
    omega
  · omega
  · omega

theorem principalRootSlotReflection_ne_simple (i : Fin 3) (p : ℕ × Fin 28) :
    principalRootSlotReflection i p ≠ (0, principalRootSimpleIndex i) := by
  intro heq
  have hj := congrArg Prod.snd heq
  change principalRootReflectionIndex i p.2 = principalRootSimpleIndex i at hj
  have hj' := congrArg (principalRootReflectionIndex i) hj
  rw [principalRootReflectionIndex_twice, principalRootReflectionIndex_simple] at hj'
  have hq := congrArg Prod.fst heq
  change ((p.1:ℤ)+principalRootReflectionCarry i p.2).toNat = 0 at hq
  rw [hj', principalRootReflectionCarry_partner] at hq
  omega

theorem principalRootSlotReflection_twice (i : Fin 3) (p : ℕ × Fin 28)
    (hp : p ≠ (0, principalRootSimpleIndex i)) :
    principalRootSlotReflection i (principalRootSlotReflection i p) = p := by
  apply Prod.ext
  · dsimp only [principalRootSlotReflection]
    rw [Int.toNat_of_nonneg (principalRootSlotReflection_nonneg i p hp),
      principalRootReflectionCarry_reflected]
    simp
  · exact principalRootReflectionIndex_twice i p.2

def principalRootSlotReflectionEquiv (i : Fin 3) :
    {p : ℕ × Fin 28 // p ≠ (0, principalRootSimpleIndex i)} ≃
      {p : ℕ × Fin 28 // p ≠ (0, principalRootSimpleIndex i)} where
  toFun p := ⟨principalRootSlotReflection i p.val, principalRootSlotReflection_ne_simple i p.val⟩
  invFun p := ⟨principalRootSlotReflection i p.val, principalRootSlotReflection_ne_simple i p.val⟩
  left_inv p := Subtype.ext (principalRootSlotReflection_twice i p.val p.property)
  right_inv p := Subtype.ext (principalRootSlotReflection_twice i p.val p.property)

theorem principalRootSlotOccupation_reflection (i : Fin 3) (p : ℕ × Fin 28)
    (hp : p ≠ (0, principalRootSimpleIndex i)) :
    principalRootSlotOccupation (principalRootSlotReflection i p) =
      simpleReflection 0 i (principalRootSlotOccupation p) := by
  unfold principalRootSlotOccupation
  rw [principalRoot_period_reflection, principalRootBase_reflection]
  simp only [principalRootSlotReflection, Int.toNat_of_nonneg
    (principalRootSlotReflection_nonneg i p hp), add_smul]
  abel

end KanadeRussell.Representation
