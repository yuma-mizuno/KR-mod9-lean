import KanadeRussell.Tsuchioka.TensorModeBrackets

/-! A four-coordinate bridge for the concrete tensor mode brackets.
The coordinates record the two root families, the principal Heisenberg mode,
and the identity. Evaluation is a proved Lie-bracket calculation. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

attribute [local instance] LieRing.ofAssociativeRing

open RootData (simpleRoot rootWeight rootWeight_first)
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

noncomputable def tensorModeBasis (w : K) (a : ℤ) : Fin 4 → Module.End K (Space K) :=
  ![tensorRootMode w (simpleRoot 0) a, tensorRootMode w (simpleRoot 1) a,
    heisenbergMode w a, 1]

noncomputable def tensorModeEvaluate (w : K) (a : ℤ) :
    (Fin 4 → K) →ₗ[K] Module.End K (Space K) where
  toFun v := ∑ r, v r • tensorModeBasis w a r
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [mul_smul, Finset.smul_sum]

theorem tensorModeEvaluate_apply (w : K) (a : ℤ) (v : Fin 4 → K) :
    tensorModeEvaluate w a v =
      v 0 • tensorRootMode w (simpleRoot 0) a +
      v 1 • tensorRootMode w (simpleRoot 1) a +
      v 2 • heisenbergMode w a + v 3 • (1 : Module.End K (Space K)) := by
  simp [tensorModeEvaluate, tensorModeBasis, Fin.sum_univ_succ, add_assoc]

/-- Remove a coordinate whose actual Heisenberg operator is zero. -/
def normalizeTensorCoordinates (a : ℤ) (v : Fin 4 → K) : Fin 4 → K :=
  ![v 0, v 1, if IsMode a.natAbs then v 2 else 0, v 3]

theorem tensorModeEvaluate_normalize (w : K) (a : ℤ) (v : Fin 4 → K) :
    tensorModeEvaluate w a (normalizeTensorCoordinates a v) =
      tensorModeEvaluate w a v := by
  by_cases ha : IsMode a.natAbs
  · simp [tensorModeEvaluate_apply, normalizeTensorCoordinates, ha]
  · simp [tensorModeEvaluate_apply, normalizeTensorCoordinates, ha,
      heisenbergMode_not_mode w a ha]

noncomputable def tensorHeisenbergPairing (w : K) (a : ℤ) : K :=
  if IsMode a.natAbs then contraction w a.natAbs else 0

noncomputable def tensorModeRawStructure (w : K) (a b : ℤ) (r s : Fin 4) : Fin 4 → K :=
  match r.val, s.val with
  | 0, 0 => ![
      Coefficients.pCoeff w * (w ^ (-2*a+2*b) - w ^ (2*a-2*b)) / 12,
      Scalar.rootSecondResidue w * (w ^ (4*a+9*b) - w ^ (9*a+4*b)) / 12,
      -(Scalar.cPrime w * (-1 : K) ^ a / 6),
      if a+b=0 then Scalar.cPrime w * (a : K) * (-1 : K) ^ a / 24 else 0]
  | 0, 1 => ![
      Coefficients.pCoeff (-w) * (w ^ (a+3*b) - w ^ (-a+8*b)) / 12,
      Coefficients.pCoeff w * (w ^ (-6*a+5*b) - w ^ (7*a+7*b)) / 12, 0, 0]
  | 0, 2 => ![-tensorHeisenbergPairing w b, 0, 0, 0]
  | 1, 0 => ![
      -(Coefficients.pCoeff (-w) * (w ^ (b+3*a) - w ^ (-b+8*a)) / 12),
      -(Coefficients.pCoeff w * (w ^ (-6*b+5*a) - w ^ (7*b+7*a)) / 12), 0, 0]
  | 1, 1 => ![
      Scalar.rootSecondResidue (-w) * (w ^ (-6*a+5*b) - w ^ (5*a+6*b)) / 12,
      Coefficients.pCoeff (-w) * (w ^ (-2*a+2*b) - w ^ (2*a-2*b)) / 12,
      -(Scalar.cPrime (-w) * (-1 : K) ^ a * rootWeight (w ^ (a+b)) (simpleRoot 1) / 6),
      if a+b=0 then Scalar.cPrime (-w) * (a : K) * (-1 : K) ^ a / 24 else 0]
  | 1, 2 => ![0, -(tensorHeisenbergPairing w b * rootWeight (w ^ (-b)) (simpleRoot 1)), 0, 0]
  | 2, 0 => ![tensorHeisenbergPairing w a, 0, 0, 0]
  | 2, 1 => ![0, tensorHeisenbergPairing w a * rootWeight (w ^ (-a)) (simpleRoot 1), 0, 0]
  | 2, 2 => ![0, 0, 0,
      if IsMode a.natAbs ∧ a+b=0 then (a : K) * contraction w a.natAbs / 4 else 0]
  | _, _ => 0

noncomputable def tensorModeStructure (w : K) (a b : ℤ) (r s : Fin 4) : Fin 4 → K :=
  normalizeTensorCoordinates (a+b) (tensorModeRawStructure w a b r s)

private theorem tensorHeisenbergPairing_mul (w : K) (a : ℤ) (x : K) :
    tensorHeisenbergPairing w a * x =
      if IsMode a.natAbs then contraction w a.natAbs * x else 0 := by
  by_cases ha : IsMode a.natAbs <;> simp [tensorHeisenbergPairing, ha]

set_option maxHeartbeats 1200000 in
/-- Every coordinate bracket is the bracket of the constructed polynomial operators. -/
theorem tensorModeBasis_lie (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (r s : Fin 4) :
    ⁅tensorModeBasis w a r, tensorModeBasis w b s⁆ =
      tensorModeEvaluate w (a+b) (tensorModeStructure w a b r s) := by
  rw [tensorModeStructure, tensorModeEvaluate_normalize]
  fin_cases r <;> fin_cases s <;>
    norm_num [tensorModeBasis, tensorModeRawStructure, tensorModeEvaluate_apply,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons,
      Pi.zero_apply, zero_smul, add_zero, zero_add]
  · rw [tensorFirstRoot_lie w hw]
    split_ifs <;> simp only [neg_mul] <;> module
  · simpa only [neg_mul] using tensorMixedRoot_lie w hw a b
  · rw [← lie_skew, heisenbergMode_tensorRootMode_lie]
    by_cases hb : IsMode b.natAbs <;>
      simp [rootWeight_first, tensorHeisenbergPairing, hb, add_comm] <;> module
  · simp [Ring.lie_def]
  · rw [← lie_skew, tensorMixedRoot_lie w hw]
    simp only [add_comm b a, neg_mul]
    module
  · rw [tensorSecondRoot_lie w hw]
    split_ifs <;> simp only [zero_smul, add_zero, neg_mul, RootData.rootWeight_second] <;> module
  · rw [← lie_skew, heisenbergMode_tensorRootMode_lie, ← tensorHeisenbergPairing_mul]
    simp only [add_comm b a, RootData.rootWeight_second, zpow_neg]
    module
  · simp [Ring.lie_def]
  · rw [heisenbergMode_tensorRootMode_lie]
    simp [rootWeight_first, tensorHeisenbergPairing, add_comm]
  · rw [heisenbergMode_tensorRootMode_lie, ← tensorHeisenbergPairing_mul]
    simp [add_comm]
  · simpa only [ite_smul, zero_smul] using heisenbergMode_lie w a b
  · simp [Ring.lie_def]
  · simp [Ring.lie_def]
  · simp [Ring.lie_def]
  · simp [Ring.lie_def]

/-- Bilinear coordinate calculation of an arbitrary finite mode combination. -/
noncomputable def tensorCoordinateBracket (w : K) (a b : ℤ)
    (u v : Fin 4 → K) : Fin 4 → K :=
  ∑ r, ∑ s, (u r * v s) • tensorModeStructure w a b r s

theorem tensorModeEvaluate_lie (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (u v : Fin 4 → K) :
    ⁅tensorModeEvaluate w a u, tensorModeEvaluate w b v⁆ =
      tensorModeEvaluate w (a+b) (tensorCoordinateBracket w a b u v) := by
  have hbilin (c d : K) (x y : Module.End K (Space K)) :
      ⁅c • x, d • y⁆ = (c*d) • ⁅x,y⁆ := by
    simp only [Ring.lie_def, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    module
  change ⁅∑ r, u r • tensorModeBasis w a r, ∑ s, v s • tensorModeBasis w b s⁆ = _
  rw [sum_lie_sum]
  simp only [tensorCoordinateBracket, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [hbilin, tensorModeBasis_lie w hw]

end KanadeRussell.Tsuchioka.Fock
