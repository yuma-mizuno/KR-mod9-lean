import KanadeRussell.Representation.PrincipalModeWeights
import KanadeRussell.Representation.PrincipalModeCartanPairing
import KanadeRussell.Representation.NormalOrderedBasisChange
import KanadeRussell.Representation.DualEigenbasis

/-! Invertible coordinate frames include a dummy column for an inactive
Heisenberg slot. Its Cartan eigenvalue is zero and its actual mode vanishes.
This reconciles the frame with the active eigenoperators and their duals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

noncomputable def principalWeightFrame (w : K) (n : Fin 12) : Matrix (Fin 3) (Fin 3) K :=
  ![principalWeightMatrix1 w, principalWeightMatrix2 w, principalWeightMatrix3 w, principalWeightMatrix4 w, principalWeightMatrix5 w, principalWeightMatrix6 w, principalWeightMatrix7 w, principalWeightMatrix8 w, principalWeightMatrix9 w, principalWeightMatrix10 w, principalWeightMatrix11 w, principalWeightMatrix12 w] n

def principalWeightSlotActive (n : Fin 12) (s : Fin 3) : Prop :=
  s ≠ 2 ∨ IsMode (n.val+1)

instance (n : Fin 12) (s : Fin 3) : Decidable (principalWeightSlotActive n s) :=
  inferInstanceAs (Decidable (s ≠ 2 ∨ IsMode (n.val+1)))

noncomputable def principalFrameEigenvalue (n : Fin 12) (i s : Fin 3) : K :=
  if principalWeightSlotActive n s then
    ∑ j, (affineCartanMatrix i j : K) * (principalWeightOccupation n s j : K)
  else 0

theorem principalWeightFrame_mul_reconstruction (w : K) (hw : w^4-w^2+1=0) (n : Fin 12) :
    principalWeightFrame w n * principalWeightReconstruction w n = 1 := by
  fin_cases n
  · exact principalWeightMatrix1_mul_inverse w hw
  · exact principalWeightMatrix2_mul_inverse w hw
  · exact principalWeightMatrix3_mul_inverse w hw
  · exact principalWeightMatrix4_mul_inverse w hw
  · exact principalWeightMatrix5_mul_inverse w hw
  · exact principalWeightMatrix6_mul_inverse w hw
  · exact principalWeightMatrix7_mul_inverse w hw
  · exact principalWeightMatrix8_mul_inverse w hw
  · exact principalWeightMatrix9_mul_inverse w hw
  · exact principalWeightMatrix10_mul_inverse w hw
  · exact principalWeightMatrix11_mul_inverse w hw
  · exact principalWeightMatrix12_mul_inverse w hw

omit [CharZero K] in
theorem principalWeightFrame_column (w : K) (n : Fin 12) (s : Fin 3) :
    (fun r => principalWeightFrame w n r s) =
      if principalWeightSlotActive n s then principalWeightCoordinates w n s
      else ![0, 0, 1] := by
  fin_cases n <;> fin_cases s <;> funext r <;> fin_cases r <;> rfl

omit [CharZero K] in
theorem principalWeightCoordinates_eq_zero_of_inactive (w : K) (n : Fin 12) (s : Fin 3)
    (hs : ¬ principalWeightSlotActive n s) : principalWeightCoordinates w n s = 0 := by
  have hs2 : s = 2 := Classical.not_not.mp (fun hn => hs (Or.inl hn))
  subst s
  fin_cases n
  all_goals simp_all [principalWeightSlotActive, IsMode, principalWeightCoordinates]

omit [CharZero K] in
/-- The unused Heisenberg input column is actually zero in the Cartan matrix. -/
theorem principalCartanMatrix_inactive_column (w : K) (a : ℤ)
    (ha : ¬ IsMode a.natAbs) (i t : Fin 3) : principalCartanMatrix w a i t 2 = 0 := by
  dsimp [principalCartanMatrix]
  apply Finset.sum_eq_zero
  intro s hs
  have hz : tensorModeStructure w 0 a s.castSucc (2 : Fin 4) t.castSucc = 0 := by
    fin_cases s <;> fin_cases t <;>
      norm_num [tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
        tensorHeisenbergPairing, ha, Fin.castSucc_mk, Matrix.cons_val_zero',
        Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three]
  rw [hz, mul_zero]

omit [CharZero K] in
theorem principalCartanMatrix_inactive_mulVec (w : K) (a : ℤ)
    (ha : ¬ IsMode a.natAbs) (i : Fin 3) :
    (principalCartanMatrix w a i).mulVec ![0, 0, 1] = 0 := by
  ext t
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using
    principalCartanMatrix_inactive_column w a ha i t

theorem principalWeightFrame_eigen (w : K) (hw : w^4-w^2+1=0) (n : Fin 12) (i : Fin 3) :
    principalCartanMatrix w (n.val+1) i * principalWeightFrame w n =
      principalWeightFrame w n * Matrix.diagonal (principalFrameEigenvalue (K := K) n i) := by
  ext t s
  have hc : (principalCartanMatrix w (n.val+1) i).mulVec
      (fun r => principalWeightFrame w n r s) =
      principalFrameEigenvalue (K := K) n i s • (fun r => principalWeightFrame w n r s) := by
    rw [principalWeightFrame_column]
    by_cases hs : principalWeightSlotActive n s
    · simpa only [if_pos hs, principalFrameEigenvalue] using
        principalWeightCoordinates_eigen w hw n s i
    · have hm : ¬ IsMode (n.val+1) := fun hm => hs (Or.inr hm)
      have ha : ¬ IsMode ((n.val+1 : ℕ) : ℤ).natAbs := by simpa only [Int.natAbs_natCast] using hm
      simpa only [if_neg hs, principalFrameEigenvalue, zero_smul, Nat.cast_add, Nat.cast_one] using
        principalCartanMatrix_inactive_mulVec w ((n.val+1 : ℕ) : ℤ) ha i
  have h := congrFun hc t
  change (principalCartanMatrix w (n.val+1) i * principalWeightFrame w n) t s =
    principalFrameEigenvalue (K := K) n i s * principalWeightFrame w n t s at h
  rw [Matrix.mul_diagonal, h, mul_comm]

private theorem isMode_index_of_congruent (a : ℤ) (n : Fin 12)
    (han : a % 12 = ((n.val+1 : ℕ) : ℤ) % 12) :
    IsMode a.natAbs ↔ IsMode (n.val+1) := by
  rw [isMode_natAbs_iff_residue, han]
  have h := isMode_natAbs_iff_residue ((n.val+1 : ℕ) : ℤ)
  simpa only [Int.natAbs_natCast] using h.symm

theorem principalWeightFrame_combination (w : K) (a : ℤ) (n : Fin 12)
    (han : a % 12 = ((n.val+1 : ℕ) : ℤ) % 12) (s : Fin 3) :
    principalModeCombination w a (fun r => principalWeightFrame w n r s) =
      principalModeCombination w a (principalWeightCoordinates w n s) := by
  rw [principalWeightFrame_column]
  by_cases hs : principalWeightSlotActive n s
  · rw [if_pos hs]
  · rw [if_neg hs, principalWeightCoordinates_eq_zero_of_inactive w n s hs, map_zero]
    have hm : ¬ IsMode a.natAbs := fun h =>
      hs (Or.inr ((isMode_index_of_congruent a n han).mp h))
    rw [principalModeCombination_eq_of_inactive w a hm]
    have hz : (![0, 0, 0] : Fin 3 → K) = 0 := by ext i; fin_cases i <;> rfl
    change principalModeCombination w a ![0, 0, 0] = 0
    rw [hz, map_zero]

noncomputable def principalDualWeightCoordinates (w : K) (a : ℤ) (n : Fin 12)
    (s : Fin 3) : Fin 3 → K :=
  fun r => (modePairingCoefficient w a r)⁻¹ * principalWeightReconstruction w n s r

/-- Pairing adjointness supplies the dual negative coordinates for every signed
index in the same residue class as the positive frame. -/
theorem principalDualWeightCoordinates_eigen (w : K) (hw : w^4-w^2+1=0)
    (a : ℤ) (n : Fin 12) (han : a % 12 = ((n.val+1 : ℕ) : ℤ) % 12) (i s : Fin 3) :
    (principalCartanMatrix w (-a) i).mulVec (principalDualWeightCoordinates w a n s) =
      (-principalFrameEigenvalue (K := K) n i s) • principalDualWeightCoordinates w a n s := by
  have hpositive : principalCartanMatrix w a i * principalWeightFrame w n =
      principalWeightFrame w n * Matrix.diagonal (principalFrameEigenvalue (K := K) n i) := by
    rw [principalCartanMatrix_eq_of_mod w hw a ((n.val+1 : ℕ) : ℤ) han]
    exact principalWeightFrame_eigen w hw n i
  exact dualEigenbasis_weightedRow (principalCartanMatrix w a i)
    (principalCartanMatrix w (-a) i) (principalWeightFrame w n)
    (principalWeightReconstruction w n) (principalFrameEigenvalue n i)
    (fun r => (modePairingCoefficient w a r)⁻¹)
    (principalWeightFrame_mul_reconstruction w hw n) hpositive
    (principalCartanMatrix_inversePairing w hw a i) s

/-- The original normal-ordered quadratic summand is exactly the sum over
positive eigenmodes and their paired negative coordinates. -/
theorem normalOrderedMode_eq_weight_sum (w : K) (hw : w^4-w^2+1=0)
    (a : ℤ) (n : Fin 12) (han : a % 12 = ((n.val+1 : ℕ) : ℤ) % 12) :
    normalOrderedMode w a = ∑ s : Fin 3,
      principalModeCombination w (-a) (principalDualWeightCoordinates w a n s) *
      principalModeCombination w a (principalWeightCoordinates w n s) := by
  rw [← normalOrderedMode_basisChange w a (principalWeightFrame w n)
    (principalWeightReconstruction w n) (principalWeightFrame_mul_reconstruction w hw n)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [principalWeightFrame_combination w a n han s]
  rfl

end KanadeRussell.Representation
