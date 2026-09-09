import KanadeRussell.Representation.PrincipalModeEigenframe

/-! An inactive dummy slot has zero dual coordinates even though its full
invertible frame retains a dummy basis vector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K]

theorem principalWeightReconstruction_row_of_inactive (w : K) (n : Fin 12) (s : Fin 3)
    (hs : ¬ principalWeightSlotActive n s) :
    principalWeightReconstruction w n s = ![0, 0, 1] := by
  have hs2 : s = 2 := Classical.not_not.mp (fun hn => hs (Or.inl hn))
  subst s
  fin_cases n
  all_goals try (exfalso; apply hs; right; decide)
  all_goals funext r; fin_cases r <;> rfl

theorem principalDualWeightCoordinates_eq_zero_of_inactive (w : K) (a : ℤ) (n : Fin 12)
    (han : a % 12 = ((n.val+1 : ℕ) : ℤ) % 12) (s : Fin 3)
    (hs : ¬ principalWeightSlotActive n s) :
    principalDualWeightCoordinates w a n s = 0 := by
  have hm : ¬ IsMode a.natAbs := by
    intro ha
    apply hs
    right
    have h := (isMode_natAbs_iff_residue a).mp ha
    rw [han] at h
    have hn := (isMode_natAbs_iff_residue ((n.val+1 : ℕ) : ℤ)).mpr h
    simpa only [Int.natAbs_natCast] using hn
  have hrow := principalWeightReconstruction_row_of_inactive w n s hs
  funext r
  change (modePairingCoefficient w a r)⁻¹ * principalWeightReconstruction w n s r = 0
  rw [congrFun hrow r]
  fin_cases r <;>
    simp [modePairingCoefficient, tensorHeisenbergPairing, hm, Matrix.cons_val_two]

end KanadeRussell.Representation
