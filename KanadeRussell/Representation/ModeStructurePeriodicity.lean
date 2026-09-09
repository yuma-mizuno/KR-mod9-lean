import KanadeRussell.Tsuchioka.AffineChevalley

/-! Periodicity modulo twelve of the noncentral principal-mode structure constants.
The central coordinate is deliberately excluded because its coefficient depends on the mode number. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem isMode_natAbs_iff_residue (a : ℤ) :
    IsMode a.natAbs ↔ a % 12 = 1 ∨ a % 12 = 5 ∨ a % 12 = 7 ∨ a % 12 = 11 := by
  have ha : (a.natAbs : ℤ) = |a| := Int.natCast_natAbs a
  rw [IsMode]
  by_cases h : 0 ≤ a
  · rw [abs_of_nonneg h] at ha
    omega
  · rw [abs_of_neg (by omega)] at ha
    omega

theorem tensorHeisenbergPairing_residue (w : K) (hw : w^4-w^2+1=0) (a : ℤ) :
    tensorHeisenbergPairing w a =
      if a % 12 = 1 ∨ a % 12 = 11 then -w^3/6+w/3+1/2
      else if a % 12 = 5 ∨ a % 12 = 7 then w^3/6-w/3+1/2 else 0 := by
  have ha : (a.natAbs : ℤ) = |a| := Int.natCast_natAbs a
  have hc := contraction_fin w hw ⟨a.natAbs % 12, Nat.mod_lt _ (by decide)⟩
  rw [tensorHeisenbergPairing, contraction_mod_twelve w hw, hc]
  simp only [Fock.spectralValue, IsMode]
  by_cases h : 0 ≤ a
  · rw [abs_of_nonneg h] at ha
    split_ifs <;> first | rfl | exfalso; omega
  · rw [abs_of_neg (by omega)] at ha
    split_ifs <;> first | rfl | exfalso; omega

theorem tensorHeisenbergPairing_eq_of_mod (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (hab : a % 12 = b % 12) :
    tensorHeisenbergPairing w a = tensorHeisenbergPairing w b := by
  simp only [tensorHeisenbergPairing_residue w hw, hab]

theorem tensorModeStructure_noncentral_eq_of_mod (w : K) (hw : w^4-w^2+1=0)
    (a b a' b' : ℤ) (ha : a % 12 = a' % 12) (hb : b % 12 = b' % 12)
    (r s t : Fin 3) :
    tensorModeStructure w a b r.castSucc s.castSucc t.castSucc =
      tensorModeStructure w a' b' r.castSucc s.castSucc t.castSucc := by
  have hpa := tensorHeisenbergPairing_eq_of_mod w hw a a' ha
  have hpb := tensorHeisenbergPairing_eq_of_mod w hw b b' hb
  have hm : IsMode (a+b).natAbs = IsMode (a'+b').natAbs := by
    apply propext
    rw [isMode_natAbs_iff_residue, isMode_natAbs_iff_residue]
    have hab : (a+b)%12 = (a'+b')%12 := by omega
    rw [hab]
  have hs : (-1 : K)^a = (-1 : K)^a' := by
    rw [← root_six_phase w hw, ← root_six_phase w hw]
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  have hp0 : w ^ (-2*a+2*b) = w ^ (-2*a'+2*b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp0
  have hp1 : w ^ (2*a-2*b) = w ^ (2*a'-2*b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp1
  have hp2 : w ^ (4*a+9*b) = w ^ (4*a'+9*b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp2
  have hp3 : w ^ (9*a+4*b) = w ^ (9*a'+4*b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp3
  have hp4 : w ^ (a+3*b) = w ^ (a'+3*b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp4
  have hp5 : w ^ (-a+8*b) = w ^ (-a'+8*b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp5
  have hp6 : w ^ (-6*a+5*b) = w ^ (-6*a'+5*b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp6
  have hp7 : w ^ (7*a+7*b) = w ^ (7*a'+7*b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp7
  have hp8 : w ^ (b+3*a) = w ^ (b'+3*a') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp8
  have hp9 : w ^ (-b+8*a) = w ^ (-b'+8*a') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp9
  have hp10 : w ^ (-6*b+5*a) = w ^ (-6*b'+5*a') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp10
  have hp11 : w ^ (7*b+7*a) = w ^ (7*b'+7*a') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp11
  have hp12 : w ^ (5*a+6*b) = w ^ (5*a'+6*b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp12
  have hp13 : w ^ (a+b) = w ^ (a'+b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp13
  have hp14 : w ^ (-a) = w ^ (-a') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp14
  have hp15 : w ^ (-b) = w ^ (-b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp15
  have hp16 : w ^ (a) = w ^ (a') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp16
  have hp17 : w ^ (b) = w ^ (b') := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  try simp only [neg_mul] at hp17
  fin_cases r <;> fin_cases s <;> fin_cases t <;>
    norm_num [tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, RootData.rootWeight_second, Fin.val_zero, Fin.val_one] <;>
    simp only [hpa, hpb, hm, hs, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17] <;> simp

end KanadeRussell.Representation
