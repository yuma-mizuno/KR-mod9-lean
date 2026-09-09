import KanadeRussell.Representation.ModeCasimirCancellation

/-! Signed opposite-mode brackets: periodic noncentral coordinates and the
exact linear dependence of the central coordinate on the mode number. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

/-- The central coefficient includes the zero mode and inactive Heisenberg slots. -/
theorem tensorModeStructure_opposite_central (w : K) (a : ℤ) (r t : Fin 3) :
    tensorModeStructure w a (-a) r.castSucc t.castSucc 3 =
      if r = t then (3*(a : K)/4) * modePairingCoefficient w a r else 0 := by
  fin_cases r <;> fin_cases t <;>
    norm_num [tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      modePairingCoefficient, tensorHeisenbergPairing, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;>
    (try split_ifs) <;> ring

/-- Every noncentral coordinate is periodic, also for signed opposite modes. -/
theorem tensorModeStructure_opposite_noncentral_eq_of_mod
    (w : K) (hw : w^4-w^2+1=0) (a b : ℤ) (hab : a%12=b%12) (r t u : Fin 3) :
    tensorModeStructure w a (-a) r.castSucc t.castSucc u.castSucc =
      tensorModeStructure w b (-b) r.castSucc t.castSucc u.castSucc := by
  apply tensorModeStructure_noncentral_eq_of_mod w hw a (-a) b (-b) hab
  omega

/-- Full coordinate transport: only the central entry changes. -/
theorem tensorModeStructure_opposite_eq_of_mod
    (w : K) (hw : w^4-w^2+1=0) (a b : ℤ) (hab : a%12=b%12) (r t : Fin 3) :
    tensorModeStructure w a (-a) r.castSucc t.castSucc =
      tensorModeStructure w b (-b) r.castSucc t.castSucc +
        ![0, 0, 0, if r = t then (3*((a-b : ℤ) : K)/4) *
          modePairingCoefficient w b r else 0] := by
  ext u
  obtain ⟨u, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last u
  · rw [Pi.add_apply, tensorModeStructure_opposite_noncentral_eq_of_mod w hw a b hab]
    fin_cases u <;> simp
  · have hlast : (Fin.last 3 : Fin 4) = 3 := rfl
    rw [hlast, Pi.add_apply, tensorModeStructure_opposite_central,
      tensorModeStructure_opposite_central, modePairingCoefficient_eq_of_mod w hw a b hab]
    norm_num [Matrix.cons_val_three]
    split_ifs <;> ring

/-- Clearing the mode number gives transport without any nonzero pairing hypothesis. -/
theorem tensorModeStructure_opposite_central_scale
    (w : K) (hw : w^4-w^2+1=0) (a b : ℤ) (hab : a%12=b%12) (r t : Fin 3) :
    (b : K) * tensorModeStructure w a (-a) r.castSucc t.castSucc 3 =
      (a : K) * tensorModeStructure w b (-b) r.castSucc t.castSucc 3 := by
  rw [tensorModeStructure_opposite_central, tensorModeStructure_opposite_central,
    modePairingCoefficient_eq_of_mod w hw a b hab]
  split_ifs <;> ring

end KanadeRussell.Representation
