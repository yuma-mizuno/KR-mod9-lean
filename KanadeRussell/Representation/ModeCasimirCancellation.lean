import KanadeRussell.Representation.PrincipalModePairing
import KanadeRussell.Representation.ModeStructurePeriodicity

/-! Exact bulk cancellation of the actual principal-mode Casimir sum.
The finite residue certificates are checked using the cyclotomic equation. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

def inverseModePairingCoefficient (w : K) (n : ℤ) : Fin 3 → K :=
  ![(12*w^3-24*w+21)*(-1 : K)^n,
    (-12*w^3+24*w+21)*(-1 : K)^n,
    if n%12=1 ∨ n%12=11 then 3*w^3-6*w+9
    else if n%12=5 ∨ n%12=7 then -3*w^3+6*w+9 else 0]

theorem modePairingCoefficient_inv (w : K) (hw : w^4-w^2+1=0) (n : ℤ) (r : Fin 3) :
    (modePairingCoefficient w n r)⁻¹ = inverseModePairingCoefficient w n r := by
  have hs : (-1 : K)^n * (-1 : K)^n = 1 := by
    rw [← mul_zpow]
    norm_num
  have h0 : Scalar.cPrime w * (12*w^3-24*w+21) = 18 := by
    dsimp [Scalar.cPrime]
    linear_combination (864-288*w^2)*hw
  have h1 : Scalar.cPrime (-w) * (-12*w^3+24*w+21) = 18 := by
    dsimp [Scalar.cPrime]
    linear_combination (864-288*w^2)*hw
  have hp (c p : K) (h : c*p=18) : (c*(-1 : K)^n/18)⁻¹ = p*(-1 : K)^n := by
    apply inv_eq_of_mul_eq_one_right
    calc
      (c*(-1 : K)^n/18)*(p*(-1 : K)^n) = (c*p/18)*((-1 : K)^n*(-1 : K)^n) := by ring
      _ = 1 := by rw [h, hs]; norm_num
  fin_cases r
  · exact hp _ _ h0
  · exact hp _ _ h1
  · change (tensorHeisenbergPairing w n / 3)⁻¹ =
      if n%12=1 ∨ n%12=11 then 3*w^3-6*w+9
      else if n%12=5 ∨ n%12=7 then -3*w^3+6*w+9 else 0
    rw [tensorHeisenbergPairing_residue w hw]
    split_ifs
    · apply inv_eq_of_mul_eq_one_right
      linear_combination (1/2-w^2/6)*hw
    · apply inv_eq_of_mul_eq_one_right
      linear_combination (1/2-w^2/6)*hw
    · simp

theorem modePairingCoefficient_eq_of_mod (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (hab : a%12=b%12) (r : Fin 3) :
    modePairingCoefficient w a r = modePairingCoefficient w b r := by
  have hs : (-1 : K)^a = (-1 : K)^b := by
    rw [← root_six_phase w hw, ← root_six_phase w hw]
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  simp only [modePairingCoefficient, hs, tensorHeisenbergPairing_eq_of_mod w hw a b hab]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
local macro "mode_bulk_reduce " w:term ", " hw:term : tactic =>
  `(tactic| norm_num [modePairingCoefficient_inv $w $hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecHead, Matrix.vecTail, isMode_natAbs_iff_residue, IsMode,
      tensorHeisenbergPairing_residue $w $hw, RootData.rootWeight_second,
      Scalar.zpow_phasePolynomial $w $hw, Scalar.phasePolynomial, Int.toNat,
      Scalar.cPrime, Coefficients.pCoeff, Scalar.rootSecondResidue])

private theorem modeBulkCoefficient_fin_0 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((0 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((0 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (0 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(0 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^5 + 112*w^4 - 84*w^3) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^3 + 196*w^2 - 28*w - 84) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^5 + 196*w^4 + 28*w^3 - 84*w^2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^5 + 112*w^4 + 84*w^3) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^2/2 - 285/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-95*w^11/2 + 285*w^9 - 95*w^8/2 - 570*w^7 + 475*w^6/2 + 475*w^5 - 665*w^4/2 - 285*w^3/2 + 285*w^2/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin_1 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((1 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((1 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (1 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(1 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^5 - 196*w^4 + 56*w^3 + 196*w^2 - 84*w) * hw
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^2/2 - 285/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^4 + 28*w^3 + 280*w^2 - 28*w - 84) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^5/2 - 95*w^4/2 - 285*w^3/2 + 285*w^2/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin_2 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((2 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((2 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (2 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(2 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-168*w^5 - 224*w^4 + 252*w^3 + 112*w^2 - 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^4 - 196*w^3 + 28*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^4 - 196*w^3 - 28*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^5 + 112*w^4 + 112*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin_3 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((3 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((3 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (3 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(3 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^4 + 28*w^3 - 196*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^5 - 112*w^4 - 168*w^3 + 112*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^3 - 112*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^4 + 28*w^3 + 196*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin_4 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((4 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((4 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (4 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(4 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (168*w^5 + 224*w^4 - 336*w^3 - 224*w^2 + 168*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^4 - 196*w^3 - 56*w^2 + 196*w + 84) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^5 - 28*w^4 + 280*w^3 + 28*w^2 - 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-168*w^3 + 224*w^2 + 168*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^2/2 - 285/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-95*w^5/2 - 95*w^4/2 + 285*w^3/2 + 285*w^2/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin_5 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((5 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((5 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (5 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(5 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^5 + 28*w^4 - 196*w^3 + 84*w^2) * hw
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^2/2 - 285/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^5 - 112*w^4 - 252*w^3 + 224*w^2 + 168*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^5 - 112*w^4 + 252*w^3 + 224*w^2 - 168*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^3 + 28*w^2 + 196*w + 84) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^11/2 - 285*w^9 - 95*w^8/2 + 570*w^7 + 475*w^6/2 - 475*w^5 - 665*w^4/2 + 285*w^3/2 + 285*w^2/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin_6 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((6 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((6 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (6 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(6 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^5 - 112*w^4 + 252*w^3 + 224*w^2 - 168*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^3 + 28*w^2 + 196*w + 84) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^5 + 28*w^4 - 196*w^3 + 84*w^2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^5 - 112*w^4 - 252*w^3 + 224*w^2 + 168*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^2/2 - 285/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^11/2 - 285*w^9 - 95*w^8/2 + 570*w^7 + 475*w^6/2 - 475*w^5 - 665*w^4/2 + 285*w^3/2 + 285*w^2/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin_7 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((7 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((7 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (7 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(7 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^5 - 28*w^4 + 280*w^3 + 28*w^2 - 84*w) * hw
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^2/2 - 285/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-168*w^3 + 224*w^2 + 168*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (168*w^5 + 224*w^4 - 336*w^3 - 224*w^2 + 168*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^4 - 196*w^3 - 56*w^2 + 196*w + 84) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-95*w^5/2 - 95*w^4/2 + 285*w^3/2 + 285*w^2/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin_8 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((8 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((8 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (8 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(8 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^3 - 112*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^4 + 28*w^3 + 196*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^4 + 28*w^3 - 196*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^5 - 112*w^4 - 168*w^3 + 112*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin_9 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((9 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((9 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (9 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(9 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^4 - 196*w^3 - 28*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^5 + 112*w^4 + 112*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-168*w^5 - 224*w^4 + 252*w^3 + 112*w^2 - 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^4 - 196*w^3 + 28*w^2 + 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin_10 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((10 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((10 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (10 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(10 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^4 + 28*w^3 + 280*w^2 - 28*w - 84) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^5 - 196*w^4 + 56*w^3 + 196*w^2 - 84*w) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^2/2 - 285/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^5/2 - 95*w^4/2 - 285*w^3/2 + 285*w^2/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin_11 (w : K) (hw : w^4-w^2+1=0)
    (r s t : Fin 3) :
    (modePairingCoefficient w ((11 : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((11 : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (11 : ℤ) s)⁻¹ *
        tensorModeStructure w (-(11 : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases r <;> fin_cases t <;> fin_cases s
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^5 + 196*w^4 + 28*w^3 - 84*w^2) * hw
  · mode_bulk_reduce w, hw <;> linear_combination (95*w^2/2 - 285/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^5 + 112*w^4 + 84*w^3) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (84*w^5 + 112*w^4 - 84*w^3) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-84*w^3 + 196*w^2 - 28*w - 84) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> linear_combination (-95*w^11/2 + 285*w^9 - 95*w^8/2 - 570*w^7 + 475*w^6/2 + 475*w^5 - 665*w^4/2 - 285*w^3/2 + 285*w^2/2) * hw
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring
  · mode_bulk_reduce w, hw <;> ring

private theorem modeBulkCoefficient_fin (w : K) (hw : w^4-w^2+1=0)
    (n : Fin 12) (r s t : Fin 3) :
    (modePairingCoefficient w ((n.val : ℤ)+1) r)⁻¹ *
        tensorModeStructure w ((n.val : ℤ)+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w (n.val : ℤ) s)⁻¹ *
        tensorModeStructure w (-(n.val : ℤ)) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  fin_cases n
  · exact modeBulkCoefficient_fin_0 w hw r s t
  · exact modeBulkCoefficient_fin_1 w hw r s t
  · exact modeBulkCoefficient_fin_2 w hw r s t
  · exact modeBulkCoefficient_fin_3 w hw r s t
  · exact modeBulkCoefficient_fin_4 w hw r s t
  · exact modeBulkCoefficient_fin_5 w hw r s t
  · exact modeBulkCoefficient_fin_6 w hw r s t
  · exact modeBulkCoefficient_fin_7 w hw r s t
  · exact modeBulkCoefficient_fin_8 w hw r s t
  · exact modeBulkCoefficient_fin_9 w hw r s t
  · exact modeBulkCoefficient_fin_10 w hw r s t
  · exact modeBulkCoefficient_fin_11 w hw r s t

theorem modeBulkCoefficient (w : K) (hw : w^4-w^2+1=0)
    (n : ℤ) (r s t : Fin 3) :
    (modePairingCoefficient w (n+1) r)⁻¹ *
        tensorModeStructure w (n+1) (-1) r.castSucc t.castSucc s.castSucc +
      (modePairingCoefficient w n s)⁻¹ *
        tensorModeStructure w (-n) (-1) s.castSucc t.castSucc r.castSucc = 0 := by
  let k : Fin 12 := ⟨(n%12).toNat, by omega⟩
  have hk : n%12 = (k.val : ℤ)%12 := by dsimp [k]; omega
  rw [modePairingCoefficient_eq_of_mod w hw (n+1) ((k.val : ℤ)+1) (by omega),
    modePairingCoefficient_eq_of_mod w hw n (k.val : ℤ) hk,
    tensorModeStructure_noncentral_eq_of_mod w hw (n+1) (-1) ((k.val : ℤ)+1) (-1)
      (by omega) rfl,
    tensorModeStructure_noncentral_eq_of_mod w hw (-n) (-1) (-(k.val : ℤ)) (-1)
      (by omega) rfl]
  exact modeBulkCoefficient_fin w hw k r s t

end KanadeRussell.Representation
