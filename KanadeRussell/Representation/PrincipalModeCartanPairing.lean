import KanadeRussell.Representation.PrincipalModeCartan

/-! Inverse principal-mode pairing is contravariant for the actual Cartan
matrices, including the inactive zero coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
local macro "cartan_pair_reduce " w:term ", " hw:term : tactic =>
  `(tactic| norm_num [principalCartanMatrix, chevalleyHCoordinates, Fin.sum_univ_three,
      modePairingCoefficient_inv $w $hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecHead, Matrix.vecTail, isMode_natAbs_iff_residue, IsMode,
      tensorHeisenbergPairing_residue $w $hw, RootData.rootWeight_second,
      Scalar.zpow_phasePolynomial $w $hw, Scalar.phasePolynomial, Int.toNat,
      Scalar.cPrime, Coefficients.pCoeff, Scalar.rootSecondResidue])

private theorem cartanPairing_fin_0 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(0:ℤ)) i r t * (modePairingCoefficient w (0:ℤ) t)⁻¹ +
      (modePairingCoefficient w (0:ℤ) r)⁻¹ * principalCartanMatrix w (0:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin_1 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(1:ℤ)) i r t * (modePairingCoefficient w (1:ℤ) t)⁻¹ +
      (modePairingCoefficient w (1:ℤ) r)⁻¹ * principalCartanMatrix w (1:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (210*w^8 + 490*w^7 - 560*w^6 - 532*w^5 + 812*w^4 + 364*w^3 - 938*w^2 - 378*w + 756) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^5/4 + 2375*w^3/4 - 855*w^2/4 - 1425*w/2 + 2565/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-770*w^7 - 490*w^6 + 1484*w^5 + 532*w^4 - 980*w^3 - 364*w^2 + 546*w + 378) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (475*w^8/4 - 475*w^7/4 - 2375*w^6/4 + 380*w^5 + 3705*w^4/4 - 285*w^3/4 - 2565*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^5/4 + 2375*w^3/4 - 855*w^2/4 - 1425*w/2 + 2565/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^14/4 + 950*w^12 + 95*w^11 - 2850*w^10 - 1805*w^9/4 + 17005*w^8/4 + 2185*w^7/4 - 3800*w^6 - 475*w^5/4 + 8835*w^4/4 - 285*w^3/4 - 2565*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-42*w^8 - 98*w^7 + 112*w^6 + 56*w^5 - 280*w^4 - 140*w^3 + 406*w^2 + 126*w - 252) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 285*w^2/4 + 285*w/2 - 855/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (154*w^7 + 98*w^6 - 196*w^5 - 56*w^4 + 112*w^3 + 140*w^2 - 126*w - 126) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-95*w^8/4 + 95*w^7/4 + 475*w^6/4 - 95*w^5/2 - 855*w^4/4 - 285*w^3/4 + 855*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 285*w^2/4 + 285*w/2 - 855/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^14/4 - 190*w^12 - 95*w^11/2 + 570*w^10 + 1045*w^9/4 - 3515*w^8/4 - 1805*w^7/4 + 1805*w^6/2 + 1235*w^5/4 - 2565*w^4/4 - 285*w^3/4 + 855*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-42*w^8 - 98*w^7 + 112*w^6 + 140*w^5 - 84*w^4 - 28*w^3 + 42*w^2 + 42*w - 84) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 95*w^2/4 + 285*w/2 - 285/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (154*w^7 + 98*w^6 - 364*w^5 - 140*w^4 + 252*w^3 + 28*w^2 - 98*w - 42) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-95*w^8/4 + 95*w^7/4 + 475*w^6/4 - 95*w^5 - 665*w^4/4 + 285*w^3/4 + 285*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 95*w^2/4 + 285*w/2 - 285/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^14/4 - 190*w^12 + 570*w^10 - 95*w^9/4 - 3325*w^8/4 + 475*w^7/4 + 665*w^6 - 665*w^5/4 - 1235*w^4/4 + 285*w^3/4 + 285*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin_2 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(2:ℤ)) i r t * (modePairingCoefficient w (2:ℤ) t)⁻¹ +
      (modePairingCoefficient w (2:ℤ) r)⁻¹ * principalCartanMatrix w (2:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (560*w^6 - 924*w^4 - 392*w^2 + 756) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-560*w^6 + 364*w^4 + 756*w^2) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-112*w^6 + 84*w^4 + 280*w^2 - 252) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (112*w^6 + 28*w^4 - 252*w^2) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-112*w^6 + 252*w^4 - 56*w^2 - 84) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (112*w^6 - 140*w^4 - 84*w^2) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin_3 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(3:ℤ)) i r t * (modePairingCoefficient w (3:ℤ) t)⁻¹ +
      (modePairingCoefficient w (3:ℤ) r)⁻¹ * principalCartanMatrix w (3:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-420*w^8 + 1260*w^6 + 420*w^5 - 1848*w^4 - 1260*w^3 + 1848*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (420*w^8 - 1260*w^6 + 420*w^5 + 1848*w^4 - 1260*w^3 + 1848*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (84*w^8 - 252*w^6 - 84*w^5 + 504*w^4 + 252*w^3 - 504*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-84*w^8 + 252*w^6 - 84*w^5 - 504*w^4 + 252*w^3 - 504*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (84*w^8 - 252*w^6 - 84*w^5 + 280*w^4 + 252*w^3 - 280*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-84*w^8 + 252*w^6 - 84*w^5 - 280*w^4 + 252*w^3 - 280*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin_4 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(4:ℤ)) i r t * (modePairingCoefficient w (4:ℤ) t)⁻¹ +
      (modePairingCoefficient w (4:ℤ) r)⁻¹ * principalCartanMatrix w (4:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-420*w^7 + 2100*w^5 - 4368*w^3 + 3696*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (420*w^7 - 840*w^5 + 588*w^3 + 1848*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (84*w^7 - 420*w^5 + 1008*w^3 - 1008*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-84*w^7 + 168*w^5 - 252*w^3 - 504*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (84*w^7 - 420*w^5 + 784*w^3 - 560*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-84*w^7 + 168*w^5 - 28*w^3 - 280*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin_5 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(5:ℤ)) i r t * (modePairingCoefficient w (5:ℤ) t)⁻¹ +
      (modePairingCoefficient w (5:ℤ) r)⁻¹ * principalCartanMatrix w (5:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (350*w^7 - 70*w^6 + 196*w^5 - 728*w^4 - 2128*w^3 + 1484*w^2 + 1302*w + 378) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^5/4 + 2375*w^3/4 - 855*w^2/4 - 1425*w/2 + 2565/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-210*w^8 - 70*w^7 + 1120*w^6 - 728*w^5 - 2296*w^4 + 1484*w^3 + 910*w^2 + 378*w + 756) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (475*w^14/4 - 950*w^12 - 665*w^11/2 + 2850*w^10 + 8455*w^9/4 - 15295*w^8/4 - 18335*w^7/4 + 3325*w^6/2 + 16625*w^5/4 + 3135*w^4/4 - 5415*w^3/4 - 2565*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^5/4 + 2375*w^3/4 - 855*w^2/4 - 1425*w/2 + 2565/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^8/4 - 475*w^7/4 + 2375*w^6/4 + 1615*w^5/2 - 1995*w^4/4 - 5415*w^3/4 - 2565*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-70*w^7 + 14*w^6 - 140*w^5 + 196*w^4 + 644*w^3 - 364*w^2 - 378*w - 126) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 285*w^2/4 + 285*w/2 - 855/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (42*w^8 + 14*w^7 - 224*w^6 + 196*w^5 + 476*w^4 - 364*w^3 - 98*w^2 - 126*w - 252) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-95*w^14/4 + 190*w^12 + 95*w^11 - 570*w^10 - 2375*w^9/4 + 2945*w^8/4 + 5035*w^7/4 - 190*w^6 - 4465*w^5/4 - 1425*w^4/4 + 1425*w^3/4 + 855*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 285*w^2/4 + 285*w/2 - 855/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^8/4 + 95*w^7/4 - 475*w^6/4 - 190*w^5 + 285*w^4/4 + 1425*w^3/4 + 855*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-70*w^7 + 14*w^6 + 28*w^5 + 112*w^4 + 280*w^3 - 252*w^2 - 182*w - 42) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 95*w^2/4 + 285*w/2 - 285/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (42*w^8 + 14*w^7 - 224*w^6 + 112*w^5 + 448*w^4 - 252*w^3 - 238*w^2 - 42*w - 84) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-95*w^14/4 + 190*w^12 + 95*w^11/2 - 570*w^10 - 1235*w^9/4 + 3135*w^8/4 + 2755*w^7/4 - 855*w^6/2 - 2565*w^5/4 - 95*w^4/4 + 855*w^3/4 + 285*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 95*w^2/4 + 285*w/2 - 285/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^8/4 + 95*w^7/4 - 475*w^6/4 - 285*w^5/2 + 475*w^4/4 + 855*w^3/4 + 285*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin_6 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(6:ℤ)) i r t * (modePairingCoefficient w (6:ℤ) t)⁻¹ +
      (modePairingCoefficient w (6:ℤ) r)⁻¹ * principalCartanMatrix w (6:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-1120*w^4 + 728*w^2 + 1512) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-1120*w^4 + 728*w^2 + 1512) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (224*w^4 + 56*w^2 - 504) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (224*w^4 + 56*w^2 - 504) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (224*w^4 - 280*w^2 - 168) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (224*w^4 - 280*w^2 - 168) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin_7 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(7:ℤ)) i r t * (modePairingCoefficient w (7:ℤ) t)⁻¹ +
      (modePairingCoefficient w (7:ℤ) r)⁻¹ * principalCartanMatrix w (7:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-210*w^8 - 70*w^7 + 1120*w^6 - 728*w^5 - 2296*w^4 + 1484*w^3 + 910*w^2 + 378*w + 756) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^5/4 + 2375*w^3/4 - 855*w^2/4 - 1425*w/2 + 2565/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (350*w^7 - 70*w^6 + 196*w^5 - 728*w^4 - 2128*w^3 + 1484*w^2 + 1302*w + 378) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^8/4 - 475*w^7/4 + 2375*w^6/4 + 1615*w^5/2 - 1995*w^4/4 - 5415*w^3/4 - 2565*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^5/4 + 2375*w^3/4 - 855*w^2/4 - 1425*w/2 + 2565/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (475*w^14/4 - 950*w^12 - 665*w^11/2 + 2850*w^10 + 8455*w^9/4 - 15295*w^8/4 - 18335*w^7/4 + 3325*w^6/2 + 16625*w^5/4 + 3135*w^4/4 - 5415*w^3/4 - 2565*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (42*w^8 + 14*w^7 - 224*w^6 + 196*w^5 + 476*w^4 - 364*w^3 - 98*w^2 - 126*w - 252) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 285*w^2/4 + 285*w/2 - 855/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-70*w^7 + 14*w^6 - 140*w^5 + 196*w^4 + 644*w^3 - 364*w^2 - 378*w - 126) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^8/4 + 95*w^7/4 - 475*w^6/4 - 190*w^5 + 285*w^4/4 + 1425*w^3/4 + 855*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 285*w^2/4 + 285*w/2 - 855/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-95*w^14/4 + 190*w^12 + 95*w^11 - 570*w^10 - 2375*w^9/4 + 2945*w^8/4 + 5035*w^7/4 - 190*w^6 - 4465*w^5/4 - 1425*w^4/4 + 1425*w^3/4 + 855*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (42*w^8 + 14*w^7 - 224*w^6 + 112*w^5 + 448*w^4 - 252*w^3 - 238*w^2 - 42*w - 84) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 95*w^2/4 + 285*w/2 - 285/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-70*w^7 + 14*w^6 + 28*w^5 + 112*w^4 + 280*w^3 - 252*w^2 - 182*w - 42) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^8/4 + 95*w^7/4 - 475*w^6/4 - 285*w^5/2 + 475*w^4/4 + 855*w^3/4 + 285*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 95*w^2/4 + 285*w/2 - 285/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-95*w^14/4 + 190*w^12 + 95*w^11/2 - 570*w^10 - 1235*w^9/4 + 3135*w^8/4 + 2755*w^7/4 - 855*w^6/2 - 2565*w^5/4 - 95*w^4/4 + 855*w^3/4 + 285*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin_8 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(8:ℤ)) i r t * (modePairingCoefficient w (8:ℤ) t)⁻¹ +
      (modePairingCoefficient w (8:ℤ) r)⁻¹ * principalCartanMatrix w (8:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (420*w^7 - 840*w^5 + 588*w^3 + 1848*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-420*w^7 + 2100*w^5 - 4368*w^3 + 3696*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-84*w^7 + 168*w^5 - 252*w^3 - 504*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (84*w^7 - 420*w^5 + 1008*w^3 - 1008*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-84*w^7 + 168*w^5 - 28*w^3 - 280*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (84*w^7 - 420*w^5 + 784*w^3 - 560*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin_9 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(9:ℤ)) i r t * (modePairingCoefficient w (9:ℤ) t)⁻¹ +
      (modePairingCoefficient w (9:ℤ) r)⁻¹ * principalCartanMatrix w (9:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (420*w^8 - 1260*w^6 + 420*w^5 + 1848*w^4 - 1260*w^3 + 1848*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-420*w^8 + 1260*w^6 + 420*w^5 - 1848*w^4 - 1260*w^3 + 1848*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-84*w^8 + 252*w^6 - 84*w^5 - 504*w^4 + 252*w^3 - 504*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (84*w^8 - 252*w^6 - 84*w^5 + 504*w^4 + 252*w^3 - 504*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-84*w^8 + 252*w^6 - 84*w^5 - 280*w^4 + 252*w^3 - 280*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (84*w^8 - 252*w^6 - 84*w^5 + 280*w^4 + 252*w^3 - 280*w) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin_10 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(10:ℤ)) i r t * (modePairingCoefficient w (10:ℤ) t)⁻¹ +
      (modePairingCoefficient w (10:ℤ) r)⁻¹ * principalCartanMatrix w (10:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-560*w^6 + 364*w^4 + 756*w^2) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (560*w^6 - 924*w^4 - 392*w^2 + 756) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (112*w^6 + 28*w^4 - 252*w^2) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-112*w^6 + 84*w^4 + 280*w^2 - 252) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (112*w^6 - 140*w^4 - 84*w^2) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-112*w^6 + 252*w^4 - 56*w^2 - 84) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin_11 (w : K) (hw : w^4-w^2+1=0) (i r t : Fin 3) :
    principalCartanMatrix w (-(11:ℤ)) i r t * (modePairingCoefficient w (11:ℤ) t)⁻¹ +
      (modePairingCoefficient w (11:ℤ) r)⁻¹ * principalCartanMatrix w (11:ℤ) i t r = 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases t
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-770*w^7 - 490*w^6 + 1484*w^5 + 532*w^4 - 980*w^3 - 364*w^2 + 546*w + 378) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^5/4 + 2375*w^3/4 - 855*w^2/4 - 1425*w/2 + 2565/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (210*w^8 + 490*w^7 - 560*w^6 - 532*w^5 + 812*w^4 + 364*w^3 - 938*w^2 - 378*w + 756) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^14/4 + 950*w^12 + 95*w^11 - 2850*w^10 - 1805*w^9/4 + 17005*w^8/4 + 2185*w^7/4 - 3800*w^6 - 475*w^5/4 + 8835*w^4/4 - 285*w^3/4 - 2565*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-475*w^5/4 + 2375*w^3/4 - 855*w^2/4 - 1425*w/2 + 2565/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (475*w^8/4 - 475*w^7/4 - 2375*w^6/4 + 380*w^5 + 3705*w^4/4 - 285*w^3/4 - 2565*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (154*w^7 + 98*w^6 - 196*w^5 - 56*w^4 + 112*w^3 + 140*w^2 - 126*w - 126) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 285*w^2/4 + 285*w/2 - 855/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-42*w^8 - 98*w^7 + 112*w^6 + 56*w^5 - 280*w^4 - 140*w^3 + 406*w^2 + 126*w - 252) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^14/4 - 190*w^12 - 95*w^11/2 + 570*w^10 + 1045*w^9/4 - 3515*w^8/4 - 1805*w^7/4 + 1805*w^6/2 + 1235*w^5/4 - 2565*w^4/4 - 285*w^3/4 + 855*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 285*w^2/4 + 285*w/2 - 855/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-95*w^8/4 + 95*w^7/4 + 475*w^6/4 - 95*w^5/2 - 855*w^4/4 - 285*w^3/4 + 855*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (154*w^7 + 98*w^6 - 364*w^5 - 140*w^4 + 252*w^3 + 28*w^2 - 98*w - 42) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 95*w^2/4 + 285*w/2 - 285/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-42*w^8 - 98*w^7 + 112*w^6 + 140*w^5 - 84*w^4 - 28*w^3 + 42*w^2 + 42*w - 84) * hw
  · cartan_pair_reduce w, hw <;> ring
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^14/4 - 190*w^12 + 570*w^10 - 95*w^9/4 - 3325*w^8/4 + 475*w^7/4 + 665*w^6 - 665*w^5/4 - 1235*w^4/4 + 285*w^3/4 + 285*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (95*w^5/4 - 475*w^3/4 + 95*w^2/4 + 285*w/2 - 285/4) * hw
  · cartan_pair_reduce w, hw <;> linear_combination (-95*w^8/4 + 95*w^7/4 + 475*w^6/4 - 95*w^5 - 665*w^4/4 + 285*w^3/4 + 285*w^2/4) * hw
  · cartan_pair_reduce w, hw <;> ring

private theorem cartanPairing_fin (w : K) (hw : w^4-w^2+1=0) (n : Fin 12) (i r t : Fin 3) :
    principalCartanMatrix w (-(n.val:ℤ)) i r t * (modePairingCoefficient w (n.val:ℤ) t)⁻¹ +
      (modePairingCoefficient w (n.val:ℤ) r)⁻¹ * principalCartanMatrix w (n.val:ℤ) i t r = 0 := by
  fin_cases n
  · exact cartanPairing_fin_0 w hw i r t
  · exact cartanPairing_fin_1 w hw i r t
  · exact cartanPairing_fin_2 w hw i r t
  · exact cartanPairing_fin_3 w hw i r t
  · exact cartanPairing_fin_4 w hw i r t
  · exact cartanPairing_fin_5 w hw i r t
  · exact cartanPairing_fin_6 w hw i r t
  · exact cartanPairing_fin_7 w hw i r t
  · exact cartanPairing_fin_8 w hw i r t
  · exact cartanPairing_fin_9 w hw i r t
  · exact cartanPairing_fin_10 w hw i r t
  · exact cartanPairing_fin_11 w hw i r t

theorem principalCartanMatrix_inversePairing_entry (w : K) (hw : w^4-w^2+1=0)
    (n : ℤ) (i r t : Fin 3) :
    principalCartanMatrix w (-n) i r t * (modePairingCoefficient w n t)⁻¹ +
      (modePairingCoefficient w n r)⁻¹ * principalCartanMatrix w n i t r = 0 := by
  let k : Fin 12 := ⟨(n%12).toNat, by omega⟩
  have hk : n%12 = (k.val:ℤ)%12 := by dsimp [k]; omega
  rw [principalCartanMatrix_eq_of_mod w hw (-n) (-(k.val:ℤ)) (by omega),
    principalCartanMatrix_eq_of_mod w hw n (k.val:ℤ) hk,
    modePairingCoefficient_eq_of_mod w hw n (k.val:ℤ) hk,
    modePairingCoefficient_eq_of_mod w hw n (k.val:ℤ) hk]
  exact cartanPairing_fin w hw k i r t

theorem principalCartanMatrix_inversePairing (w : K) (hw : w^4-w^2+1=0)
    (n : ℤ) (i : Fin 3) :
    principalCartanMatrix w (-n) i * Matrix.diagonal (fun r => (modePairingCoefficient w n r)⁻¹) +
      Matrix.diagonal (fun r => (modePairingCoefficient w n r)⁻¹) *
        (principalCartanMatrix w n i).transpose = 0 := by
  ext r t
  simpa using principalCartanMatrix_inversePairing_entry w hw n i r t

end KanadeRussell.Representation
