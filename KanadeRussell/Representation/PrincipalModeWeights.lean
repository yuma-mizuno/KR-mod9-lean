import KanadeRussell.Representation.PrincipalModeCartan

/-! Polynomial coordinate certificates for the positive principal modes.
These are coordinate statements; operator independence is not assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

def principalWeightOccupation0 : Fin 3 → ℕ := ![1, 0, 0]
noncomputable def principalWeightVector0 (w : K) : Fin 3 → K := ![-5*w^3/6 + 5*w/3 - 3/2, -5*w^3/6 + 5*w^2/6 + 19*w/6 + 7/3, 1]

theorem principalWeightVector0_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 1 i).mulVec (principalWeightVector0 w) =
      ((![2, -1, 0] : Fin 3 → K) i) • principalWeightVector0 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector0, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation1 : Fin 3 → ℕ := ![0, 1, 0]
noncomputable def principalWeightVector1 (w : K) : Fin 3 → K := ![w^3/6 - w/3 + 1/2, w^3/6 - w^2/6 - 5*w/6 - 2/3, 1]

theorem principalWeightVector1_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 1 i).mulVec (principalWeightVector1 w) =
      ((![-1, 2, -1] : Fin 3 → K) i) • principalWeightVector1 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector1, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation2 : Fin 3 → ℕ := ![0, 0, 1]
noncomputable def principalWeightVector2 (w : K) : Fin 3 → K := ![w^3/2 - w + 1/2, w^3/2 - w^2/2 - 3*w/2 - 1, 1]

theorem principalWeightVector2_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 1 i).mulVec (principalWeightVector2 w) =
      ((![0, -3, 2] : Fin 3 → K) i) • principalWeightVector2 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector2, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation3 : Fin 3 → ℕ := ![0, 1, 1]
noncomputable def principalWeightVector3 (w : K) : Fin 3 → K := ![2*w^3 - w^2 - 2*w + 2, 1, 0]

theorem principalWeightVector3_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 2 i).mulVec (principalWeightVector3 w) =
      ((![-1, -1, 1] : Fin 3 → K) i) • principalWeightVector3 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector3, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation4 : Fin 3 → ℕ := ![1, 1, 0]
noncomputable def principalWeightVector4 (w : K) : Fin 3 → K := ![-26*w^3 + 15*w^2 + 26*w - 30, 1, 0]

theorem principalWeightVector4_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 2 i).mulVec (principalWeightVector4 w) =
      ((![1, 1, -1] : Fin 3 → K) i) • principalWeightVector4 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector4, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation5 : Fin 3 → ℕ := ![1, 1, 1]
noncomputable def principalWeightVector5 (w : K) : Fin 3 → K := ![-4*w^3 + 11*w^2 - 11*w + 4, 1, 0]

theorem principalWeightVector5_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 3 i).mulVec (principalWeightVector5 w) =
      ((![1, -2, 1] : Fin 3 → K) i) • principalWeightVector5 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector5, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation6 : Fin 3 → ℕ := ![0, 2, 1]
noncomputable def principalWeightVector6 (w : K) : Fin 3 → K := ![w^3 - 3*w^2 + 3*w - 1, 1, 0]

theorem principalWeightVector6_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 3 i).mulVec (principalWeightVector6 w) =
      ((![-2, 1, 0] : Fin 3 → K) i) • principalWeightVector6 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector6, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation7 : Fin 3 → ℕ := ![0, 3, 1]
noncomputable def principalWeightVector7 (w : K) : Fin 3 → K := ![-8*w^3 + 7*w^2 + 4*w - 7, 1, 0]

theorem principalWeightVector7_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 4 i).mulVec (principalWeightVector7 w) =
      ((![-3, 3, -1] : Fin 3 → K) i) • principalWeightVector7 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector7, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation8 : Fin 3 → ℕ := ![1, 2, 1]
noncomputable def principalWeightVector8 (w : K) : Fin 3 → K := ![8*w^3 - 7*w^2 - 4*w + 7, 1, 0]

theorem principalWeightVector8_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 4 i).mulVec (principalWeightVector8 w) =
      ((![0, 0, 0] : Fin 3 → K) i) • principalWeightVector8 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector8, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation9 : Fin 3 → ℕ := ![2, 2, 1]
noncomputable def principalWeightVector9 (w : K) : Fin 3 → K := ![-5*w^3/6 + 5*w/3 - 3/2, 2*w^3/3 + 5*w^2/6 + w/6 - 1/6, 1]

theorem principalWeightVector9_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 5 i).mulVec (principalWeightVector9 w) =
      ((![2, -1, 0] : Fin 3 → K) i) • principalWeightVector9 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector9, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation10 : Fin 3 → ℕ := ![1, 3, 1]
noncomputable def principalWeightVector10 (w : K) : Fin 3 → K := ![w^3/6 - w/3 + 1/2, -w^3/3 - w^2/6 + w/6 - 1/6, 1]

theorem principalWeightVector10_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 5 i).mulVec (principalWeightVector10 w) =
      ((![-1, 2, -1] : Fin 3 → K) i) • principalWeightVector10 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector10, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation11 : Fin 3 → ℕ := ![0, 3, 2]
noncomputable def principalWeightVector11 (w : K) : Fin 3 → K := ![3*w^3/2 - 3*w + 5/2, -w^3 - 3*w^2/2 - w/2 + 1/2, 1]

theorem principalWeightVector11_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 5 i).mulVec (principalWeightVector11 w) =
      ((![-3, 0, 1] : Fin 3 → K) i) • principalWeightVector11 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector11, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation12 : Fin 3 → ℕ := ![1, 3, 2]
noncomputable def principalWeightVector12 (w : K) : Fin 3 → K := ![7*w^3 - 8*w^2 + 4, 1, 0]

theorem principalWeightVector12_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 6 i).mulVec (principalWeightVector12 w) =
      ((![-1, -1, 1] : Fin 3 → K) i) • principalWeightVector12 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector12, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation13 : Fin 3 → ℕ := ![2, 3, 1]
noncomputable def principalWeightVector13 (w : K) : Fin 3 → K := ![-7*w^3 + 8*w^2 - 4, 1, 0]

theorem principalWeightVector13_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 6 i).mulVec (principalWeightVector13 w) =
      ((![1, 1, -1] : Fin 3 → K) i) • principalWeightVector13 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector13, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation14 : Fin 3 → ℕ := ![3, 3, 1]
noncomputable def principalWeightVector14 (w : K) : Fin 3 → K := ![-3*w^3/2 + 3*w - 5/2, -3*w^3/2 - 3*w^2/2 + w/2 + 1, 1]

theorem principalWeightVector14_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 7 i).mulVec (principalWeightVector14 w) =
      ((![3, 0, -1] : Fin 3 → K) i) • principalWeightVector14 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector14, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation15 : Fin 3 → ℕ := ![2, 3, 2]
noncomputable def principalWeightVector15 (w : K) : Fin 3 → K := ![-w^3/6 + w/3 - 1/2, -w^3/6 - w^2/6 - w/6 + 1/3, 1]

theorem principalWeightVector15_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 7 i).mulVec (principalWeightVector15 w) =
      ((![1, -2, 1] : Fin 3 → K) i) • principalWeightVector15 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector15, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation16 : Fin 3 → ℕ := ![1, 4, 2]
noncomputable def principalWeightVector16 (w : K) : Fin 3 → K := ![5*w^3/6 - 5*w/3 + 3/2, 5*w^3/6 + 5*w^2/6 - w/6 - 2/3, 1]

theorem principalWeightVector16_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 7 i).mulVec (principalWeightVector16 w) =
      ((![-2, 1, 0] : Fin 3 → K) i) • principalWeightVector16 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector16, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation17 : Fin 3 → ℕ := ![3, 3, 2]
noncomputable def principalWeightVector17 (w : K) : Fin 3 → K := ![4*w^3 - 7*w^2 + 4*w, 1, 0]

theorem principalWeightVector17_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 8 i).mulVec (principalWeightVector17 w) =
      ((![3, -3, 1] : Fin 3 → K) i) • principalWeightVector17 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector17, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation18 : Fin 3 → ℕ := ![2, 4, 2]
noncomputable def principalWeightVector18 (w : K) : Fin 3 → K := ![-4*w^3 + 7*w^2 - 4*w, 1, 0]

theorem principalWeightVector18_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 8 i).mulVec (principalWeightVector18 w) =
      ((![0, 0, 0] : Fin 3 → K) i) • principalWeightVector18 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector18, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation19 : Fin 3 → ℕ := ![3, 4, 2]
noncomputable def principalWeightVector19 (w : K) : Fin 3 → K := ![-4*w^3 + 3*w^2 + 3*w - 4, 1, 0]

theorem principalWeightVector19_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 9 i).mulVec (principalWeightVector19 w) =
      ((![2, -1, 0] : Fin 3 → K) i) • principalWeightVector19 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector19, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation20 : Fin 3 → ℕ := ![2, 5, 2]
noncomputable def principalWeightVector20 (w : K) : Fin 3 → K := ![15*w^3 - 11*w^2 - 11*w + 15, 1, 0]

theorem principalWeightVector20_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 9 i).mulVec (principalWeightVector20 w) =
      ((![-1, 2, -1] : Fin 3 → K) i) • principalWeightVector20 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector20, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation21 : Fin 3 → ℕ := ![2, 5, 3]
noncomputable def principalWeightVector21 (w : K) : Fin 3 → K := ![-15*w^2 + 26*w - 15, 1, 0]

theorem principalWeightVector21_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 10 i).mulVec (principalWeightVector21 w) =
      ((![-1, -1, 1] : Fin 3 → K) i) • principalWeightVector21 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector21, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation22 : Fin 3 → ℕ := ![3, 5, 2]
noncomputable def principalWeightVector22 (w : K) : Fin 3 → K := ![w^2 - 2*w + 1, 1, 0]

theorem principalWeightVector22_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 10 i).mulVec (principalWeightVector22 w) =
      ((![1, 1, -1] : Fin 3 → K) i) • principalWeightVector22 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector22, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation23 : Fin 3 → ℕ := ![3, 5, 3]
noncomputable def principalWeightVector23 (w : K) : Fin 3 → K := ![-w^3/6 + w/3 - 1/2, -2*w^3/3 - w^2/6 + 5*w/6 + 5/6, 1]

theorem principalWeightVector23_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 11 i).mulVec (principalWeightVector23 w) =
      ((![1, -2, 1] : Fin 3 → K) i) • principalWeightVector23 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector23, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation24 : Fin 3 → ℕ := ![2, 6, 3]
noncomputable def principalWeightVector24 (w : K) : Fin 3 → K := ![5*w^3/6 - 5*w/3 + 3/2, 7*w^3/3 + 5*w^2/6 - 19*w/6 - 19/6, 1]

theorem principalWeightVector24_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 11 i).mulVec (principalWeightVector24 w) =
      ((![-2, 1, 0] : Fin 3 → K) i) • principalWeightVector24 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector24, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation25 : Fin 3 → ℕ := ![3, 6, 2]
noncomputable def principalWeightVector25 (w : K) : Fin 3 → K := ![-w^3/2 + w - 1/2, -w^3 - w^2/2 + 3*w/2 + 3/2, 1]

theorem principalWeightVector25_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 11 i).mulVec (principalWeightVector25 w) =
      ((![0, 3, -2] : Fin 3 → K) i) • principalWeightVector25 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector25, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode] <;> grind only

def principalWeightOccupation26 : Fin 3 → ℕ := ![3, 6, 3]
noncomputable def principalWeightVector26 (_w : K) : Fin 3 → K := ![1, 0, 0]

theorem principalWeightVector26_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 12 i).mulVec (principalWeightVector26 w) =
      ((![0, 0, 0] : Fin 3 → K) i) • principalWeightVector26 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector26, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode]

def principalWeightOccupation27 : Fin 3 → ℕ := ![3, 6, 3]
noncomputable def principalWeightVector27 (_w : K) : Fin 3 → K := ![0, 1, 0]

theorem principalWeightVector27_eigen (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    (principalCartanMatrix w 12 i).mulVec (principalWeightVector27 w) =
      ((![0, 0, 0] : Fin 3 → K) i) • principalWeightVector27 w := by
  ext t
  fin_cases i <;> fin_cases t <;>
    norm_num [principalCartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      chevalleyHCoordinates, tensorModeStructure, normalizeTensorCoordinates,
      tensorModeRawStructure, principalWeightVector27, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      tensorHeisenbergPairing_residue w hw, isMode_natAbs_iff_residue,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode]

noncomputable def principalWeightMatrix1 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-5*w^3/6 + 5*w/3 - 3/2, w^3/6 - w/3 + 1/2, w^3/2 - w + 1/2],
    ![-5*w^3/6 + 5*w^2/6 + 19*w/6 + 7/3, w^3/6 - w^2/6 - 5*w/6 - 2/3, w^3/2 - w^2/2 - 3*w/2 - 1],
    ![1, 1, 1]]

noncomputable def principalWeightInverse1 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-1/4, -w^3/4 + w^2/4, 1/4],
    ![-w^3/2 + w + 1, 3*w^3/2 - 2*w^2 + w/2 + 1/2, 1/2],
    ![w^3/2 - w - 3/4, -5*w^3/4 + 7*w^2/4 - w/2 - 1/2, 1/4]]

theorem principalWeightMatrix1_mul_inverse (w : K) (hw : w^4-w^2+1=0) :
    principalWeightMatrix1 w * principalWeightInverse1 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix1, principalWeightInverse1, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

noncomputable def principalWeightMatrix2 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![2*w^3 - w^2 - 2*w + 2, -26*w^3 + 15*w^2 + 26*w - 30, 0],
    ![1, 1, 0],
    ![0, 0, 1]]

noncomputable def principalWeightInverse2 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-w^2 - 7*w/4 - 1, w^3/4 - w/2 + 1/2, 0],
    ![w^2 + 7*w/4 + 1, -w^3/4 + w/2 + 1/2, 0],
    ![0, 0, 1]]

theorem principalWeightMatrix2_mul_inverse (w : K) (hw : w^4-w^2+1=0) :
    principalWeightMatrix2 w * principalWeightInverse2 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix2, principalWeightInverse2, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

noncomputable def principalWeightMatrix3 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-4*w^3 + 11*w^2 - 11*w + 4, w^3 - 3*w^2 + 3*w - 1, 0],
    ![1, 1, 0],
    ![0, 0, 1]]

noncomputable def principalWeightInverse3 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-5*w^3/6 - 7*w^2/3 - 7*w/3 - 5/6, -w^3/6 + w/3 + 1/2, 0],
    ![5*w^3/6 + 7*w^2/3 + 7*w/3 + 5/6, w^3/6 - w/3 + 1/2, 0],
    ![0, 0, 1]]

theorem principalWeightMatrix3_mul_inverse (w : K) (hw : w^4-w^2+1=0) :
    principalWeightMatrix3 w * principalWeightInverse3 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix3, principalWeightInverse3, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

noncomputable def principalWeightMatrix4 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-8*w^3 + 7*w^2 + 4*w - 7, 8*w^3 - 7*w^2 - 4*w + 7, 0],
    ![1, 1, 0],
    ![0, 0, 1]]

noncomputable def principalWeightInverse4 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-2*w^3 - 7*w^2/2 - 2*w, 1/2, 0],
    ![2*w^3 + 7*w^2/2 + 2*w, 1/2, 0],
    ![0, 0, 1]]

theorem principalWeightMatrix4_mul_inverse (w : K) (hw : w^4-w^2+1=0) :
    principalWeightMatrix4 w * principalWeightInverse4 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix4, principalWeightInverse4, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

noncomputable def principalWeightMatrix5 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-5*w^3/6 + 5*w/3 - 3/2, w^3/6 - w/3 + 1/2, 3*w^3/2 - 3*w + 5/2],
    ![2*w^3/3 + 5*w^2/6 + w/6 - 1/6, -w^3/3 - w^2/6 + w/6 - 1/6, -w^3 - 3*w^2/2 - w/2 + 1/2],
    ![1, 1, 1]]

noncomputable def principalWeightInverse5 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![w^3/2 - w - 1, 1/2 - w/2, 1/2],
    ![-w^3 + 2*w + 7/4, -w^3/4 - w^2/4 + w - 3/4, 1/4],
    ![w^3/2 - w - 3/4, w^3/4 + w^2/4 - w/2 + 1/4, 1/4]]

theorem principalWeightMatrix5_mul_inverse (w : K) (hw : w^4-w^2+1=0) :
    principalWeightMatrix5 w * principalWeightInverse5 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix5, principalWeightInverse5, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

noncomputable def principalWeightMatrix6 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![7*w^3 - 8*w^2 + 4, -7*w^3 + 8*w^2 - 4, 0],
    ![1, 1, 0],
    ![0, 0, 1]]

noncomputable def principalWeightInverse6 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-7*w^3/2 - 4*w^2 + 2, 1/2, 0],
    ![7*w^3/2 + 4*w^2 - 2, 1/2, 0],
    ![0, 0, 1]]

theorem principalWeightMatrix6_mul_inverse (w : K) (hw : w^4-w^2+1=0) :
    principalWeightMatrix6 w * principalWeightInverse6 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix6, principalWeightInverse6, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

noncomputable def principalWeightMatrix7 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-3*w^3/2 + 3*w - 5/2, -w^3/6 + w/3 - 1/2, 5*w^3/6 - 5*w/3 + 3/2],
    ![-3*w^3/2 - 3*w^2/2 + w/2 + 1, -w^3/6 - w^2/6 - w/6 + 1/3, 5*w^3/6 + 5*w^2/6 - w/6 - 2/3],
    ![1, 1, 1]]

noncomputable def principalWeightInverse7 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-w^3/2 + w + 3/4, -w^3/4 + w^2/4 + w/2 - 1/2, 1/4],
    ![w^3 - 2*w - 7/4, 3*w^3/4 - w^2/4 - w + 1, 1/4],
    ![-w^3/2 + w + 1, -w^3/2 + w/2 - 1/2, 1/2]]

theorem principalWeightMatrix7_mul_inverse (w : K) (hw : w^4-w^2+1=0) :
    principalWeightMatrix7 w * principalWeightInverse7 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix7, principalWeightInverse7, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

noncomputable def principalWeightMatrix8 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![4*w^3 - 7*w^2 + 4*w, -4*w^3 + 7*w^2 - 4*w, 0],
    ![1, 1, 0],
    ![0, 0, 1]]

noncomputable def principalWeightInverse8 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![4*w^3 + 7*w^2/2 - 2*w - 7/2, 1/2, 0],
    ![-4*w^3 - 7*w^2/2 + 2*w + 7/2, 1/2, 0],
    ![0, 0, 1]]

theorem principalWeightMatrix8_mul_inverse (w : K) (hw : w^4-w^2+1=0) :
    principalWeightMatrix8 w * principalWeightInverse8 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix8, principalWeightInverse8, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

noncomputable def principalWeightMatrix9 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-4*w^3 + 3*w^2 + 3*w - 4, 15*w^3 - 11*w^2 - 11*w + 15, 0],
    ![1, 1, 0],
    ![0, 0, 1]]

noncomputable def principalWeightInverse9 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-19*w^3/6 - 7*w^2/3 + 7*w/3 + 19/6, w^3/6 - w/3 + 1/2, 0],
    ![19*w^3/6 + 7*w^2/3 - 7*w/3 - 19/6, -w^3/6 + w/3 + 1/2, 0],
    ![0, 0, 1]]

theorem principalWeightMatrix9_mul_inverse (w : K) (hw : w^4-w^2+1=0) :
    principalWeightMatrix9 w * principalWeightInverse9 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix9, principalWeightInverse9, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

noncomputable def principalWeightMatrix10 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-15*w^2 + 26*w - 15, w^2 - 2*w + 1, 0],
    ![1, 1, 0],
    ![0, 0, 1]]

noncomputable def principalWeightInverse10 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-7*w^3/4 - w^2 + 7*w/4 + 2, -w^3/4 + w/2 + 1/2, 0],
    ![7*w^3/4 + w^2 - 7*w/4 - 2, w^3/4 - w/2 + 1/2, 0],
    ![0, 0, 1]]

theorem principalWeightMatrix10_mul_inverse (w : K) (hw : w^4-w^2+1=0) :
    principalWeightMatrix10 w * principalWeightInverse10 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix10, principalWeightInverse10, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

noncomputable def principalWeightMatrix11 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![-w^3/6 + w/3 - 1/2, 5*w^3/6 - 5*w/3 + 3/2, -w^3/2 + w - 1/2],
    ![-2*w^3/3 - w^2/6 + 5*w/6 + 5/6, 7*w^3/3 + 5*w^2/6 - 19*w/6 - 19/6, -w^3 - w^2/2 + 3*w/2 + 3/2],
    ![1, 1, 1]]

noncomputable def principalWeightInverse11 (w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![w^3/2 - w - 1, 2*w^3 - 2*w^2 - w/2 + 3/2, 1/2],
    ![1/4, -w^3/4 + w^2/4 - 1/4, 1/4],
    ![-w^3/2 + w + 3/4, -7*w^3/4 + 7*w^2/4 + w/2 - 5/4, 1/4]]

theorem principalWeightMatrix11_mul_inverse (w : K) (hw : w^4-w^2+1=0) :
    principalWeightMatrix11 w * principalWeightInverse11 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix11, principalWeightInverse11, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

noncomputable def principalWeightMatrix12 (_w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, 1]]

noncomputable def principalWeightInverse12 (_w : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, 1]]

omit [CharZero K] in
theorem principalWeightMatrix12_mul_inverse (w : K) (_hw : w^4-w^2+1=0) :
    principalWeightMatrix12 w * principalWeightInverse12 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalWeightMatrix12, principalWeightInverse12, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Residues are represented by the positive integers `n.val + 1`.
The third entry is zero in the eight inactive Heisenberg residues. -/
noncomputable def principalWeightCoordinates (w : K) (n : Fin 12) : Fin 3 → (Fin 3 → K) :=
  ![![principalWeightVector0 w, principalWeightVector1 w, principalWeightVector2 w],
    ![principalWeightVector3 w, principalWeightVector4 w, 0],
    ![principalWeightVector5 w, principalWeightVector6 w, 0],
    ![principalWeightVector7 w, principalWeightVector8 w, 0],
    ![principalWeightVector9 w, principalWeightVector10 w, principalWeightVector11 w],
    ![principalWeightVector12 w, principalWeightVector13 w, 0],
    ![principalWeightVector14 w, principalWeightVector15 w, principalWeightVector16 w],
    ![principalWeightVector17 w, principalWeightVector18 w, 0],
    ![principalWeightVector19 w, principalWeightVector20 w, 0],
    ![principalWeightVector21 w, principalWeightVector22 w, 0],
    ![principalWeightVector23 w, principalWeightVector24 w, principalWeightVector25 w],
    ![principalWeightVector26 w, principalWeightVector27 w, 0]] n

def principalWeightOccupation (n : Fin 12) : Fin 3 → (Fin 3 → ℕ) :=
  ![![principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2],
    ![principalWeightOccupation3, principalWeightOccupation4, ![2, 0, 0]],
    ![principalWeightOccupation5, principalWeightOccupation6, ![3, 0, 0]],
    ![principalWeightOccupation7, principalWeightOccupation8, ![4, 0, 0]],
    ![principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11],
    ![principalWeightOccupation12, principalWeightOccupation13, ![6, 0, 0]],
    ![principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16],
    ![principalWeightOccupation17, principalWeightOccupation18, ![8, 0, 0]],
    ![principalWeightOccupation19, principalWeightOccupation20, ![9, 0, 0]],
    ![principalWeightOccupation21, principalWeightOccupation22, ![10, 0, 0]],
    ![principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25],
    ![principalWeightOccupation26, principalWeightOccupation27, ![12, 0, 0]]] n

noncomputable def principalWeightReconstruction (w : K) (n : Fin 12) : Matrix (Fin 3) (Fin 3) K :=
  ![principalWeightInverse1 w, principalWeightInverse2 w, principalWeightInverse3 w, principalWeightInverse4 w, principalWeightInverse5 w, principalWeightInverse6 w, principalWeightInverse7 w, principalWeightInverse8 w, principalWeightInverse9 w, principalWeightInverse10 w, principalWeightInverse11 w, principalWeightInverse12 w] n

theorem principalWeightOccupation_degree (n : Fin 12) (r : Fin 3) :
    ∑ i, principalWeightOccupation n r i = n.val + 1 := by
  fin_cases n <;> fin_cases r <;>
    norm_num [principalWeightOccupation, Fin.sum_univ_three, Matrix.cons_val_two,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27]

theorem principalWeightCoordinates_eigen (w : K) (hw : w^4-w^2+1=0)
    (n : Fin 12) (r i : Fin 3) :
    (principalCartanMatrix w (n.val+1) i).mulVec (principalWeightCoordinates w n r) =
      (∑ j, (affineCartanMatrix i j : K) * (principalWeightOccupation n r j : K)) •
        principalWeightCoordinates w n r := by
  fin_cases n <;> fin_cases r
  · have h := principalWeightVector0_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation0, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector1_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation1, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector2_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation2, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector3_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation3, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector4_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation4, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · simp [principalWeightCoordinates, Matrix.mulVec_zero]
  · have h := principalWeightVector5_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation5, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector6_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation6, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · simp [principalWeightCoordinates, Matrix.mulVec_zero]
  · have h := principalWeightVector7_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation7, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector8_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation8, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · simp [principalWeightCoordinates, Matrix.mulVec_zero]
  · have h := principalWeightVector9_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation9, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector10_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation10, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector11_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation11, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector12_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation12, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector13_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation13, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · simp [principalWeightCoordinates, Matrix.mulVec_zero]
  · have h := principalWeightVector14_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation14, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector15_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation15, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector16_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation16, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector17_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation17, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector18_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation18, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · simp [principalWeightCoordinates, Matrix.mulVec_zero]
  · have h := principalWeightVector19_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation19, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector20_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation20, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · simp [principalWeightCoordinates, Matrix.mulVec_zero]
  · have h := principalWeightVector21_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation21, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector22_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation22, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · simp [principalWeightCoordinates, Matrix.mulVec_zero]
  · have h := principalWeightVector23_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation23, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector24_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation24, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector25_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation25, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector26_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation26, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · have h := principalWeightVector27_eigen w hw i
    fin_cases i <;> norm_num [principalWeightCoordinates, principalWeightOccupation,
      principalWeightOccupation27, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact h
  · simp [principalWeightCoordinates, Matrix.mulVec_zero]

/-- Explicit reconstruction of every active coordinate from the eigenvectors. -/
theorem principalWeightCoordinates_reconstruct (w : K) (hw : w^4-w^2+1=0)
    (n : Fin 12) (v : Fin 3 → K) :
    ∑ r, ((principalWeightReconstruction w n).mulVec v) r •
      principalWeightCoordinates w n r =
        ![v 0, v 1, if IsMode (n.val+1) then v 2 else 0] := by
  ext i
  fin_cases n <;> fin_cases i <;>
    norm_num [principalWeightReconstruction, principalWeightCoordinates,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, IsMode,
      Matrix.cons_val_two, Matrix.cons_val_three,
principalWeightVector0, principalWeightVector1, principalWeightVector2, principalWeightVector3, principalWeightVector4, principalWeightVector5, principalWeightVector6, principalWeightVector7, principalWeightVector8, principalWeightVector9, principalWeightVector10, principalWeightVector11, principalWeightVector12, principalWeightVector13, principalWeightVector14, principalWeightVector15, principalWeightVector16, principalWeightVector17, principalWeightVector18, principalWeightVector19, principalWeightVector20, principalWeightVector21, principalWeightVector22, principalWeightVector23, principalWeightVector24, principalWeightVector25, principalWeightVector26, principalWeightVector27,
principalWeightInverse1, principalWeightInverse2, principalWeightInverse3, principalWeightInverse4, principalWeightInverse5, principalWeightInverse6, principalWeightInverse7, principalWeightInverse8, principalWeightInverse9, principalWeightInverse10, principalWeightInverse11, principalWeightInverse12] <;> grind only

end KanadeRussell.Representation
