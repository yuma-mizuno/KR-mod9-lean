import KanadeRussell.Representation.PrincipalModeEigenframe

/-! The diagonal brackets of dual positive and negative principal eigenmodes,
including their central coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

noncomputable def principalFrameRootBracket (w : K) (n : Fin 12) (r : Fin 3) : Fin 4 → K :=
  ∑ s : Fin 3, ∑ t : Fin 3,
    (principalWeightFrame w n s r * principalDualWeightCoordinates w (n.val+1) n r t) •
      tensorModeStructure w (n.val+1) (-(n.val+1)) s.castSucc t.castSucc

noncomputable def principalFrameRootCartan (w : K) (n : Fin 12) (r : Fin 3) : Fin 4 → K :=
  if principalWeightSlotActive n r then
    ∑ j : Fin 3, ((![1, 1, 3] : Fin 3 → K) j * (principalWeightOccupation n r j : K)) •
      chevalleyHCoordinates w j
  else 0

private theorem principalFrameRootBracket_1 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨0, by decide⟩ r = principalFrameRootCartan w ⟨0, by decide⟩ r := by
  have hc : contraction w 1 = tensorHeisenbergPairing w 1 := by
    norm_num [tensorHeisenbergPairing, IsMode]
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix1, principalWeightInverse1, hc,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

private theorem principalFrameRootBracket_2 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨1, by decide⟩ r = principalFrameRootCartan w ⟨1, by decide⟩ r := by
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix2, principalWeightInverse2,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

private theorem principalFrameRootBracket_3 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨2, by decide⟩ r = principalFrameRootCartan w ⟨2, by decide⟩ r := by
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix3, principalWeightInverse3,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

private theorem principalFrameRootBracket_4 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨3, by decide⟩ r = principalFrameRootCartan w ⟨3, by decide⟩ r := by
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix4, principalWeightInverse4,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

private theorem principalFrameRootBracket_5 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨4, by decide⟩ r = principalFrameRootCartan w ⟨4, by decide⟩ r := by
  have hc : contraction w 5 = tensorHeisenbergPairing w 5 := by
    norm_num [tensorHeisenbergPairing, IsMode]
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix5, principalWeightInverse5, hc,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

private theorem principalFrameRootBracket_6 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨5, by decide⟩ r = principalFrameRootCartan w ⟨5, by decide⟩ r := by
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix6, principalWeightInverse6,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

private theorem principalFrameRootBracket_7 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨6, by decide⟩ r = principalFrameRootCartan w ⟨6, by decide⟩ r := by
  have hc : contraction w 7 = tensorHeisenbergPairing w 7 := by
    norm_num [tensorHeisenbergPairing, IsMode]
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix7, principalWeightInverse7, hc,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

private theorem principalFrameRootBracket_8 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨7, by decide⟩ r = principalFrameRootCartan w ⟨7, by decide⟩ r := by
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix8, principalWeightInverse8,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

private theorem principalFrameRootBracket_9 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨8, by decide⟩ r = principalFrameRootCartan w ⟨8, by decide⟩ r := by
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix9, principalWeightInverse9,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

private theorem principalFrameRootBracket_10 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨9, by decide⟩ r = principalFrameRootCartan w ⟨9, by decide⟩ r := by
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix10, principalWeightInverse10,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

private theorem principalFrameRootBracket_11 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨10, by decide⟩ r = principalFrameRootCartan w ⟨10, by decide⟩ r := by
  have hc : contraction w 11 = tensorHeisenbergPairing w 11 := by
    norm_num [tensorHeisenbergPairing, IsMode]
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix11, principalWeightInverse11, hc,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

private theorem principalFrameRootBracket_12 (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    principalFrameRootBracket w ⟨11, by decide⟩ r = principalFrameRootCartan w ⟨11, by decide⟩ r := by
  ext u
  simp only [principalFrameRootBracket, principalFrameRootCartan, ite_apply,
    Finset.sum_apply, Pi.smul_apply]
  fin_cases r <;> fin_cases u <;>
    norm_num [principalFrameRootBracket, principalFrameRootCartan, principalWeightFrame,
      principalDualWeightCoordinates, principalWeightReconstruction, principalWeightOccupation,
      principalWeightSlotActive, Fin.sum_univ_three, chevalleyHCoordinates,
      modePairingCoefficient_inv w hw, inverseModePairingCoefficient,
      tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, tensorHeisenbergPairing_residue w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second, Coefficients.pCoeff, Scalar.cPrime,
      Scalar.rootSecondResidue, IsMode,
principalWeightMatrix12, principalWeightInverse12,
principalWeightOccupation0, principalWeightOccupation1, principalWeightOccupation2, principalWeightOccupation3, principalWeightOccupation4, principalWeightOccupation5, principalWeightOccupation6, principalWeightOccupation7, principalWeightOccupation8, principalWeightOccupation9, principalWeightOccupation10, principalWeightOccupation11, principalWeightOccupation12, principalWeightOccupation13, principalWeightOccupation14, principalWeightOccupation15, principalWeightOccupation16, principalWeightOccupation17, principalWeightOccupation18, principalWeightOccupation19, principalWeightOccupation20, principalWeightOccupation21, principalWeightOccupation22, principalWeightOccupation23, principalWeightOccupation24, principalWeightOccupation25, principalWeightOccupation26, principalWeightOccupation27] <;> grind only

/-- The central terms are included; inactive ghost slots give zero. -/
theorem principalFrameRootBracket_eq_cartan (w : K) (hw : w^4-w^2+1=0)
    (n : Fin 12) (r : Fin 3) :
    principalFrameRootBracket w n r = principalFrameRootCartan w n r := by
  fin_cases n
  · exact principalFrameRootBracket_1 w hw r
  · exact principalFrameRootBracket_2 w hw r
  · exact principalFrameRootBracket_3 w hw r
  · exact principalFrameRootBracket_4 w hw r
  · exact principalFrameRootBracket_5 w hw r
  · exact principalFrameRootBracket_6 w hw r
  · exact principalFrameRootBracket_7 w hw r
  · exact principalFrameRootBracket_8 w hw r
  · exact principalFrameRootBracket_9 w hw r
  · exact principalFrameRootBracket_10 w hw r
  · exact principalFrameRootBracket_11 w hw r
  · exact principalFrameRootBracket_12 w hw r

theorem principalFrameRootBracket_evaluate (w : K) (hw : w^4-w^2+1=0)
    (n : Fin 12) (r : Fin 3) :
    ⁅principalModeCombination w (n.val+1) (fun t => principalWeightFrame w n t r),
      principalModeCombination w (-(n.val+1))
        (principalDualWeightCoordinates w (n.val+1) n r)⁆ =
      tensorModeEvaluate w 0 (principalFrameRootBracket w n r) := by
  have hsmul (c d : K) (A B : Module.End K (Space K)) :
      ⁅c • A, d • B⁆ = (c*d) • ⁅A,B⁆ := by
    simp only [Ring.lie_def, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      smul_smul, smul_sub]
    module
  rw [principalModeCombination_apply, principalModeCombination_apply, sum_lie_sum]
  simp only [principalFrameRootBracket, map_sum, map_smul, hsmul, principalMode,
    tensorModeBasis_lie w hw, add_neg_cancel]

/-- The diagonal bracket of the actual dual eigenoperators, with no independence hypothesis. -/
theorem principalFrameRootBracket_operator (w : K) (hw : w^4-w^2+1=0)
    (n : Fin 12) (r : Fin 3) (hr : principalWeightSlotActive n r) :
    ⁅principalModeCombination w (n.val+1) (fun t => principalWeightFrame w n t r),
      principalModeCombination w (-(n.val+1))
        (principalDualWeightCoordinates w (n.val+1) n r)⁆ =
      ∑ j : Fin 3, ((![1, 1, 3] : Fin 3 → K) j * (principalWeightOccupation n r j : K)) •
        chevalleyH w j := by
  rw [principalFrameRootBracket_evaluate w hw, principalFrameRootBracket_eq_cartan w hw,
    principalFrameRootCartan, if_pos hr]
  simp only [map_sum, map_smul, chevalleyH]

end KanadeRussell.Representation
