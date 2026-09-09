import KanadeRussell.Tsuchioka.TensorLieCoordinates
import KanadeRussell.Tsuchioka.CyclotomicPhaseReduction

/-! Explicit Chevalley coordinates for the source D4^(3) Cartan matrix.
The identities below are checked in a characteristic-zero field satisfying Phi_12(w)=0. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

def affineCartanMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, -1, 0; -1, 2, -3; 0, -1, 2]

def chevalleyECoordinates (w : K) : Fin 3 → Fin 4 → K :=
  ![![-5*w^3/6 + 5*w/3 - 3/2,
      -5*w^3/6 + 5*w^2/6 + 19*w/6 + 7/3, 1, 0],
    ![w^3/6 - w/3 + 1/2,
      w^3/6 - w^2/6 - 5*w/6 - 2/3, 1, 0],
    ![w^3/2 - w + 1/2,
      w^3/2 - w^2/2 - 3*w/2 - 1, 1, 0]]

def chevalleyFCoordinates (w : K) : Fin 3 → Fin 4 → K :=
  ![![3*w^3 - 6*w + 21/4,
      9*w^3/4 + 3*w^2/4 - 3*w - 3,
      3*w^3/4 - 3*w/2 + 9/4, 0],
    ![-3*w^3/2 + 3*w - 3,
      -3*w^3/2 + 3*w/2 + 3/2,
      3*w^3/2 - 3*w + 9/2, 0],
    ![-w^3/2 + w - 3/4,
      -w^3/4 - w^2/4 + w/2 + 1/2,
      w^3/4 - w/2 + 3/4, 0]]

def chevalleyHCoordinates (w : K) : Fin 3 → Fin 4 → K :=
  ![![5*w^3/2 - 5*w + 9/2, -5*w^3/2 + 5*w + 9/2, 0, 3/4],
    ![-w^3/2 + w - 3/2, w^3/2 - w - 3/2, 0, 3/4],
    ![-w^3/2 + w - 1/2, w^3/2 - w - 1/2, 0, 1/4]]

theorem contraction_one (w : K) (hw : w^4-w^2+1=0) :
    contraction w 1 = -w^3/6+w/3+1/2 := by
  simpa [spectralValue] using contraction_fin w hw (1 : Fin 12)

theorem chevalley_coordinates_HH (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    tensorCoordinateBracket w 0 0 (chevalleyHCoordinates w i) (chevalleyHCoordinates w j) = 0 := by
  fin_cases i <;> fin_cases j <;> funext r <;> fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, chevalleyHCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, RootData.rootWeight_second,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HE_00 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 1 (chevalleyHCoordinates w 0) (chevalleyECoordinates w 0) =
      (affineCartanMatrix 0 0 : K) • chevalleyECoordinates w 0 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HE_01 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 1 (chevalleyHCoordinates w 0) (chevalleyECoordinates w 1) =
      (affineCartanMatrix 0 1 : K) • chevalleyECoordinates w 1 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HE_02 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 1 (chevalleyHCoordinates w 0) (chevalleyECoordinates w 2) =
      (affineCartanMatrix 0 2 : K) • chevalleyECoordinates w 2 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HE_10 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 1 (chevalleyHCoordinates w 1) (chevalleyECoordinates w 0) =
      (affineCartanMatrix 1 0 : K) • chevalleyECoordinates w 0 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HE_11 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 1 (chevalleyHCoordinates w 1) (chevalleyECoordinates w 1) =
      (affineCartanMatrix 1 1 : K) • chevalleyECoordinates w 1 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HE_12 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 1 (chevalleyHCoordinates w 1) (chevalleyECoordinates w 2) =
      (affineCartanMatrix 1 2 : K) • chevalleyECoordinates w 2 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HE_20 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 1 (chevalleyHCoordinates w 2) (chevalleyECoordinates w 0) =
      (affineCartanMatrix 2 0 : K) • chevalleyECoordinates w 0 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HE_21 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 1 (chevalleyHCoordinates w 2) (chevalleyECoordinates w 1) =
      (affineCartanMatrix 2 1 : K) • chevalleyECoordinates w 1 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HE_22 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 1 (chevalleyHCoordinates w 2) (chevalleyECoordinates w 2) =
      (affineCartanMatrix 2 2 : K) • chevalleyECoordinates w 2 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_coordinates_HE (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    tensorCoordinateBracket w 0 1 (chevalleyHCoordinates w i) (chevalleyECoordinates w j) =
      (affineCartanMatrix i j : K) • chevalleyECoordinates w j := by
  fin_cases i <;> fin_cases j
  · exact chevalley_coordinates_HE_00 w hw
  · exact chevalley_coordinates_HE_01 w hw
  · exact chevalley_coordinates_HE_02 w hw
  · exact chevalley_coordinates_HE_10 w hw
  · exact chevalley_coordinates_HE_11 w hw
  · exact chevalley_coordinates_HE_12 w hw
  · exact chevalley_coordinates_HE_20 w hw
  · exact chevalley_coordinates_HE_21 w hw
  · exact chevalley_coordinates_HE_22 w hw

private theorem chevalley_coordinates_HF_00 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 (-1) (chevalleyHCoordinates w 0) (chevalleyFCoordinates w 0) =
      -(affineCartanMatrix 0 0 : K) • chevalleyFCoordinates w 0 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HF_01 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 (-1) (chevalleyHCoordinates w 0) (chevalleyFCoordinates w 1) =
      -(affineCartanMatrix 0 1 : K) • chevalleyFCoordinates w 1 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HF_02 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 (-1) (chevalleyHCoordinates w 0) (chevalleyFCoordinates w 2) =
      -(affineCartanMatrix 0 2 : K) • chevalleyFCoordinates w 2 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HF_10 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 (-1) (chevalleyHCoordinates w 1) (chevalleyFCoordinates w 0) =
      -(affineCartanMatrix 1 0 : K) • chevalleyFCoordinates w 0 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HF_11 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 (-1) (chevalleyHCoordinates w 1) (chevalleyFCoordinates w 1) =
      -(affineCartanMatrix 1 1 : K) • chevalleyFCoordinates w 1 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HF_12 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 (-1) (chevalleyHCoordinates w 1) (chevalleyFCoordinates w 2) =
      -(affineCartanMatrix 1 2 : K) • chevalleyFCoordinates w 2 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HF_20 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 (-1) (chevalleyHCoordinates w 2) (chevalleyFCoordinates w 0) =
      -(affineCartanMatrix 2 0 : K) • chevalleyFCoordinates w 0 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HF_21 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 (-1) (chevalleyHCoordinates w 2) (chevalleyFCoordinates w 1) =
      -(affineCartanMatrix 2 1 : K) • chevalleyFCoordinates w 1 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_HF_22 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 0 (-1) (chevalleyHCoordinates w 2) (chevalleyFCoordinates w 2) =
      -(affineCartanMatrix 2 2 : K) • chevalleyFCoordinates w 2 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_coordinates_HF (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    tensorCoordinateBracket w 0 (-1) (chevalleyHCoordinates w i) (chevalleyFCoordinates w j) =
      -(affineCartanMatrix i j : K) • chevalleyFCoordinates w j := by
  fin_cases i <;> fin_cases j
  · exact chevalley_coordinates_HF_00 w hw
  · exact chevalley_coordinates_HF_01 w hw
  · exact chevalley_coordinates_HF_02 w hw
  · exact chevalley_coordinates_HF_10 w hw
  · exact chevalley_coordinates_HF_11 w hw
  · exact chevalley_coordinates_HF_12 w hw
  · exact chevalley_coordinates_HF_20 w hw
  · exact chevalley_coordinates_HF_21 w hw
  · exact chevalley_coordinates_HF_22 w hw

private theorem chevalley_coordinates_EF_00 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 0) (chevalleyFCoordinates w 0) =
      if (0 : Fin 3)=0 then chevalleyHCoordinates w 0 else 0 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_EF_01 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 0) (chevalleyFCoordinates w 1) =
      if (0 : Fin 3)=1 then chevalleyHCoordinates w 0 else 0 := by
  funext r
  change tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 0) (chevalleyFCoordinates w 1) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_EF_02 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 0) (chevalleyFCoordinates w 2) =
      if (0 : Fin 3)=2 then chevalleyHCoordinates w 0 else 0 := by
  funext r
  change tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 0) (chevalleyFCoordinates w 2) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_EF_10 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 1) (chevalleyFCoordinates w 0) =
      if (1 : Fin 3)=0 then chevalleyHCoordinates w 1 else 0 := by
  funext r
  change tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 1) (chevalleyFCoordinates w 0) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_EF_11 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 1) (chevalleyFCoordinates w 1) =
      if (1 : Fin 3)=1 then chevalleyHCoordinates w 1 else 0 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_EF_12 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 1) (chevalleyFCoordinates w 2) =
      if (1 : Fin 3)=2 then chevalleyHCoordinates w 1 else 0 := by
  funext r
  change tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 1) (chevalleyFCoordinates w 2) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_EF_20 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 2) (chevalleyFCoordinates w 0) =
      if (2 : Fin 3)=0 then chevalleyHCoordinates w 2 else 0 := by
  funext r
  change tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 2) (chevalleyFCoordinates w 0) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_EF_21 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 2) (chevalleyFCoordinates w 1) =
      if (2 : Fin 3)=1 then chevalleyHCoordinates w 2 else 0 := by
  funext r
  change tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 2) (chevalleyFCoordinates w 1) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

private theorem chevalley_coordinates_EF_22 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w 2) (chevalleyFCoordinates w 2) =
      if (2 : Fin 3)=2 then chevalleyHCoordinates w 2 else 0 := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing, affineCartanMatrix,
      chevalleyHCoordinates, chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_coordinates_EF (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    tensorCoordinateBracket w 1 (-1) (chevalleyECoordinates w i) (chevalleyFCoordinates w j) =
      if i=j then chevalleyHCoordinates w i else 0 := by
  fin_cases i <;> fin_cases j
  · exact chevalley_coordinates_EF_00 w hw
  · exact chevalley_coordinates_EF_01 w hw
  · exact chevalley_coordinates_EF_02 w hw
  · exact chevalley_coordinates_EF_10 w hw
  · exact chevalley_coordinates_EF_11 w hw
  · exact chevalley_coordinates_EF_12 w hw
  · exact chevalley_coordinates_EF_20 w hw
  · exact chevalley_coordinates_EF_21 w hw
  · exact chevalley_coordinates_EF_22 w hw

end KanadeRussell.Tsuchioka.Fock
