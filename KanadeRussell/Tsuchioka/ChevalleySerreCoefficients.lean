import KanadeRussell.Tsuchioka.ChevalleyCoefficients

/-! Finite polynomial certificates for the two Serre families.
Each intermediate vector is evaluated by the proved concrete coordinate bracket.
All equalities are checked by Lean; the displayed polynomials are not assumptions. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace KanadeRussell.Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

theorem chevalley_E_step_0_1_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (1)
      (chevalleyECoordinates w 0) (chevalleyECoordinates w 1) = ![w^3/3 -2*w/3 +2/3, 4*w^2/3 +7*w/3 +4/3, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_E_step_0_1_2 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (2)
      (chevalleyECoordinates w 0) (![w^3/3 -2*w/3 +2/3, 4*w^2/3 +7*w/3 +4/3, 0, 0]) = 0 := by
  funext r
  change (tensorCoordinateBracket w (1) (2)
      (chevalleyECoordinates w 0) (![w^3/3 -2*w/3 +2/3, 4*w^2/3 +7*w/3 +4/3, 0, 0])) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_E_step_0_2_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (1)
      (chevalleyECoordinates w 0) (chevalleyECoordinates w 2) = 0 := by
  funext r
  change (tensorCoordinateBracket w (1) (1)
      (chevalleyECoordinates w 0) (chevalleyECoordinates w 2)) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_E_step_1_0_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (1)
      (chevalleyECoordinates w 1) (chevalleyECoordinates w 0) = ![-w^3/3 +2*w/3 -2/3, -4*w^2/3 -7*w/3 -4/3, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_E_step_1_0_2 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (2)
      (chevalleyECoordinates w 1) (![-w^3/3 +2*w/3 -2/3, -4*w^2/3 -7*w/3 -4/3, 0, 0]) = 0 := by
  funext r
  change (tensorCoordinateBracket w (1) (2)
      (chevalleyECoordinates w 1) (![-w^3/3 +2*w/3 -2/3, -4*w^2/3 -7*w/3 -4/3, 0, 0])) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_E_step_1_2_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (1)
      (chevalleyECoordinates w 1) (chevalleyECoordinates w 2) = ![w^3/3 -2*w/3, 2*w^2/3 +w +2/3, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_E_step_1_2_2 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (2)
      (chevalleyECoordinates w 1) (![w^3/3 -2*w/3, 2*w^2/3 +w +2/3, 0, 0]) = ![4*w^3/9 -8*w/9, -8*w^3/9 -20*w^2/9 -20*w/9 -8/9, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_E_step_1_2_3 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (3)
      (chevalleyECoordinates w 1) (![4*w^3/9 -8*w/9, -8*w^3/9 -20*w^2/9 -20*w/9 -8/9, 0, 0]) = ![4*w^3/9 -8*w/9, 28*w^3/9 +16*w^2/3 +28*w/9, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_E_step_1_2_4 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (4)
      (chevalleyECoordinates w 1) (![4*w^3/9 -8*w/9, 28*w^3/9 +16*w^2/3 +28*w/9, 0, 0]) = 0 := by
  funext r
  change (tensorCoordinateBracket w (1) (4)
      (chevalleyECoordinates w 1) (![4*w^3/9 -8*w/9, 28*w^3/9 +16*w^2/3 +28*w/9, 0, 0])) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_E_step_2_0_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (1)
      (chevalleyECoordinates w 2) (chevalleyECoordinates w 0) = 0 := by
  funext r
  change (tensorCoordinateBracket w (1) (1)
      (chevalleyECoordinates w 2) (chevalleyECoordinates w 0)) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_E_step_2_1_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (1)
      (chevalleyECoordinates w 2) (chevalleyECoordinates w 1) = ![-w^3/3 +2*w/3, -2*w^2/3 -w -2/3, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_E_step_2_1_2 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (1) (2)
      (chevalleyECoordinates w 2) (![-w^3/3 +2*w/3, -2*w^2/3 -w -2/3, 0, 0]) = 0 := by
  funext r
  change (tensorCoordinateBracket w (1) (2)
      (chevalleyECoordinates w 2) (![-w^3/3 +2*w/3, -2*w^2/3 -w -2/3, 0, 0])) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_0_1_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-1)
      (chevalleyFCoordinates w 0) (chevalleyFCoordinates w 1) = ![-9*w^3 +18*w -63/4, 9*w^3/2 +9*w^2/4 -9*w/2 -9/2, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_0_1_2 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-2)
      (chevalleyFCoordinates w 0) (![-9*w^3 +18*w -63/4, 9*w^3/2 +9*w^2/4 -9*w/2 -9/2, 0, 0]) = 0 := by
  funext r
  change (tensorCoordinateBracket w (-1) (-2)
      (chevalleyFCoordinates w 0) (![-9*w^3 +18*w -63/4, 9*w^3/2 +9*w^2/4 -9*w/2 -9/2, 0, 0])) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_0_2_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-1)
      (chevalleyFCoordinates w 0) (chevalleyFCoordinates w 2) = 0 := by
  funext r
  change (tensorCoordinateBracket w (-1) (-1)
      (chevalleyFCoordinates w 0) (chevalleyFCoordinates w 2)) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_1_0_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-1)
      (chevalleyFCoordinates w 1) (chevalleyFCoordinates w 0) = ![9*w^3 -18*w +63/4, -9*w^3/2 -9*w^2/4 +9*w/2 +9/2, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_1_0_2 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-2)
      (chevalleyFCoordinates w 1) (![9*w^3 -18*w +63/4, -9*w^3/2 -9*w^2/4 +9*w/2 +9/2, 0, 0]) = 0 := by
  funext r
  change (tensorCoordinateBracket w (-1) (-2)
      (chevalleyFCoordinates w 1) (![9*w^3 -18*w +63/4, -9*w^3/2 -9*w^2/4 +9*w/2 +9/2, 0, 0])) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_1_2_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-1)
      (chevalleyFCoordinates w 1) (chevalleyFCoordinates w 2) = ![-3*w^3/2 +3*w -9/4, 3*w^2/4 -3/2, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_1_2_2 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-2)
      (chevalleyFCoordinates w 1) (![-3*w^3/2 +3*w -9/4, 3*w^2/4 -3/2, 0, 0]) = ![-27*w^3/2 +27*w -45/2, -9*w^3/2 +9/2, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_1_2_3 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-3)
      (chevalleyFCoordinates w 1) (![-27*w^3/2 +27*w -45/2, -9*w^3/2 +9/2, 0, 0]) = ![-189*w^3/2 +189*w -162, 27*w^3 -27*w/2, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_1_2_4 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-4)
      (chevalleyFCoordinates w 1) (![-189*w^3/2 +189*w -162, 27*w^3 -27*w/2, 0, 0]) = 0 := by
  funext r
  change (tensorCoordinateBracket w (-1) (-4)
      (chevalleyFCoordinates w 1) (![-189*w^3/2 +189*w -162, 27*w^3 -27*w/2, 0, 0])) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_2_0_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-1)
      (chevalleyFCoordinates w 2) (chevalleyFCoordinates w 0) = 0 := by
  funext r
  change (tensorCoordinateBracket w (-1) (-1)
      (chevalleyFCoordinates w 2) (chevalleyFCoordinates w 0)) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_2_1_1 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-1)
      (chevalleyFCoordinates w 2) (chevalleyFCoordinates w 1) = ![3*w^3/2 -3*w +9/4, -3*w^2/4 +3/2, 0, 0] := by
  funext r
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

theorem chevalley_F_step_2_1_2 (w : K) (hw : w^4-w^2+1=0) :
    tensorCoordinateBracket w (-1) (-2)
      (chevalleyFCoordinates w 2) (![3*w^3/2 -3*w +9/4, -3*w^2/4 +3/2, 0, 0]) = 0 := by
  funext r
  change (tensorCoordinateBracket w (-1) (-2)
      (chevalleyFCoordinates w 2) (![3*w^3/2 -3*w +9/4, -3*w^2/4 +3/2, 0, 0])) r = (0 : K)
  fin_cases r <;>
    norm_num [tensorCoordinateBracket, tensorModeStructure, tensorModeRawStructure,
      normalizeTensorCoordinates, tensorHeisenbergPairing,
      chevalleyECoordinates, chevalleyFCoordinates,
      IsMode, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      RootData.rootWeight_second, contraction_one w hw,
      Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial, Int.toNat,
      Coefficients.pCoeff, Scalar.cPrime, Scalar.rootSecondResidue] <;> grind only

end KanadeRussell.Tsuchioka.Fock
