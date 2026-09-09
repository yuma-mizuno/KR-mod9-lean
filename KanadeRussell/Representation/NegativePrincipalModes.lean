import KanadeRussell.Representation.PositivePrincipalModes
import KanadeRussell.Representation.PrincipalModeInactiveDual

/-! The inverse-pairing rows are actual negative eigenmodes, with the
opposite root shifts. Their ordered products recover each original summand. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

noncomputable def negativePrincipalMode (w : K) (n : ℕ) (r : Fin 3) :
    Module.End K (Space K) :=
  principalModeCombination w (-((n : ℤ)+1))
    (principalDualWeightCoordinates w ((n : ℤ)+1) (positiveModeResidue n) r)

noncomputable def negativeCyclicPrincipalMode (w : K) (seed : Space K) (n : ℕ) (r : Fin 3) :
    Module.End K (tensorCyclicSpan w seed) :=
  tensorCyclicPrincipalModeCombination w seed (-((n : ℤ)+1))
    (principalDualWeightCoordinates w ((n : ℤ)+1) (positiveModeResidue n) r)

theorem negativeModeCoordinates_eigen (w : K) (hw : w^4-w^2+1=0)
    (n : ℕ) (r i : Fin 3) :
    (principalCartanMatrix w (-((n : ℤ)+1)) i).mulVec
        (principalDualWeightCoordinates w ((n : ℤ)+1) (positiveModeResidue n) r) =
      (∑ j : Fin 3, (affineCartanMatrix i j : K) * (-(positiveModeOccupation n r j : K))) •
        principalDualWeightCoordinates w ((n : ℤ)+1) (positiveModeResidue n) r := by
  have hcongr : ((n : ℤ)+1) % 12 = (((positiveModeResidue n).val+1 : ℕ) : ℤ) % 12 := by
    simpa only [Nat.cast_add, Nat.cast_one] using positiveModeResidue_congr n
  have h := principalDualWeightCoordinates_eigen w hw ((n : ℤ)+1)
    (positiveModeResidue n) hcongr i r
  by_cases hr : principalWeightSlotActive (positiveModeResidue n) r
  · simp only [principalFrameEigenvalue, if_pos hr] at h
    simpa only [mul_neg, Finset.sum_neg_distrib, positiveModeOccupation_cartan] using h
  · rw [principalDualWeightCoordinates_eq_zero_of_inactive w ((n : ℤ)+1)
      (positiveModeResidue n) hcongr r hr]
    simp

theorem negativePrincipalMode_H (w : K) (hw : w^4-w^2+1=0)
    (n : ℕ) (r i : Fin 3) :
    ⁅chevalleyH w i, negativePrincipalMode w n r⁆ =
      (∑ j : Fin 3, (affineCartanMatrix i j : K) * (-(positiveModeOccupation n r j : K))) •
        negativePrincipalMode w n r :=
  principalModeCombination_eigenoperator w hw _ (by omega) i _ _
    (negativeModeCoordinates_eigen w hw n r i)

theorem negativePrincipalMode_D (w : K) (n : ℕ) (r : Fin 3) :
    ⁅Fock.principalDerivation (K := K), negativePrincipalMode w n r⁆ =
      (-((n : K)+1)) • negativePrincipalMode w n r := by
  simpa only [negativePrincipalMode, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one] using
    principalDerivation_lie_principalModeCombination w (-((n : ℤ)+1))
      (principalDualWeightCoordinates w ((n : ℤ)+1) (positiveModeResidue n) r)

theorem tensorPrincipalModule_negativeMode_mem_rootGrade (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (n : ℕ) (r : Fin 3) (beta : RootCoefficients)
    (p : tensorCyclicSpan w seed) (hp : p ∈ M.rootGrade beta) :
    negativeCyclicPrincipalMode w seed n r p ∈ M.rootGrade (beta+positiveModeOccupation n r) := by
  have hdegree : totalDegree (-positiveModeOccupation n r) = -((n : ℤ)+1) := by
    simp only [totalDegree, Pi.neg_apply, Finset.sum_neg_distrib]
    exact congrArg Neg.neg (positiveModeOccupation_degree n r)
  have h := tensorPrincipalModule_modeCombination_mem_rootGrade w hw seed M haction d hD
    (-positiveModeOccupation n r) (by rw [hdegree]; omega)
    (principalDualWeightCoordinates w ((n : ℤ)+1) (positiveModeResidue n) r)
    (by
      intro i
      rw [hdegree]
      simpa only [Pi.neg_apply, Int.cast_neg] using negativeModeCoordinates_eigen w hw n r i)
    beta p hp
  simpa only [negativeCyclicPrincipalMode, hdegree, sub_neg_eq_add] using h

theorem normalOrderedMode_eq_negative_positive (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    normalOrderedMode w ((n : ℤ)+1) =
      ∑ r : Fin 3, negativePrincipalMode w n r * positivePrincipalMode w n r := by
  exact normalOrderedMode_eq_weight_sum w hw ((n : ℤ)+1) (positiveModeResidue n)
    (by simpa only [Nat.cast_add, Nat.cast_one] using positiveModeResidue_congr n)

end KanadeRussell.Representation
