import KanadeRussell.Tsuchioka.SecondRootScalarExpansion
import KanadeRussell.Tsuchioka.TensorRootCentralResidues

/-! The complete second-root self commutator on the source tensor Fock
space, with the two root families, projected Heisenberg term, and centre. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.RootData

theorem second_fusion_four :
    (coxeter^[4]) (simpleRoot 1) + simpleRoot 1 = (coxeter^[2]) (simpleRoot 1) := by decide

theorem second_fusion_eight :
    (coxeter^[8]) (simpleRoot 1) + simpleRoot 1 = (coxeter^[10]) (simpleRoot 1) := by decide

theorem second_fusion_eleven :
    (coxeter^[11]) (simpleRoot 1) + simpleRoot 1 = (coxeter^[5]) (simpleRoot 0) := by decide

theorem second_fusion_one :
    (coxeter^[1]) (simpleRoot 1) + simpleRoot 1 = (coxeter^[6]) (simpleRoot 0) := by decide

end KanadeRussell.Tsuchioka.RootData

namespace KanadeRussell.Tsuchioka.Fock

open RootData (simpleRoot rootWeight)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorSecondResidue_delta_four (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorRootPairResidue w (simpleRoot 1) (simpleRoot 1) f a b
      (Scalar.delta (w ^ (-4 : ℤ))) =
      (w ^ (-2 * a + 2 * b) / 12) • tensorRootMode w (simpleRoot 1) (a + b) f := by
  change tensorRootPairResidue w (simpleRoot 1) (simpleRoot 1) f a b
    (fun n : ℤ => (w ^ (-4 : ℤ)) ^ n) = _
  have h := tensorRootPairResidue_phase_fusion w hw (simpleRoot 1) (simpleRoot 1)
    (simpleRoot 1) (4 : Fin 12) 2 RootData.second_fusion_four f a b
  simpa [← Scalar.negative_phase w hw, Scalar.delta] using h

theorem tensorSecondResidue_delta_eight (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorRootPairResidue w (simpleRoot 1) (simpleRoot 1) f a b
      (Scalar.delta (w ^ 4)) =
      (w ^ (2 * a - 2 * b) / 12) • tensorRootMode w (simpleRoot 1) (a + b) f := by
  change tensorRootPairResidue w (simpleRoot 1) (simpleRoot 1) f a b
    (fun n : ℤ => (w ^ 4) ^ n) = _
  have h := tensorRootPairResidue_phase_fusion w hw (simpleRoot 1) (simpleRoot 1)
    (simpleRoot 1) (8 : Fin 12) 10 RootData.second_fusion_eight f a b
  have hp : Scalar.phasePolynomial w 8 = w ^ 4 := by
    change w ^ 2 - 1 = w ^ 4
    linear_combination -hw
  rw [hp] at h
  have he : w ^ (2 * a + 10 * b) = w ^ (2 * a - 2 * b) :=
    Coefficients.zpow_eq_of_mod w hw _ _ (by omega)
  norm_num at h
  rw [he] at h
  exact h

theorem tensorSecondResidue_delta_eleven (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorRootPairResidue w (simpleRoot 1) (simpleRoot 1) f a b (Scalar.delta w) =
      (w ^ (-6 * a + 5 * b) / 12) • tensorRootMode w (simpleRoot 0) (a + b) f := by
  change tensorRootPairResidue w (simpleRoot 1) (simpleRoot 1) f a b
    (fun n : ℤ => (w) ^ n) = _
  have h := tensorRootPairResidue_phase_fusion w hw (simpleRoot 1) (simpleRoot 1)
    (simpleRoot 0) (11 : Fin 12) 5 RootData.second_fusion_eleven f a b
  simpa [Scalar.phasePolynomial, Scalar.delta] using h

theorem tensorSecondResidue_delta_one (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorRootPairResidue w (simpleRoot 1) (simpleRoot 1) f a b
      (Scalar.delta (w ^ (-1 : ℤ))) =
      (w ^ (5 * a + 6 * b) / 12) • tensorRootMode w (simpleRoot 0) (a + b) f := by
  change tensorRootPairResidue w (simpleRoot 1) (simpleRoot 1) f a b
    (fun n : ℤ => (w ^ (-1 : ℤ)) ^ n) = _
  have h := tensorRootPairResidue_phase_fusion w hw (simpleRoot 1) (simpleRoot 1)
    (simpleRoot 0) (1 : Fin 12) 6 RootData.second_fusion_one f a b
  simpa [← Scalar.negative_phase w hw, Scalar.delta] using h

/-- The actual second-root self bracket for arbitrary integer indices and
polynomial inputs. The central Euler term retains the full root weight. -/
theorem tensorSecondRoot_commutator (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorRootMode w (simpleRoot 1) a (tensorRootMode w (simpleRoot 1) b f) -
        tensorRootMode w (simpleRoot 1) b (tensorRootMode w (simpleRoot 1) a f) =
      (Coefficients.pCoeff (-w) * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
        tensorRootMode w (simpleRoot 1) (a + b) f +
      (Scalar.rootSecondResidue (-w) * (w ^ (-6 * a + 5 * b) - w ^ (5 * a + 6 * b)) / 12) •
        tensorRootMode w (simpleRoot 0) (a + b) f -
      (Scalar.cPrime (-w) * (-1 : K) ^ a * rootWeight (w ^ (a + b)) (simpleRoot 1) / 6) •
        heisenbergMode w (a + b) f +
      (if a + b = 0 then (Scalar.cPrime (-w) * (a : K) * (-1 : K) ^ a / 24) • f else 0) := by
  rw [tensorRootMode_commutator_kernel w hw]
  change tensorRootPairResidue w (simpleRoot 1) (simpleRoot 1) f a b
    (Scalar.rootCommutatorKernel w (simpleRoot 1) (simpleRoot 1)) = _
  rw [Scalar.rootCommutatorKernel_second_second w hw]
  change tensorRootPairResidue w (simpleRoot 1) (simpleRoot 1) f a b
    (Coefficients.pCoeff (-w) • (Scalar.delta (w ^ (-4 : ℤ)) - Scalar.delta (w ^ 4)) +
      Scalar.rootSecondResidue (-w) • (Scalar.delta w - Scalar.delta (w ^ (-1 : ℤ))) +
      (2 * Scalar.cPrime (-w)) • Scalar.eulerDelta (-1 : K)) = _
  simp only [map_add, map_sub, map_smul, tensorSecondResidue_delta_four w hw,
    tensorSecondResidue_delta_eight w hw, tensorSecondResidue_delta_eleven w hw,
    tensorSecondResidue_delta_one w hw, tensorRootSelfResidue_euler_central w hw]
  by_cases hab : a + b = 0 <;>
    simp only [hab, if_true, if_false, smul_add, smul_smul, smul_zero, add_zero] <;> module

end KanadeRussell.Tsuchioka.Fock
