import KanadeRussell.Tsuchioka.MixedRootScalarExpansion
import KanadeRussell.Tsuchioka.TensorPairResidues

/-! The complete mixed first/second-root tensor commutator on every
polynomial input. All four simple-pole lattice fusions are discharged. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.RootData

def mixedRootRepresentative : Fin 4 → Lattice :=
  ![simpleRoot 1, simpleRoot 0, simpleRoot 0, simpleRoot 1]

def mixedRootOrbitPower : Fin 4 → ℕ := ![7, 3, 8, 5]

theorem mixed_root_fusion (k : Fin 4) :
    (coxeter^[(Scalar.mixedRootPole k).val]) (simpleRoot 0) + simpleRoot 1 =
      (coxeter^[mixedRootOrbitPower k]) (mixedRootRepresentative k) := by
  fin_cases k <;> decide

end KanadeRussell.Tsuchioka.RootData

namespace KanadeRussell.Tsuchioka.Fock

open RootData (simpleRoot mixedRootRepresentative mixedRootOrbitPower)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorMixedRoot_commutator_sum (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorRootMode w (simpleRoot 0) a (tensorRootMode w (simpleRoot 1) b f) -
        tensorRootMode w (simpleRoot 1) b (tensorRootMode w (simpleRoot 0) a f) =
      ∑ k : Fin 4, (Scalar.mixedRootResidue w k *
        w ^ (((mixedRootOrbitPower k : ℤ) - (Scalar.mixedRootPole k).val) * a +
          mixedRootOrbitPower k * b) / 12) •
            tensorRootMode w (mixedRootRepresentative k) (a + b) f := by
  rw [tensorRootMode_commutator_kernel w hw]
  change tensorRootPairResidue w (simpleRoot 0) (simpleRoot 1) f a b
    (Scalar.rootCommutatorKernel w (simpleRoot 0) (simpleRoot 1)) = _
  rw [Scalar.rootCommutatorKernel_first_second w hw]
  have hk : (fun n => ∑ k : Fin 4, Scalar.mixedRootResidue w k *
      (Scalar.phasePolynomial w (Scalar.mixedRootPole k)) ^ n) =
      ∑ k : Fin 4, Scalar.mixedRootResidue w k •
        (fun n : ℤ => (Scalar.phasePolynomial w (Scalar.mixedRootPole k)) ^ n) := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hk, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul, tensorRootPairResidue_phase_fusion w hw
    (simpleRoot 0) (simpleRoot 1) (mixedRootRepresentative k)
    (Scalar.mixedRootPole k) (mixedRootOrbitPower k) (RootData.mixed_root_fusion k)]
  rw [smul_smul]
  congr 1
  ring

/-- The full mixed bracket, with both root families and their exact phases. -/
theorem tensorMixedRoot_commutator (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorRootMode w (simpleRoot 0) a (tensorRootMode w (simpleRoot 1) b f) -
        tensorRootMode w (simpleRoot 1) b (tensorRootMode w (simpleRoot 0) a f) =
      (Coefficients.pCoeff (-w) * (w ^ (a + 3 * b) - w ^ (-a + 8 * b)) / 12) •
        tensorRootMode w (simpleRoot 0) (a + b) f +
      (Coefficients.pCoeff w * (w ^ (-6 * a + 5 * b) - w ^ (7 * a + 7 * b)) / 12) •
        tensorRootMode w (simpleRoot 1) (a + b) f := by
  rw [tensorMixedRoot_commutator_sum w hw]
  norm_num [Fin.sum_univ_succ, mixedRootRepresentative, mixedRootOrbitPower,
    Scalar.mixedRootResidue, Scalar.mixedRootPole]
  module

end KanadeRussell.Tsuchioka.Fock
