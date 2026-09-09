import KanadeRussell.Tsuchioka.TensorResidueMaps
import KanadeRussell.Tsuchioka.TensorCommutatorKernel

/-! The complete first-root commutator for the source tensor fields,
including first- and second-root modes, the Heisenberg mode, and the
level-three central scalar. Other root brackets and module identification
are not assumed. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorSameResidue_G1_cube (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorSameResidue w f a b (Scalar.antisymmetricFourier (Scalar.G w 0 ^ 3)) =
      (Coefficients.pCoeff w * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
        tensorRootMode w (simpleRoot 0) (a + b) f +
      (Scalar.rootSecondResidue w * (w ^ (4 * a + 9 * b) - w ^ (9 * a + 4 * b)) / 12) •
        tensorRootMode w (simpleRoot 1) (a + b) f -
      (Scalar.cPrime w * (-1 : K) ^ a / 6) • heisenbergMode w (a + b) f +
      (if a + b = 0 then (Scalar.cPrime w * (a : K) * (-1 : K) ^ a / 24) • f else 0) := by
  rw [Scalar.G1_cube_fourier w hw]
  change tensorSameResidue w f a b
    (Coefficients.pCoeff w • (Scalar.delta (w ^ (-4 : ℤ)) - Scalar.delta (w ^ 4)) +
      Scalar.rootSecondResidue w • (Scalar.delta (w ^ (-5 : ℤ)) - Scalar.delta (w ^ 5)) +
      (2 * Scalar.cPrime w) • Scalar.eulerDelta (-1 : K)) = _
  simp only [map_add, map_sub, map_smul, tensorSameResidue_delta_four w hw,
    tensorSameResidue_delta_eight w hw, tensorSameResidue_delta_five w hw,
    tensorSameResidue_delta_seven w hw, tensorSameResidue_euler_central w hw]
  by_cases hab : a + b = 0 <;> simp only [hab, if_true, if_false, smul_add, smul_sub,
    smul_smul, smul_zero, add_zero] <;> module

/-- The actual tensor first-root commutator, on every polynomial input and
at arbitrary integer indices. Its Heisenberg term is retained in all degrees. -/
theorem tensorFirstRoot_commutator (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorRootMode w (simpleRoot 0) a (tensorRootMode w (simpleRoot 0) b f) -
        tensorRootMode w (simpleRoot 0) b (tensorRootMode w (simpleRoot 0) a f) =
      (Coefficients.pCoeff w * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
        tensorRootMode w (simpleRoot 0) (a + b) f +
      (Scalar.rootSecondResidue w * (w ^ (4 * a + 9 * b) - w ^ (9 * a + 4 * b)) / 12) •
        tensorRootMode w (simpleRoot 1) (a + b) f -
      (Scalar.cPrime w * (-1 : K) ^ a / 6) • heisenbergMode w (a + b) f +
      (if a + b = 0 then (Scalar.cPrime w * (a : K) * (-1 : K) ^ a / 24) • f else 0) := by
  rw [tensorRootMode_first_commutator_kernel w hw]
  change tensorSameResidue w f a b (Scalar.antisymmetricFourier (Scalar.G w 0 ^ 3)) = _
  exact tensorSameResidue_G1_cube w hw f a b

end KanadeRussell.Tsuchioka.Fock
