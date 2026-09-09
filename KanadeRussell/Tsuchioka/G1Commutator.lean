import KanadeRussell.Tsuchioka.CentralEuler
import KanadeRussell.Tsuchioka.CommutatorScalar
import KanadeRussell.Tsuchioka.FiniteModeRelations

/-! The first generalized commutator on the constructed Fock modes. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

theorem sameResidue_G1 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    sameResidue w f a b (Scalar.antisymmetricFourier (Scalar.G w 0 ^ 2 * Scalar.G w 0)) =
      (Coefficients.pCoeff w * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
        mode w (a + b) f +
      (Scalar.rootSecondResidue w * (w ^ (4 * a + 9 * b) - w ^ (9 * a + 4 * b)) / 12) •
        secondRootMode w (a + b) f +
      (if a + b = 0 then (Scalar.cPrime w * (a : K) * (-1 : K) ^ a / 24) • f else 0) := by
  rw [show Scalar.G w 0 ^ 2 * Scalar.G w 0 = Scalar.G w 0 ^ 3 from (pow_succ _ 2).symm,
    Scalar.G1_cube_fourier w hw]
  change sameResidue w f a b
    (Coefficients.pCoeff w • (Scalar.delta (w ^ (-4 : ℤ)) - Scalar.delta (w ^ 4)) +
      Scalar.rootSecondResidue w • (Scalar.delta (w ^ (-5 : ℤ)) - Scalar.delta (w ^ 5)) +
      (2 * Scalar.cPrime w) • Scalar.eulerDelta (-1 : K)) = _
  simp only [map_add, map_sub, map_smul, sameResidue_delta_four w hw,
    sameResidue_delta_eight w hw, sameResidue_delta_five w hw,
    sameResidue_delta_seven w hw, sameResidue_euler_central w hw]
  by_cases hab : a + b = 0 <;> simp only [hab, if_true, if_false, smul_add, smul_sub,
    smul_smul, smul_zero, add_zero] <;> module

theorem mixedResidue_G1 (w : K) (f : Space K) (a b : ℤ) :
    mixedResidue w f a b
      (Scalar.antisymmetricFourier (Scalar.H w (-Scalar.exponents 0) * Scalar.G w 0)) = 0 := by
  rw [Scalar.G, Scalar.H_neg_mul, Scalar.antisymmetricFourier_one, map_zero]

/-- The first relation of source Theorem 3.2, with its central derivative term
computed from the summed normal product. -/
theorem G1_commutator (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    quadraticConvolution w (Scalar.G w 0) f a b -
      quadraticConvolution w (Scalar.G w 0) f b a =
      (Coefficients.pCoeff w * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
        mode w (a + b) f +
      (Scalar.rootSecondResidue w * (w ^ (4 * a + 9 * b) - w ^ (9 * a + 4 * b)) / 12) •
        secondRootMode w (a + b) f +
      (if a + b = 0 then (Scalar.cPrime w * (a : K) * (-1 : K) ^ a / 24) • f else 0) := by
  rw [quadraticConvolution_antisymmetric_kernel w hw, sameResidue_G1 w hw,
    mixedResidue_G1, add_zero]

theorem G1_commutator_word_finite (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      skewSum (fun v => (highestWeightAction w).wordValue (v ++ t))
        (fun p => PowerSeries.coeff p (Scalar.G w 0)) a b (M + 1) =
        (Coefficients.pCoeff w * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
          mode w (a + b) ((highestWeightAction w).wordValue t) +
        (Scalar.rootSecondResidue w * (w ^ (4 * a + 9 * b) - w ^ (9 * a + 4 * b)) / 12) •
          secondRootMode w (a + b) ((highestWeightAction w).wordValue t) +
        (if a + b = 0 then (Scalar.cPrime w * (a : K) * (-1 : K) ^ a / 24) •
          (highestWeightAction w).wordValue t else 0) := by
  obtain ⟨N, hN⟩ := pair_tails_eventually_zero w a b t
  refine ⟨N, ?_⟩
  intro M hM
  rw [← pair_convolutions_eq_skewSum w (Scalar.G w 0) a b t (M + 1)
    (fun p hp => hN p (by omega))]
  exact G1_commutator w hw _ a b

end KanadeRussell.Tsuchioka.Fock
