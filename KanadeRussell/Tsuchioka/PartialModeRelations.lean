import KanadeRussell.Tsuchioka.MixedResidueVanishing
import KanadeRussell.Tsuchioka.CentralEuler
import KanadeRussell.Tsuchioka.CombinedFourier
import KanadeRussell.Tsuchioka.FiniteModeRelations

/-! The two partial mode relations in source Theorem 3.2. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

theorem sameResidue_G3 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    sameResidue w f a b (Scalar.symmetricFourier (Scalar.G w 0 ^ 2 * Scalar.G w 2)) =
      (Coefficients.mCoeff w * (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) / 12) •
        secondRootMode w (a + b) f +
      (if a + b = 0 then (Scalar.bCoeff w * (-1 : K) ^ a / 48) • f else 0) := by
  rw [Scalar.same_G3_fourier w hw]
  change sameResidue w f a b
    (Coefficients.mCoeff w • (Scalar.delta (w ^ (-5 : ℤ)) + Scalar.delta (w ^ 5)) +
      Scalar.bCoeff w • Scalar.delta (-1 : K)) = _
  simp only [map_add, map_smul, sameResidue_delta_five w hw,
    sameResidue_delta_seven w hw, sameResidue_delta_central w hw]
  by_cases hab : a + b = 0 <;> simp only [hab, if_true, if_false, smul_add, smul_smul,
    smul_zero, add_zero] <;> module

theorem mixedResidue_G3 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) (hab : ¬3 ∣ a + b) :
    mixedResidue w f a b
      (Scalar.symmetricFourier (Scalar.H w (-Scalar.exponents 0) * Scalar.G w 2)) =
      (-1 : K) ^ (a + b) • mode w (a + b) f := by
  rw [Scalar.distinct_G3_fourier w hw]
  change mixedResidue w f a b
    ((6 : K) • Scalar.delta (1 : K) -
      (2 : K) • (Scalar.delta (w ^ 2) + Scalar.delta (w ^ (-2 : ℤ)))) = _
  simp only [map_sub, map_add, map_smul, mixedResidue_delta_one w hw,
    mixedResidue_delta_two w hw f a b hab, mixedResidue_delta_neg_two w hw f a b hab,
    add_zero, smul_zero, sub_zero, smul_smul]
  congr 1
  ring

/-- The third relation of Theorem 3.2, with its required total-mode restriction. -/
theorem G3_anticommutator (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) (hab : ¬3 ∣ a + b) :
    quadraticConvolution w (Scalar.G w 2) f a b +
      quadraticConvolution w (Scalar.G w 2) f b a =
      (Coefficients.mCoeff w * (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) / 12) •
        secondRootMode w (a + b) f +
      (if a + b = 0 then (Scalar.bCoeff w * (-1 : K) ^ a / 48) • f else 0) +
      (-1 : K) ^ (a + b) • mode w (a + b) f := by
  rw [quadraticConvolution_symmetric_kernel w hw, sameResidue_G3 w hw,
    mixedResidue_G3 w hw f a b hab]

theorem sameResidue_G6 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    sameResidue w f a b (Scalar.antisymmetricFourier (Scalar.G w 0 ^ 2 * Scalar.G6 w)) =
      (Coefficients.pCoeff w * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
        mode w (a + b) f +
      (if a + b = 0 then
        ((1 - 3 * (Coefficients.pCoeff w / Coefficients.qCoeff w)) *
          (a : K) * (-1 : K) ^ a / 12) • f else 0) := by
  rw [Scalar.same_G6_fourier w hw]
  change sameResidue w f a b
    ((4 * (1 - 3 * (Coefficients.pCoeff w / Coefficients.qCoeff w))) •
        Scalar.eulerDelta (-1 : K) -
      Coefficients.pCoeff w • (Scalar.delta (w ^ 4) - Scalar.delta (w ^ (-4 : ℤ)))) = _
  simp only [map_sub, map_smul, sameResidue_delta_four w hw,
    sameResidue_delta_eight w hw, sameResidue_euler_central w hw]
  by_cases hab : a + b = 0 <;> simp only [hab, if_true, if_false, smul_sub, smul_smul,
    smul_zero, add_zero] <;> module

theorem mixedResidue_G6 (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) (hab : ¬3 ∣ a + b) :
    mixedResidue w f a b
      (Scalar.antisymmetricFourier (Scalar.H w (-Scalar.exponents 0) * Scalar.G6 w)) = 0 := by
  rw [Scalar.distinct_G6_fourier w hw]
  change mixedResidue w f a b
    ((Coefficients.pCoeff w / 3) • (Scalar.delta (w ^ (-2 : ℤ)) - Scalar.delta (w ^ 2))) = _
  simp only [map_smul, map_sub, mixedResidue_delta_two w hw f a b hab,
    mixedResidue_delta_neg_two w hw f a b hab, sub_self, smul_zero]

/-- The fourth relation of Theorem 3.2, using the actual source G6 combination. -/
theorem G6_commutator (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) (hab : ¬3 ∣ a + b) :
    quadraticConvolution w (Scalar.G6 w) f a b -
      quadraticConvolution w (Scalar.G6 w) f b a =
      (Coefficients.pCoeff w * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
        mode w (a + b) f +
      (if a + b = 0 then
        ((1 - 3 * (Coefficients.pCoeff w / Coefficients.qCoeff w)) *
          (a : K) * (-1 : K) ^ a / 12) • f else 0) := by
  rw [quadraticConvolution_antisymmetric_kernel w hw, sameResidue_G6 w hw,
    mixedResidue_G6 w hw f a b hab, add_zero]

theorem G3_anticommutator_word_finite (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (hab : ¬3 ∣ a + b) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      symmetricSum (fun v => (highestWeightAction w).wordValue (v ++ t))
        (fun p => PowerSeries.coeff p (Scalar.G w 2)) a b (M + 1) =
        (Coefficients.mCoeff w * (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) / 12) •
          secondRootMode w (a + b) ((highestWeightAction w).wordValue t) +
        (if a + b = 0 then (Scalar.bCoeff w * (-1 : K) ^ a / 48) •
          (highestWeightAction w).wordValue t else 0) +
        (-1 : K) ^ (a + b) • mode w (a + b) ((highestWeightAction w).wordValue t) := by
  obtain ⟨N, hN⟩ := pair_tails_eventually_zero w a b t
  refine ⟨N, ?_⟩
  intro M hM
  rw [← pair_convolutions_eq_symmetricSum w (Scalar.G w 2) a b t (M + 1)
    (fun p hp => hN p (by omega))]
  exact G3_anticommutator w hw _ a b hab

theorem G6_commutator_word_finite (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (hab : ¬3 ∣ a + b) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      skewSum (fun v => (highestWeightAction w).wordValue (v ++ t))
        (fun p => PowerSeries.coeff p (Scalar.G6 w)) a b (M + 1) =
        (Coefficients.pCoeff w * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
          mode w (a + b) ((highestWeightAction w).wordValue t) +
        (if a + b = 0 then
          ((1 - 3 * (Coefficients.pCoeff w / Coefficients.qCoeff w)) *
            (a : K) * (-1 : K) ^ a / 12) •
          (highestWeightAction w).wordValue t else 0) := by
  obtain ⟨N, hN⟩ := pair_tails_eventually_zero w a b t
  refine ⟨N, ?_⟩
  intro M hM
  rw [← pair_convolutions_eq_skewSum w (Scalar.G6 w) a b t (M + 1)
    (fun p hp => hN p (by omega))]
  exact G6_commutator w hw _ a b hab

end KanadeRussell.Tsuchioka.Fock
