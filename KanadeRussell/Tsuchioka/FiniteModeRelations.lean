import KanadeRussell.Tsuchioka.G2Anticommutator
import KanadeRussell.Tsuchioka.FockGrading
import KanadeRussell.Tsuchioka.OrderingReduction

/-! Finite natural-index mode relations on each highest-weight suffix vector. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

theorem quadraticConvolution_eq_sum_of_tail (w : K) (h : PowerSeries K)
    (f : Space K) (a b : ℤ) (N : ℕ)
    (htail : ∀ p : ℕ, N ≤ p → mode w (a - p) (mode w (b + p) f) = 0) :
    quadraticConvolution w h f a b =
      ∑ p ∈ Finset.range N, PowerSeries.coeff p h • mode w (a - p) (mode w (b + p) f) := by
  classical
  let g (n : ℤ) := positive h n • mode w (a - n) (mode w (b + n) f)
  have hs : Function.support g ⊆
      ((Finset.range N).image (fun p : ℕ => (p : ℤ)) : Set ℤ) := by
    intro n hn
    have hn0 : 0 ≤ n := by
      by_contra hn0
      exact hn (by simp [g, positive, hn0])
    have hnN : n.toNat < N := by
      by_contra hnN
      have ht := htail n.toNat (by omega)
      have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
      rw [he] at ht
      exact hn (by simp [g, ht])
    exact Finset.mem_image.mpr ⟨n.toNat, Finset.mem_range.mpr hnN, Int.toNat_of_nonneg hn0⟩
  change (∑ᶠ n : ℤ, g n) = _
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_image]
  · simp only [g, positive_nat]
  · intro i hi j hj hij
    exact Int.ofNat_injective hij

theorem pair_convolutions_eq_symmetricSum (w : K) (h : PowerSeries K)
    (a b : ℤ) (t : Word) (N : ℕ)
    (htail : ∀ p : ℕ, N ≤ p →
      (highestWeightAction w).wordValue ([a - p, b + p] ++ t) = 0 ∧
      (highestWeightAction w).wordValue ([b - p, a + p] ++ t) = 0) :
    quadraticConvolution w h ((highestWeightAction w).wordValue t) a b +
      quadraticConvolution w h ((highestWeightAction w).wordValue t) b a =
      symmetricSum (fun v => (highestWeightAction w).wordValue (v ++ t))
        (fun p => PowerSeries.coeff p h) a b N := by
  have hf : ∀ p : ℕ, N ≤ p →
      mode w (a - p) (mode w (b + p) ((highestWeightAction w).wordValue t)) = 0 :=
    fun p hp => (htail p hp).1
  have hr : ∀ p : ℕ, N ≤ p →
      mode w (b - p) (mode w (a + p) ((highestWeightAction w).wordValue t)) = 0 :=
    fun p hp => (htail p hp).2
  rw [quadraticConvolution_eq_sum_of_tail w h _ a b N hf,
    quadraticConvolution_eq_sum_of_tail w h _ b a N hr]
  simp only [symmetricSum, smul_add, Finset.sum_add_distrib]
  rfl

/-- A common finite cutoff works for every later truncation of the G2 relation
on each word suffix. Thus its use in algebraic straightening needs no infinite sum. -/
theorem G2_anticommutator_word_finite (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      symmetricSum (fun v => (highestWeightAction w).wordValue (v ++ t))
        (fun p => PowerSeries.coeff p (Scalar.G w 1)) a b (M + 1) =
        (Scalar.aPrime w * (w ^ (-2 * a + 2 * b) + w ^ (2 * a - 2 * b)) / 12) •
          mode w (a + b) ((highestWeightAction w).wordValue t) +
        (Coefficients.tCoeff w * (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) / 12) •
          secondRootMode w (a + b) ((highestWeightAction w).wordValue t) +
        (if a + b = 0 then (Scalar.cPrime w * (-1 : K) ^ a / 48) •
          (highestWeightAction w).wordValue t else 0) +
        ((-1 : K) ^ (a + b) / 3) • mode w (a + b) ((highestWeightAction w).wordValue t) := by
  obtain ⟨N, hN⟩ := pair_tails_eventually_zero w a b t
  refine ⟨N, ?_⟩
  intro M hM
  rw [← pair_convolutions_eq_symmetricSum w (Scalar.G w 1) a b t (M + 1)
    (fun p hp => hN p (by omega))]
  exact G2_anticommutator w hw _ a b

theorem pair_convolutions_eq_skewSum (w : K) (h : PowerSeries K)
    (a b : ℤ) (t : Word) (N : ℕ)
    (htail : ∀ p : ℕ, N ≤ p →
      (highestWeightAction w).wordValue ([a - p, b + p] ++ t) = 0 ∧
      (highestWeightAction w).wordValue ([b - p, a + p] ++ t) = 0) :
    quadraticConvolution w h ((highestWeightAction w).wordValue t) a b -
      quadraticConvolution w h ((highestWeightAction w).wordValue t) b a =
      skewSum (fun v => (highestWeightAction w).wordValue (v ++ t))
        (fun p => PowerSeries.coeff p h) a b N := by
  have hf : ∀ p : ℕ, N ≤ p →
      mode w (a - p) (mode w (b + p) ((highestWeightAction w).wordValue t)) = 0 :=
    fun p hp => (htail p hp).1
  have hr : ∀ p : ℕ, N ≤ p →
      mode w (b - p) (mode w (a + p) ((highestWeightAction w).wordValue t)) = 0 :=
    fun p hp => (htail p hp).2
  rw [quadraticConvolution_eq_sum_of_tail w h _ a b N hf,
    quadraticConvolution_eq_sum_of_tail w h _ b a N hr]
  simp only [skewSum, smul_sub, Finset.sum_sub_distrib]
  rfl

end KanadeRussell.Tsuchioka.Fock
