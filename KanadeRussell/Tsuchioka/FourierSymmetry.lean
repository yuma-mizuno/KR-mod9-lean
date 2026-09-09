import KanadeRussell.Tsuchioka.ScalarPhases

/-! Linear Fourier operations and the reciprocal-pair identities used by the source. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Scalar

open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

noncomputable def symmetricFourier (f : PowerSeries K) : ℤ → K :=
  positive f + reflect (positive f)

noncomputable def antisymmetricFourier (f : PowerSeries K) : ℤ → K :=
  positive f - reflect (positive f)

theorem symmetricFourier_add (f g : PowerSeries K) :
    symmetricFourier (f + g) = symmetricFourier f + symmetricFourier g := by
  funext n
  simp only [symmetricFourier, positive_add, reflect, Pi.add_apply]
  ring

theorem antisymmetricFourier_add (f g : PowerSeries K) :
    antisymmetricFourier (f + g) = antisymmetricFourier f + antisymmetricFourier g := by
  funext n
  simp only [antisymmetricFourier, positive_add, reflect, Pi.add_apply, Pi.sub_apply]
  ring

theorem antisymmetricFourier_sub (f g : PowerSeries K) :
    antisymmetricFourier (f - g) = antisymmetricFourier f - antisymmetricFourier g := by
  funext n
  simp only [antisymmetricFourier, positive_sub, reflect, Pi.sub_apply]
  ring

theorem symmetricFourier_C_mul (a : K) (f : PowerSeries K) :
    symmetricFourier (C a * f) = fun n => a * symmetricFourier f n := by
  funext n
  simp only [symmetricFourier, positive_C_mul, reflect, Pi.add_apply]
  ring

theorem antisymmetricFourier_C_mul (a : K) (f : PowerSeries K) :
    antisymmetricFourier (C a * f) = fun n => a * antisymmetricFourier f n := by
  funext n
  simp only [antisymmetricFourier, positive_C_mul, reflect, Pi.sub_apply]
  ring

theorem positive_one (n : ℤ) :
    positive (1 : PowerSeries K) n = if n = 0 then 1 else 0 := by
  by_cases hn : 0 ≤ n
  · by_cases hz : n = 0
    · subst n; simp [positive]
    · simp [positive, hn, hz, show n.toNat ≠ 0 by omega]
  · simp [positive, hn, show n ≠ 0 by omega]

@[simp] theorem antisymmetricFourier_one :
    antisymmetricFourier (1 : PowerSeries K) = 0 := by
  funext n
  simp [antisymmetricFourier, reflect, positive_one]

/-- A reciprocal pair, centered so its constant coefficient is correct. -/
theorem symmetric_geometric_pair (c : K) :
    symmetricFourier (geometric c + geometric c⁻¹ - 1) =
      fun n => delta c n + delta c⁻¹ n := by
  funext n
  change (positive _ n : K) + positive _ (-n) = _
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast]
    by_cases hn : n = 0
    · subst n; norm_num [positive, delta]
    · rw [positive_nat, positive_neg_nat _ n (by omega)]
      simp [delta, hn]
  | negSucc n =>
    change (positive _ (-((n + 1 : ℕ) : ℤ)) : K) +
      positive _ (-(-((n + 1 : ℕ) : ℤ))) =
        delta c (-((n + 1 : ℕ) : ℤ)) + delta c⁻¹ (-((n + 1 : ℕ) : ℤ))
    rw [positive_neg_nat _ _ (by omega), neg_neg, positive_nat]
    simp only [map_sub, map_add, coeff_geometric, coeff_one, Nat.succ_ne_zero,
      if_false, sub_zero, zero_add, delta, zpow_neg, zpow_natCast, inv_pow, inv_inv]
    ring

theorem antisymmetric_geometric_pair (c : K) :
    antisymmetricFourier (geometric c - geometric c⁻¹) =
      fun n => delta c n - delta c⁻¹ n := by
  funext n
  change (positive _ n : K) - positive _ (-n) = _
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast]
    by_cases hn : n = 0
    · subst n; norm_num [positive, delta]
    · rw [positive_nat, positive_neg_nat _ n (by omega)]
      simp [delta, hn]
  | negSucc n =>
    change (positive _ (-((n + 1 : ℕ) : ℤ)) : K) -
      positive _ (-(-((n + 1 : ℕ) : ℤ))) =
        delta c (-((n + 1 : ℕ) : ℤ)) - delta c⁻¹ (-((n + 1 : ℕ) : ℤ))
    rw [positive_neg_nat _ _ (by omega), neg_neg, positive_nat]
    simp only [map_sub, coeff_geometric, zero_sub, delta, zpow_neg,
      zpow_natCast, inv_pow, inv_inv]
    ring

theorem symmetric_geometric_neg_one :
    symmetricFourier (2 * geometric (-1 : K) - 1) = fun n => 2 * delta (-1) n := by
  simpa only [show (-1 : K)⁻¹ = -1 by simp, two_mul] using
    symmetric_geometric_pair (-1 : K)

def oppositePhase (p : Fin 12) : Fin 12 :=
  ⟨(12 - p.val) % 12, Nat.mod_lt _ (by decide)⟩

theorem phasePolynomial_opposite (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (p : Fin 12) :
    phasePolynomial w (oppositePhase p) = (phasePolynomial w p)⁻¹ := by
  rw [phasePolynomial_inverse w hw, ← negative_phase w hw (oppositePhase p), ← zpow_natCast]
  apply Coefficients.zpow_eq_of_mod w hw
  simp only [oppositePhase, Int.natCast_mod, Int.natCast_sub (by omega : p.val ≤ 12),
    Nat.cast_ofNat]
  omega

end KanadeRussell.Tsuchioka.Scalar
