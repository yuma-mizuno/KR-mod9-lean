import Mathlib
set_option backward.isDefEq.respectTransparency false

/-! Coefficientwise rigidity, paper `lem:positive-norm-rigidity`. -/

open PowerSeries

namespace KanadeRussell.Rigidity

noncomputable def norm (q X Y Z : PowerSeries ℤ) : PowerSeries ℤ :=
  X ^ 3 + q * Y ^ 3 - q ^ 2 * Z ^ 3 + 3 * q * X * Y * Z

/-- Paper `eq:positive-norm-factorization`. -/
theorem norm_sub_factorization (q X Y Z x y z : PowerSeries ℤ) :
    norm q X Y Z - norm q x y z =
      (X - x) * (X ^ 2 + X * x + x ^ 2 + 3 * q * Y * Z) +
      (q * (Y - y)) * (Y ^ 2 + Y * y + y ^ 2 + 3 * x * Z) +
      (q * (Z - z)) * (3 * x * y - q * (Z ^ 2 + Z * z + z ^ 2)) := by
  unfold norm
  ring

/-- At the first potentially nonzero coefficient, multiplication only sees the constant. -/
theorem coeff_mul_of_lower_zero (d p : PowerSeries ℤ) (n : ℕ)
    (h : ∀ k < n, coeff k d = 0) :
    coeff n (d * p) = coeff n d * constantCoeff p := by
  rw [coeff_mul]
  rw [Finset.sum_eq_single (n, 0)]
  · simp
  · intro ij hij hne
    have hs := Finset.mem_antidiagonal.mp hij
    have hi : ij.1 < n := by
      by_contra hlt
      apply hne
      apply Prod.ext <;> simp only <;> omega
    simp [h _ hi]
  · simp

/-- Three nonnegative series cannot cancel after multiplication by series with positive
constant coefficients. No positivity of the other multiplier coefficients is assumed. -/
theorem positive_combination_eq_zero
    (d e f p r s : PowerSeries ℤ)
    (hd : ∀ n, 0 ≤ coeff n d) (he : ∀ n, 0 ≤ coeff n e)
    (hf : ∀ n, 0 ≤ coeff n f)
    (hp : 0 < constantCoeff p) (hr : 0 < constantCoeff r)
    (hs : 0 < constantCoeff s) (hz : d * p + e * r + f * s = 0) :
    d = 0 ∧ e = 0 ∧ f = 0 := by
  have hall : ∀ n, coeff n d = 0 ∧ coeff n e = 0 ∧ coeff n f = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hc := congrArg (coeff n) hz
      simp only [map_add, map_zero] at hc
      rw [coeff_mul_of_lower_zero d p n (fun k hk => (ih k hk).1),
        coeff_mul_of_lower_zero e r n (fun k hk => (ih k hk).2.1),
        coeff_mul_of_lower_zero f s n (fun k hk => (ih k hk).2.2)] at hc
      have hdp := mul_nonneg (hd n) hp.le
      have her := mul_nonneg (he n) hr.le
      have hfs := mul_nonneg (hf n) hs.le
      constructor
      · nlinarith [hd n]
      constructor
      · nlinarith [he n]
      · nlinarith [hf n]
  exact ⟨PowerSeries.ext fun n => by simpa using (hall n).1,
    PowerSeries.ext fun n => by simpa using (hall n).2.1,
    PowerSeries.ext fun n => by simpa using (hall n).2.2⟩

/-- Paper `lem:positive-norm-rigidity`, over the target coefficient ring `ℤ`. -/
theorem rigidity (A B C a b c : PowerSeries ℤ)
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (hC : constantCoeff C = 1) (ha : constantCoeff a = 1)
    (hb : constantCoeff b = 1) (_hc : constantCoeff c = 1)
    (hAa : ∀ n, coeff n a ≤ coeff n A)
    (hBb : ∀ n, coeff n b ≤ coeff n B)
    (hCc : ∀ n, coeff n c ≤ coeff n C)
    (hn : norm X A B C = norm X a b c) : A = a ∧ B = b ∧ C = c := by
  have hshift (d : PowerSeries ℤ) (hd : ∀ n, 0 ≤ coeff n d) :
      ∀ n, 0 ≤ coeff n (X * d) := by
    intro n
    cases n with
    | zero => simp
    | succ n => simpa using hd n
  have h := positive_combination_eq_zero
    (A - a) (X * (B - b)) (X * (C - c))
    (A ^ 2 + A * a + a ^ 2 + 3 * X * B * C)
    (B ^ 2 + B * b + b ^ 2 + 3 * a * C)
    (3 * a * b - X * (C ^ 2 + C * c + c ^ 2))
    (fun n => by simpa using sub_nonneg.mpr (hAa n))
    (hshift _ (fun n => by simpa using sub_nonneg.mpr (hBb n)))
    (hshift _ (fun n => by simpa using sub_nonneg.mpr (hCc n)))
    (by norm_num [hA, ha, map_ofNat]) (by norm_num [hB, hb, ha, hC, map_ofNat]) (by norm_num [ha, hb, map_ofNat])
    (by rw [← norm_sub_factorization, hn, sub_self])
  refine ⟨sub_eq_zero.mp h.1, ?_, ?_⟩
  · exact sub_eq_zero.mp (PowerSeries.X_mul_injective (by simpa using h.2.1))
  · exact sub_eq_zero.mp (PowerSeries.X_mul_injective (by simpa using h.2.2))

end KanadeRussell.Rigidity
