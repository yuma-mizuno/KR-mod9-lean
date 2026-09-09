import Mathlib
set_option backward.isDefEq.respectTransparency false

/-! Uniqueness of the two q-difference equations (design D10). -/

open PowerSeries

namespace KanadeRussell.Infra

section General
variable {R : Type*} [CommRing R] [IsDomain R]

/-- A finite q-difference operator with arbitrary series multipliers. -/
noncomputable def difference {m : ℕ} (p : Fin m → PowerSeries R) (r : Fin m → R)
    (f : PowerSeries R) : PowerSeries R := ∑ i, p i * rescale (r i) f

private theorem coeff_mul_rescale_of_lower_zero (p f : PowerSeries R) (r : R) (n : ℕ)
    (h : ∀ k < n, coeff k f = 0) :
    coeff n (p * rescale r f) = constantCoeff p * r ^ n * coeff n f := by
  rw [coeff_mul, Finset.sum_eq_single (0, n)]
  · simp [coeff_rescale, mul_assoc]
  · intro ij hij hne
    have hs := Finset.mem_antidiagonal.mp hij
    have hi : ij.2 < n := by
      by_contra hlt
      apply hne
      apply Prod.ext <;> simp only <;> omega
    simp [coeff_rescale, h _ hi]
  · simp

/-- A nonzero diagonal coefficient gives coefficientwise uniqueness of a q-difference
solution from its initial segment; the multipliers may be arbitrary power series. -/
theorem difference_eq_zero_of_initial {m k : ℕ}
    (p : Fin m → PowerSeries R) (r : Fin m → R)
    (hdiag : ∀ n, k ≤ n → (∑ i, constantCoeff (p i) * r i ^ n) ≠ 0)
    (f : PowerSeries R) (hf : difference p r f = 0)
    (hinit : ∀ n < k, coeff n f = 0) : f = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < k
    · exact hinit n hn
    have hc := congrArg (coeff n) hf
    simp only [difference, map_sum, map_zero] at hc
    simp_rw [coeff_mul_rescale_of_lower_zero _ f _ n ih] at hc
    rw [← Finset.sum_mul] at hc
    exact (mul_eq_zero.mp hc).resolve_left (hdiag n (by omega))

/-- Paper `eq:app-scalar-equation`, in denominator-free form. -/
noncomputable def scalarEquation (q : R) (f : PowerSeries R) : PowerSeries R :=
  C q * f - (C (1 + q) + C (q ^ 2) * X ^ 2) * rescale q f +
    (1 - C (q ^ 2) * X) * rescale (q ^ 2) f + C (q ^ 2) * X * rescale (q ^ 3) f

omit [IsDomain R] in
private theorem scalar_diagonal (q : R) (n : ℕ) :
    q - (1 + q) * q ^ (n + 2) + (q ^ 2) ^ (n + 2) =
      q * (1 - q ^ (n + 2)) * (1 - q ^ (n + 1)) := by
  simp only [pow_succ]
  ring

theorem scalarEquation_eq_zero_of_initial (q : R) (hq : q ≠ 0)
    (hpow : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
    (f : PowerSeries R) (hf : scalarEquation q f = 0)
    (h0 : coeff 0 f = 0) (h1 : coeff 1 f = 0) : f = 0 := by
  let p : Fin 4 → PowerSeries R :=
    ![C q, -(C (1 + q) + C (q ^ 2) * X ^ 2), 1 - C (q ^ 2) * X, C (q ^ 2) * X]
  let r : Fin 4 → R := ![1, q, q ^ 2, q ^ 3]
  apply difference_eq_zero_of_initial (k := 2) p r _ f _ _
  · intro n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [p, r, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    simp only [map_neg, map_add, map_sub, map_mul, map_pow, constantCoeff_C,
      constantCoeff_X, map_one, zero_pow (by decide : 2 ≠ 0), mul_zero,
      zero_mul, add_zero, sub_zero, one_mul, one_pow, mul_one, neg_mul]
    rw [show 2 + j = j + 2 by omega, ← add_assoc, ← sub_eq_add_neg, scalar_diagonal]
    exact mul_ne_zero (mul_ne_zero hq (sub_ne_zero.mpr (hpow _ (by omega)).symm))
      (sub_ne_zero.mpr (hpow _ (by omega)).symm)
  · convert hf using 1
    simp [difference, scalarEquation, p, r, Fin.sum_univ_succ]
    ring
  · intro n hn
    interval_cases n <;> assumption

/-- Paper `eq:app-exterior-equation` for `W = x H`, after cancellation of `q x`. -/
noncomputable def exteriorEquation (q : R) (f : PowerSeries R) : PowerSeries R :=
  f - (1 - C (q ^ 2) * X) * rescale q f -
    C (q ^ 2) * X * (C (1 + q) + C (q ^ 4) * X ^ 2) * rescale (q ^ 2) f -
    C (q ^ 6) * X ^ 2 * rescale (q ^ 3) f

theorem exteriorEquation_eq_zero_of_initial (q : R)
    (hpow : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
    (f : PowerSeries R) (hf : exteriorEquation q f = 0)
    (h0 : coeff 0 f = 0) : f = 0 := by
  let p : Fin 4 → PowerSeries R :=
    ![1, -(1 - C (q ^ 2) * X),
      -(C (q ^ 2) * X * (C (1 + q) + C (q ^ 4) * X ^ 2)), -(C (q ^ 6) * X ^ 2)]
  let r : Fin 4 → R := ![1, q, q ^ 2, q ^ 3]
  apply difference_eq_zero_of_initial (k := 1) p r _ f _ _
  · intro n hn
    simpa [p, r, Fin.sum_univ_succ, sub_eq_add_neg] using
      (sub_ne_zero.mpr (hpow n hn).symm : (1 : R) - q ^ n ≠ 0)
  · convert hf using 1
    simp [difference, exteriorEquation, p, r, Fin.sum_univ_succ]
    ring
  · intro n hn
    have : n = 0 := by omega
    simpa [this] using h0

end General
end KanadeRussell.Infra
