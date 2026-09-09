import KanadeRussell.Source.Reflected
import KanadeRussell.Source.ReflectedMinus
import KanadeRussell.Source.AdditionAlgebra
set_option backward.isDefEq.respectTransparency false

/-! The first source addition identity, paper `eq:app-addition-0`. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell.Source
open Infra

noncomputable def shift (k : ℕ) : PowerSeries QSeries →+* PowerSeries QSeries := rescale (q ^ k)

@[simp] theorem shift_zero (f : PowerSeries QSeries) : shift 0 f = f := by simp [shift]

theorem shift_add (i j : ℕ) (f : PowerSeries QSeries) : shift i (shift j f) = shift (i + j) f := by
  simp only [shift, rescale_rescale, ← pow_add, Nat.add_comm]

@[simp] theorem shift_C (k : ℕ) (c : QSeries) : shift k (PowerSeries.C c) = PowerSeries.C c := by
  apply PowerSeries.ext
  intro n
  simp only [shift, coeff_rescale, coeff_C]
  split_ifs with h
  · subst n; simp
  · simp

local notation "Q" => (PowerSeries.C q : PowerSeries QSeries)
local notation "aS" => sourceSeries 0 0
local notation "bS" => sourceSeries 1 3

@[simp] theorem shift_X (k : ℕ) : shift k (X : PowerSeries QSeries) = Q ^ k * X := by
  simp [shift, map_pow]

private theorem a_shift (k : ℕ) :
    shift (k + 1) aS = shift k aS - Q ^ (k + 1) * X * shift (k + 1) bS := by
  have ha : aS - shift 1 aS = Q * X * shift 1 bS := by simpa [shift] using a_sub_rescale
  have h := congrArg (shift k) ha
  simp only [map_sub, map_mul, shift_add, shift_C, shift_X] at h
  linear_combination -h

private theorem b_shift (k : ℕ) :
    shift (k + 2) bS = Q ^ k * X * shift k bS + shift (k + 1) bS - Q ^ k * X * shift (k + 1) aS := by
  have hb : shift 2 bS = X * bS + shift 1 bS - X * shift 1 aS := by simpa [shift] using b_rescale_two
  have h := congrArg (shift k) hb
  simpa only [map_sub, map_add, map_mul, shift_add, shift_X] using h

private theorem p_shift (k : ℕ) :
    shift k p = (1 - Q ^ (k + 1) * X) * shift (k + 1) p +
      Q ^ (k + 1) * X * (1 + Q + Q ^ (2 * k + 2) * X ^ 2) * shift (k + 2) p +
      Q ^ (2 * k + 4) * X ^ 2 * shift (k + 3) p := by
  have hp : p = (1 - Q * X) * shift 1 p + Q * X * (1 + Q + Q ^ 2 * X ^ 2) * shift 2 p +
      Q ^ 4 * X ^ 2 * shift 3 p := by simpa [shift, map_pow] using p_recurrence
  have h := congrArg (shift k) hp
  simp only [map_add, map_sub, map_mul, map_pow, map_one, shift_add, shift_C, shift_X] at h
  linear_combination h

noncomputable def additionCandidate : PowerSeries QSeries :=
  aS * (p + Q * X * shift 1 p) + Q * X ^ 2 * bS * shift 1 p

private theorem candidate_shift (k : ℕ) : shift k additionCandidate =
    shift k aS * (shift k p + Q ^ (k + 1) * X * shift (k + 1) p) +
      Q ^ (2 * k + 1) * X ^ 2 * shift k bS * shift (k + 1) p := by
  simp only [additionCandidate, map_add, map_mul, map_pow, shift_add, shift_C, shift_X]
  ring

/-- The polynomial certificate instantiated at the actual source series. -/
theorem scalarEquation_additionCandidate : scalarEquation q additionCandidate = 0 := by
  have h := addition_polynomial Q X (shift 0 aS) (shift 1 aS) (shift 2 aS) (shift 3 aS)
    (shift 0 bS) (shift 1 bS) (shift 2 bS) (shift 3 bS)
    (shift 0 p) (shift 1 p) (shift 2 p) (shift 3 p) (shift 4 p)
    (by simpa using a_shift 0) (by simpa using a_shift 1) (by simpa using a_shift 2)
    (by simpa using b_shift 0) (by simpa using b_shift 1)
    (by simpa using p_shift 0) (by simpa using p_shift 1)
  have he : scalarEquation q additionCandidate =
      Q * shift 0 additionCandidate - (1 + Q + Q ^ 2 * X ^ 2) * shift 1 additionCandidate +
      (1 - Q ^ 2 * X) * shift 2 additionCandidate + Q ^ 2 * X * shift 3 additionCandidate := by
    simp [scalarEquation, shift, map_pow]
  rw [he, candidate_shift 0, candidate_shift 1, candidate_shift 2, candidate_shift 3]
  simpa only [Nat.reduceAdd, Nat.reduceMul, pow_one] using h

theorem additionCandidate_eq : additionCandidate =
    aS * f₀ + Q * X ^ 2 * bS * rescale q p := by
  rw [f₀_eq_p_add]
  simp only [additionCandidate, shift, pow_one]

private theorem candidate_coeff_zero : coeff 0 additionCandidate = coeff 0 aS := by
  rw [additionCandidate_eq]
  simp [f₀]

private theorem candidate_coeff_one : coeff 1 additionCandidate =
    coeff 1 aS + q * bInv (q; q)_1 * coeff 0 aS := by
  rw [additionCandidate_eq, map_add]
  have hz : coeff 1 (Q * X ^ 2 * bS * rescale q p) = 0 := by
    simp only [pow_two, mul_assoc, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, mul_zero]
  rw [hz, add_zero, coeff_one_mul, coeff_one_f₀]
  simp only [f₀, constantCoeff_diagonalSeries, mul_one, ← coeff_zero_eq_constantCoeff]

/-- Paper `eq:app-addition-0`, proved by the scalar equation and its initial coefficients. -/
theorem addition_zero : reflectedSeries = aS * f₀ + Q * X ^ 2 * bS * rescale q p := by
  have hh : scalarEquation q (reflectedSeries - additionCandidate) = 0 := by
    have h1 := scalarEquation_reflected
    have h2 := scalarEquation_additionCandidate
    simp only [scalarEquation, map_sub] at *
    linear_combination h1 - h2
  have hpow : ∀ n : ℕ, 0 < n → q ^ n ≠ 1 := by
    intro n hn h
    have hc := congrArg (constantCoeff (R := ℤ)) h
    simp [q, hn.ne'] at hc
  have hz := scalarEquation_eq_zero_of_initial q (by exact X_ne_zero) hpow
    (reflectedSeries - additionCandidate) hh
    (by rw [map_sub, reflected_coeff_zero, candidate_coeff_zero, sub_self])
    (by rw [map_sub, reflected_coeff_one, candidate_coeff_one, sub_self])
  exact (sub_eq_zero.mp hz).trans additionCandidate_eq

/-- Paper `eq:app-addition-plus`, obtained from the first addition identity and F-contiguity. -/
theorem addition_plus : shift 1 reflectedSeries =
    aS * shift 1 f₀ - Q * X * shift 1 bS * shift 1 p := by
  have hz : reflectedSeries = aS * f₀ + Q * X ^ 2 * bS * shift 1 p := by
    simpa [shift] using addition_zero
  have h := congrArg (shift 1) hz
  simp only [map_add, map_mul, map_pow, shift_C, shift_X, shift_add] at h
  have hf₀ : f₀ = p + Q * X * shift 1 p := by simpa [shift] using f₀_eq_p_add
  have hf := congrArg (shift 1) hf₀
  simp only [map_add, map_mul, shift_C, shift_X, shift_add] at hf
  have ha : shift 1 aS = aS - Q * X * shift 1 bS := by simpa using a_shift 0
  rw [ha, hf] at h
  rw [hf]
  linear_combination h

@[simp] theorem sumCoeff_shift_reflected : sumCoeff (shift 1 reflectedSeries) = Wval := by
  simp only [shift, pow_one, reflectedSeries]
  rw [weightedSeries_rescale q Prod.fst summable_reflectedTerm,
    sumCoeff_weightedSeries Prod.fst (summable_series_mul summable_reflectedTerm _)]
  rfl

/-- First identity of paper `eq:app-quadratic-bridge`. -/
theorem quadratic_bridge_U : Uval = A ^ 2 + q * B * C := by
  have ha := sourceSeries_summableCoeff 0 0
  have hb := sourceSeries_summableCoeff 1 3
  have hf : SummableCoeff f₀ := diagonalSeries_summableCoeff 0 0
  have hp : SummableCoeff p := diagonalSeries_summableCoeff 1 0
  have hq := SummableCoeff.C q
  have hx := SummableCoeff.X
  have he := congrArg sumCoeff addition_zero
  rw [sumCoeff_reflectedSeries, sumCoeff_add (ha.mul hf) (((hq.mul (hx.pow 2)).mul hb).mul (hp.rescale q)),
    sumCoeff_mul ha hf,
    sumCoeff_mul ((hq.mul (hx.pow 2)).mul hb) (hp.rescale q),
    sumCoeff_mul (hq.mul (hx.pow 2)) hb, sumCoeff_mul hq (hx.pow 2),
    sumCoeff_pow hx 2, sumCoeff_C, sumCoeff_X,
    sumCoeff_a, sumCoeff_b, sumCoeff_f₀, sumCoeff_rescale_p] at he
  simpa only [one_pow, mul_one, pow_two] using he

/-- Third identity of paper `eq:app-quadratic-bridge`. -/
theorem quadratic_bridge_W : Wval = A * B - q * C ^ 2 := by
  have ha := sourceSeries_summableCoeff 0 0
  have hb := sourceSeries_summableCoeff 1 3
  have hf : SummableCoeff f₀ := diagonalSeries_summableCoeff 0 0
  have hp : SummableCoeff p := diagonalSeries_summableCoeff 1 0
  have hq := SummableCoeff.C q
  have hx := SummableCoeff.X
  have hf1 : SummableCoeff (shift 1 f₀) := by simpa [shift] using hf.rescale q
  have hb1 : SummableCoeff (shift 1 bS) := by simpa [shift] using hb.rescale q
  have hp1 : SummableCoeff (shift 1 p) := by simpa [shift] using hp.rescale q
  have he := congrArg sumCoeff addition_plus
  rw [sumCoeff_shift_reflected,
    sumCoeff_sub (ha.mul hf1) (((hq.mul hx).mul hb1).mul hp1),
    sumCoeff_mul ha hf1, sumCoeff_mul ((hq.mul hx).mul hb1) hp1,
    sumCoeff_mul (hq.mul hx) hb1, sumCoeff_mul hq hx, sumCoeff_C, sumCoeff_X] at he
  simp only [shift, pow_one, sumCoeff_a, sumCoeff_rescale_f₀,
    sumCoeff_rescale_b, sumCoeff_rescale_p, mul_one] at he
  convert he using 1
  ring

private theorem f₀_shift (k : ℕ) : shift k f₀ = shift k p + Q ^ (k + 1) * X * shift (k + 1) p := by
  have hf : f₀ = p + Q * X * shift 1 p := by simpa [shift] using f₀_eq_p_add
  have h := congrArg (shift k) hf
  simp only [map_add, map_mul, shift_C, shift_X, shift_add] at h
  linear_combination h

/-- Paper `eq:app-addition-minus`, including cancellation only of nonzero qx. -/
theorem addition_minus : minusSeries = X * bS * shift 1 f₀ + shift 1 bS * f₀ := by
  have hg₀ : reflectedSeries = aS * f₀ + Q * X ^ 2 * bS * shift 1 p := by
    simpa [shift] using addition_zero
  have hg₂ : shift 2 reflectedSeries = shift 1 aS * shift 2 f₀ - Q ^ 2 * X * shift 2 bS * shift 2 p := by
    have h := congrArg (shift 1) addition_plus
    simp only [map_sub, map_mul, shift_add, shift_C, shift_X] at h
    linear_combination h
  have hm : Q * X * minusSeries = reflectedSeries - shift 1 reflectedSeries - Q * X * shift 2 reflectedSeries := by
    simpa [shift] using reflected_minus_contiguity
  have hF₀ : f₀ = p + Q * X * shift 1 p := by simpa using f₀_shift 0
  have hF₁ : shift 1 f₀ = shift 1 p + Q ^ 2 * X * shift 2 p := by simpa using f₀_shift 1
  have hF₂ : shift 2 f₀ = shift 2 p + Q ^ 3 * X * shift 3 p := by simpa using f₀_shift 2
  have hp := addition_minus_polynomial Q X aS (shift 1 aS) bS (shift 1 bS) (shift 2 bS)
    p (shift 1 p) (shift 2 p) (shift 3 p)
    (by simpa using a_shift 0) (by simpa using b_shift 0) (by simpa using p_shift 0)
  have he : Q * X * minusSeries = Q * X * (X * bS * shift 1 f₀ + shift 1 bS * f₀) := by
    rw [addition_plus, hg₂, hg₀, hF₂, hF₁, hF₀] at hm
    rw [hF₁, hF₀]
    linear_combination hm + hp
  have hQ : Q ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := QSeries)) h
    exact (show (q : QSeries) ≠ 0 from X_ne_zero) (by simpa using hc)
  exact mul_left_cancel₀ (mul_ne_zero hQ X_ne_zero) he

/-- Second identity of paper `eq:app-quadratic-bridge`. -/
theorem quadratic_bridge_V : Vval = B ^ 2 + A * C := by
  have hb := sourceSeries_summableCoeff 1 3
  have hf : SummableCoeff f₀ := diagonalSeries_summableCoeff 0 0
  have hx := SummableCoeff.X
  have hf1 : SummableCoeff (shift 1 f₀) := by simpa [shift] using hf.rescale q
  have hb1 : SummableCoeff (shift 1 bS) := by simpa [shift] using hb.rescale q
  have he := congrArg sumCoeff addition_minus
  rw [sumCoeff_minusSeries,
    sumCoeff_add ((hx.mul hb).mul hf1) (hb1.mul hf),
    sumCoeff_mul (hx.mul hb) hf1, sumCoeff_mul hx hb, sumCoeff_mul hb1 hf,
    sumCoeff_X, sumCoeff_b, sumCoeff_f₀] at he
  simp only [shift, pow_one, sumCoeff_rescale_b, sumCoeff_rescale_f₀, one_mul] at he
  convert he using 1
  ring

/-- Milestone M1: all three identities of paper `eq:app-quadratic-bridge`. -/
theorem quadratic_bridge :
    Uval = A ^ 2 + q * B * C ∧ Vval = B ^ 2 + A * C ∧ Wval = A * B - q * C ^ 2 :=
  ⟨quadratic_bridge_U, quadratic_bridge_V, quadratic_bridge_W⟩

end KanadeRussell.Source
