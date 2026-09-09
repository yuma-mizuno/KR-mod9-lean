import KanadeRussell.Source.Anchors
import KanadeRussell.Infra.Nonarch
import KanadeRussell.Infra.SumCoeff
set_option backward.isDefEq.respectTransparency false

/-! Coefficient-defined source series and their contiguities (design D6). -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell.Source

open Infra

noncomputable def sourceRow (a b m : ℕ) : PowerSeries ℤ := ∑' n, sourceTerm a b (m, n)

noncomputable def sourceSeries (a b : ℕ) : PowerSeries (PowerSeries ℤ) := mk (sourceRow a b)

theorem summable_sourceRow_terms (a b m : ℕ) : Summable (fun n => sourceTerm a b (m, n)) :=
  (summable_sourceTerm a b).prod_factor m

theorem sourceSeries_summableCoeff (a b : ℕ) : SummableCoeff (sourceSeries a b) := by
  simpa only [SummableCoeff, sourceSeries, coeff_mk, sourceRow] using (summable_sourceTerm a b).prod

theorem sumCoeff_sourceSeries (a b : ℕ) :
    sumCoeff (sourceSeries a b) = ∑' mn, sourceTerm a b mn := by
  simpa only [sumCoeff, sourceSeries, coeff_mk, sourceRow] using
    (summable_sourceTerm a b).tsum_prod.symm

@[simp] theorem sumCoeff_a : sumCoeff (sourceSeries 0 0) = A := sumCoeff_sourceSeries 0 0
@[simp] theorem sumCoeff_b : sumCoeff (sourceSeries 1 3) = B := sumCoeff_sourceSeries 1 3

/-- Termwise factorial cancellation behind the first F-contiguity. -/
theorem sourceTerm_first_contiguity (m n : ℕ) :
    (1 - q ^ (m + 1)) * sourceTerm 0 0 (m + 1, n) =
      q ^ (m + 1) * sourceTerm 1 3 (m, n) := by
  have hu := isUnit_qPochhammer_q 0 m
  have hv := isUnit_qPochhammer_q 0 (m + 1)
  simp only [Nat.zero_add, pow_one] at hu hv
  have hc := bInv_qFactorial_step q m hu hv
  have he : (m + 1) ^ 2 + 3 * (m + 1) * n + 3 * n ^ 2 =
      (m + 1) + (m ^ 2 + 3 * m * n + 3 * n ^ 2 + m + 3 * n) := by ring
  simp only [sourceTerm, zero_mul, one_mul, add_zero]
  rw [he, pow_add]
  linear_combination q ^ (m + 1) * q ^ (m ^ 2 + 3 * m * n + 3 * n ^ 2 + m + 3 * n) *
    bInv (q ^ 3; q ^ 3)_n * hc

/-- Paper `eq:app-F-contiguities` at y=1: a(x)-a(qx)=qx b(qx). -/
theorem a_sub_rescale :
    sourceSeries 0 0 - rescale q (sourceSeries 0 0) =
      PowerSeries.C q * X * rescale q (sourceSeries 1 3) := by
  apply PowerSeries.ext
  intro m
  cases m with
  | zero => simp only [map_sub, coeff_rescale, pow_zero, one_mul, sub_self,
      coeff_C_mul, coeff_zero_X_mul, mul_zero, mul_assoc]
  | succ m =>
    rw [mul_assoc]
    simp only [map_sub, coeff_rescale, coeff_C_mul, coeff_succ_X_mul,
      sourceSeries, coeff_mk]
    have h := ((summable_sourceRow_terms 0 0 (m + 1)).hasSum.mul_left (1 - q ^ (m + 1)))
    have h' := (summable_sourceRow_terms 1 3 m).hasSum.mul_left (q ^ (m + 1))
    have he := (h.congr_fun (fun n => (sourceTerm_first_contiguity m n).symm)).unique h'
    change (1 - q ^ (m + 1)) * sourceRow 0 0 (m + 1) =
      q ^ (m + 1) * sourceRow 1 3 m at he
    rw [pow_succ] at he
    linear_combination he

/-- Multiplying an x-coefficient by q^m increments the first source parameter. -/
theorem sourceTerm_rescale (a b m n : ℕ) :
    q ^ m * sourceTerm a b (m, n) = sourceTerm (a + 1) b (m, n) := by
  simp only [sourceTerm]
  rw [← mul_assoc, ← mul_assoc, ← pow_add]
  congr 2
  congr 1
  ring

theorem sourceSeries_rescale (a b : ℕ) :
    rescale q (sourceSeries a b) = sourceSeries (a + 1) b := by
  apply PowerSeries.ext
  intro m
  simp only [coeff_rescale, sourceSeries, coeff_mk, sourceRow]
  rw [← (summable_sourceRow_terms a b m).tsum_mul_left]
  exact tsum_congr (sourceTerm_rescale a b m)

@[simp] theorem sumCoeff_rescale_b : sumCoeff (rescale q (sourceSeries 1 3)) = C := by
  rw [sourceSeries_rescale, sumCoeff_sourceSeries]
  rfl

/-- The second source contiguity shifts the n-index and clears both factorials. -/
theorem sourceTerm_second_contiguity (m n : ℕ) :
    q ^ m * sourceTerm 0 0 (m, n + 1) - sourceTerm 1 3 (m, n + 1) =
      q ^ (m + 1) * (1 - q ^ (m + 1)) * sourceTerm 1 3 (m + 1, n) := by
  have hqm (k : ℕ) : IsUnit (q; q)_k := by simpa using isUnit_qPochhammer_q 0 k
  have hQn (k : ℕ) : IsUnit (q ^ 3; q ^ 3)_k := by simpa using isUnit_qPochhammer_q 2 k
  have hm := bInv_qFactorial_step q m (hqm m) (hqm (m + 1))
  have hn := bInv_qFactorial_step (q ^ 3) n (hQn n) (hQn (n + 1))
  simp only [sourceTerm, zero_mul, one_mul, add_zero]
  linear_combination
    q ^ (m ^ 2 + 3 * m * n + 3 * n ^ 2 + 4 * m + 6 * n + 3) * bInv (q; q)_m * hn -
    q ^ (m ^ 2 + 3 * m * n + 3 * n ^ 2 + 4 * m + 6 * n + 3) * bInv (q ^ 3; q ^ 3)_n * hm

/-- The n-index contiguity after summation, with its zero boundary term checked. -/
theorem sourceRow_second_contiguity (m : ℕ) :
    q ^ m * sourceRow 0 0 m - sourceRow 1 3 m =
      q ^ (m + 1) * (1 - q ^ (m + 1)) * sourceRow 1 3 (m + 1) := by
  have hd := ((summable_sourceRow_terms 0 0 m).hasSum.mul_left (q ^ m)).sub
    (summable_sourceRow_terms 1 3 m).hasSum
  have hr := ((summable_sourceRow_terms 1 3 (m + 1)).hasSum.mul_left
    (q ^ (m + 1) * (1 - q ^ (m + 1)))).congr_fun
      (fun n => sourceTerm_second_contiguity m n)
  have hz : q ^ m * sourceTerm 0 0 (m, 0) - sourceTerm 1 3 (m, 0) = 0 := by
    simp only [sourceTerm, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0),
      add_zero, one_mul, qPochhammer_zero, bInv_one, mul_one, pow_add]
    ring
  have hh := (hasSum_nat_add_iff (f := fun n => q ^ m * sourceTerm 0 0 (m, n) -
    sourceTerm 1 3 (m, n)) 1).mp hr
  simp only [Finset.sum_range_one, hz, add_zero] at hh
  exact hd.unique hh

/-- Paper `eq:app-L-system`, last row: b(q²x)=x b(x)+b(qx)-x a(qx). -/
theorem b_rescale_two :
    rescale (q ^ 2) (sourceSeries 1 3) =
      X * sourceSeries 1 3 + rescale q (sourceSeries 1 3) - X * rescale q (sourceSeries 0 0) := by
  apply PowerSeries.ext
  intro m
  cases m with
  | zero =>
    simp only [coeff_rescale, pow_zero, one_mul, map_sub, map_add,
      coeff_zero_X_mul, zero_add, sub_zero]
  | succ m =>
    simp only [coeff_rescale, map_sub, map_add, coeff_succ_X_mul, sourceSeries, coeff_mk]
    have h := sourceRow_second_contiguity m
    linear_combination h

end KanadeRussell.Source
