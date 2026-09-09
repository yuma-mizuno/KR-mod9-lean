import Mathlib
import RogersRamanujan
set_option backward.isDefEq.respectTransparency false

/-! Evaluation at `x = 1` on series with summable coefficients (design D7). -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity

namespace KanadeRussell.Infra

abbrev QSeries := PowerSeries ℤ

def SummableCoeff (f : PowerSeries QSeries) : Prop := Summable (fun n => coeff n f)

noncomputable def sumCoeff (f : PowerSeries QSeries) : QSeries := ∑' n, coeff n f

theorem SummableCoeff.add {f g : PowerSeries QSeries}
    (hf : SummableCoeff f) (hg : SummableCoeff g) : SummableCoeff (f + g) := by
  simpa [SummableCoeff] using Summable.add hf hg

theorem sumCoeff_add {f g : PowerSeries QSeries}
    (hf : SummableCoeff f) (hg : SummableCoeff g) :
    sumCoeff (f + g) = sumCoeff f + sumCoeff g := by
  simp only [sumCoeff, map_add]
  exact hf.tsum_add hg

theorem SummableCoeff.neg {f : PowerSeries QSeries}
    (hf : SummableCoeff f) : SummableCoeff (-f) := by
  simpa [SummableCoeff] using Summable.neg hf

theorem sumCoeff_neg (f : PowerSeries QSeries) : sumCoeff (-f) = -sumCoeff f := by
  simp only [sumCoeff, map_neg]
  exact tsum_neg

theorem SummableCoeff.mul {f g : PowerSeries QSeries}
    (hf : SummableCoeff f) (hg : SummableCoeff g) : SummableCoeff (f * g) := by
  have h := hf.hasSum.mul_antidiagonal hg.hasSum
  simpa [SummableCoeff, coeff_mul] using h.summable

theorem sumCoeff_mul {f g : PowerSeries QSeries}
    (hf : SummableCoeff f) (hg : SummableCoeff g) :
    sumCoeff (f * g) = sumCoeff f * sumCoeff g := by
  simpa only [sumCoeff, coeff_mul] using (hf.hasSum.mul_antidiagonal hg.hasSum).tsum_eq

theorem SummableCoeff.C (a : QSeries) : SummableCoeff (PowerSeries.C a) := by
  apply summable_of_hasFiniteSupport
  apply (Set.finite_singleton 0).subset
  intro n hn
  by_contra h
  have hn0 : n ≠ 0 := by simpa using h
  exact hn (by simp [coeff_C, hn0])

@[simp] theorem sumCoeff_C (a : QSeries) : sumCoeff (PowerSeries.C a) = a := by
  simp [sumCoeff, coeff_C]

/-- q-shifts preserve summable coefficients, including evaluation at x = 1. -/
theorem SummableCoeff.rescale (r : QSeries) {f : PowerSeries QSeries}
    (hf : SummableCoeff f) : SummableCoeff (PowerSeries.rescale r f) := by
  have hb : (fun n : ℕ => r ^ n).BoundedRange := PowerSeries.bounded _
  have hh := NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero (fun n => coeff n f) |>.mp hf
  apply (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero _).mpr
  simpa only [coeff_rescale] using hb.mul_tendsto_zero hh

@[simp] theorem sumCoeff_X : sumCoeff (X : PowerSeries QSeries) = 1 := by
  simp [sumCoeff, coeff_X]

theorem SummableCoeff.X : SummableCoeff (PowerSeries.X : PowerSeries QSeries) := by
  apply summable_of_hasFiniteSupport
  apply (Set.finite_singleton 1).subset
  intro n hn
  by_contra h
  have hn1 : n ≠ 1 := by simpa using h
  exact hn (by simp [coeff_X, hn1])

theorem SummableCoeff.sub {f g : PowerSeries QSeries}
    (hf : SummableCoeff f) (hg : SummableCoeff g) : SummableCoeff (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem sumCoeff_sub {f g : PowerSeries QSeries}
    (hf : SummableCoeff f) (hg : SummableCoeff g) : sumCoeff (f - g) = sumCoeff f - sumCoeff g := by
  simpa [sub_eq_add_neg, sumCoeff_neg] using sumCoeff_add hf hg.neg

theorem SummableCoeff.pow {f : PowerSeries QSeries} (hf : SummableCoeff f) (n : ℕ) :
    SummableCoeff (f ^ n) := by
  induction n with
  | zero => simpa using SummableCoeff.C (1 : QSeries)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem sumCoeff_pow {f : PowerSeries QSeries} (hf : SummableCoeff f) (n : ℕ) :
    sumCoeff (f ^ n) = sumCoeff f ^ n := by
  induction n with
  | zero => simpa using sumCoeff_C (1 : QSeries)
  | succ n ih => rw [pow_succ, sumCoeff_mul (hf.pow n) hf, ih, pow_succ]

end KanadeRussell.Infra
