import Mathlib
import RogersRamanujan
set_option backward.isDefEq.respectTransparency false

/-! The injective substitution `q = t⁴` of design D3. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity

namespace KanadeRussell.Infra

noncomputable def baseChange : PowerSeries ℤ →+* PowerSeries ℤ := intEval (X ^ 4)

theorem continuous_expand (d : ℕ) (hd : d ≠ 0) :
    Continuous (expand d hd (R := ℤ)) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, tendsto_iff_coeff_tendsto]
  intro n
  simp only [coeff_expand]
  split_ifs
  · exact (continuous_coeff ℤ (n / d)).continuousAt
  · exact tendsto_const_nhds

theorem expand_eq_intEval (d : ℕ) (hd : d ≠ 0) :
    (expand d hd (R := ℤ)).toRingHom = intEval (X ^ d) := by
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, expand_X] using
    eq_intEval (expand d hd (R := ℤ)).toRingHom (continuous_expand d hd)

theorem baseChange_eq_expand (f : PowerSeries ℤ) : baseChange f = expand 4 (by decide) f := by
  rw [baseChange, ← expand_eq_intEval 4 (by decide)]
  rfl

@[simp] theorem coeff_baseChange (f : PowerSeries ℤ) (n : ℕ) :
    coeff (4 * n) (baseChange f) = coeff n f := by
  rw [baseChange_eq_expand, coeff_expand_mul]

theorem baseChange_injective : Function.Injective baseChange := by
  intro f g h
  apply PowerSeries.ext
  intro n
  simpa only [coeff_baseChange] using congrArg (coeff (4 * n)) h

@[simp] theorem baseChange_X : baseChange (X : PowerSeries ℤ) = X ^ 4 := by
  simp [baseChange]

theorem baseChange_continuous : Continuous baseChange := by
  unfold baseChange
  fun_prop

end KanadeRussell.Infra
