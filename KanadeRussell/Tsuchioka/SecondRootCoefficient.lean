import KanadeRussell.Tsuchioka.G2Anticommutator
import KanadeRussell.Tsuchioka.Phases

/-! Nonvanishing of the second-root coefficient in the two G2 specializations
used in Section 4.1: equal indices and indices differing by one. -/

namespace KanadeRussell.Tsuchioka.Coefficients

variable {K : Type*} [Field K] [CharZero K]

theorem tCoeff_ne_zero (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    tCoeff w ≠ 0 := by
  convert t_ne_zero w hw using 1
  unfold tCoeff
  ring

theorem second_phase_adjacent_ne_zero (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    w ^ 4 + w ^ 9 ≠ 0 := by
  have h : (w ^ 4 + w ^ 9) * (w ^ 3 - w - 1) = 1 := by
    linear_combination (w ^ 8 - w ^ 5 - w ^ 4 - w ^ 2 - 1) * hw
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

theorem second_phase_equal (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (a : ℤ) :
    w ^ (4 * a + 9 * a) + w ^ (9 * a + 4 * a) = 2 * w ^ a := by
  rw [(ordering_phase_factor w hw a a).1, (ordering_phase_factor w hw a a).2]
  simp only [sub_self, mul_zero, zpow_zero, mul_one]
  ring

theorem second_phase_adjacent (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (b : ℤ) :
    w ^ (4 * (b + 1) + 9 * b) + w ^ (9 * (b + 1) + 4 * b) =
      w ^ b * (w ^ 4 + w ^ 9) := by
  rw [(ordering_phase_factor w hw (b + 1) b).1,
    (ordering_phase_factor w hw (b + 1) b).2]
  norm_num only [add_sub_cancel_left, mul_one, zpow_ofNat]
  ring

theorem second_coefficient_ne_zero (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (hab : a = b ∨ a = b + 1) :
    tCoeff w * (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) / 12 ≠ 0 := by
  apply div_ne_zero ?_ (by norm_num)
  apply mul_ne_zero (tCoeff_ne_zero w hw)
  rcases hab with rfl | rfl
  · rw [second_phase_equal w hw]
    exact mul_ne_zero (by norm_num) (zpow_ne_zero _ (root_ne_zero w hw))
  · rw [second_phase_adjacent w hw]
    exact mul_ne_zero (zpow_ne_zero _ (root_ne_zero w hw))
      (second_phase_adjacent_ne_zero w hw)

theorem second_indices (i : ℤ) :
    ∃ a b : ℤ, a + b = i ∧ (a = b ∨ a = b + 1) := by
  refine ⟨i - i / 2, i / 2, by omega, ?_⟩
  omega

end KanadeRussell.Tsuchioka.Coefficients
