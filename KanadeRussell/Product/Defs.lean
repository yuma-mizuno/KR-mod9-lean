import KanadeRussell.Source.Anchors
set_option backward.isDefEq.respectTransparency false

/-! Exact product-side definitions and arithmetic-progression splitting. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Product

noncomputable def J (r : ℕ) : PowerSeries ℤ := E 9 * P9 r * P9 (9 - r)

theorem isUnit_E (d : ℕ) (hd : 0 < d) : IsUnit (E d) :=
  isUnit_qPochhammerInf (by simp [q, hd.ne']) (by simp [q, hd.ne'])

theorem isUnit_J (r : ℕ) (hr : 0 < r) (hr9 : r < 9) : IsUnit (J r) :=
  ((isUnit_E 9 (by decide)).mul (isUnit_P9 r hr)).mul (isUnit_P9 (9 - r) (by omega))

theorem E_three_split : E 3 = P9 3 * P9 6 * E 9 := by
  rw [E, qPochhammerInf_eq_prod_range (by decide : 3 ≠ 0) (by simp [q])]
  norm_num only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, mul_one,
    one_mul, ← pow_mul, ← pow_add, Nat.reduceMul, Nat.reduceAdd]
  rfl

theorem E_one_split : E 1 =
    P9 1 * P9 2 * P9 3 * P9 4 * P9 5 * P9 6 * P9 7 * P9 8 * E 9 := by
  rw [E, pow_one, qPochhammerInf_eq_prod_range (by decide : 9 ≠ 0) (by simp [q])]
  norm_num only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, mul_one,
    one_mul, ← pow_succ', Nat.reduceAdd]
  rfl

/-- Product splitting behind the level-nine theta form. -/
theorem J_product : J 1 * J 2 * J 4 * E 3 = E 1 * (E 9) ^ 3 := by
  rw [E_one_split, E_three_split]
  norm_num only [J, Nat.reduceSub]
  ring

theorem K_one_J : K₁ * E 3 * J 1 = (E 9) ^ 2 := by
  have h := K₁_mul
  rw [E_three_split]
  norm_num only [J, Nat.reduceSub]
  linear_combination (E 9) ^ 2 * h

theorem K_two_J : K₂ * E 3 * J 2 = (E 9) ^ 2 := by
  have h := K₂_mul
  rw [E_three_split]
  norm_num only [J, Nat.reduceSub]
  linear_combination (E 9) ^ 2 * h

theorem K_three_J : K₃ * E 3 * J 4 = (E 9) ^ 2 := by
  have h := K₃_mul
  rw [E_three_split]
  norm_num only [J, Nat.reduceSub]
  linear_combination (E 9) ^ 2 * h

noncomputable def thetaNumerator : PowerSeries ℤ :=
  (J 2) ^ 3 * (J 4) ^ 3 + q * (J 1) ^ 3 * (J 4) ^ 3 -
    q ^ 2 * (J 1) ^ 3 * (J 2) ^ 3 + 3 * q * (J 1 * J 2 * J 4) ^ 2

end KanadeRussell.Product
