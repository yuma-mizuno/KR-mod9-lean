import KanadeRussell.Source.ShortFunctional
import KanadeRussell.Source.UNormalized
set_option backward.isDefEq.respectTransparency false

/-! The unconditional source norm, assembled from the four theta functionals. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell
open Infra Source

/-- Paper `eq:norm-determinant-factorization`. -/
theorem source_determinant_factorization : Uval * Vval - Wval ^ 2 = C * cubicNorm A B C := by
  rw [quadratic_bridge_U, quadratic_bridge_V, quadratic_bridge_W]
  unfold cubicNorm
  ring

/-- The theta-functional determinant before using the quadratic bridge. -/
theorem source_determinant : E 1 * E 3 * (Uval * Vval - Wval ^ 2) = C * a := by
  have hd :
      (theta 1 * uOne - twist (theta 1) * twist uOne) *
        (twist (theta 3) * uFive + theta 3 * twist uFive) -
      (twist (theta 3) * uOne + theta 3 * twist uOne) *
        (theta 1 * uFive - twist (theta 1) * twist uFive) =
      -(twist uOne * uFive - uOne * twist uFive) *
        (theta 1 * theta 3 + twist (theta 1) * twist (theta 3)) := by ring
  rw [short_functional_one, long_functional_five, long_functional_one,
    short_functional_five, uCasoratian_specialized, theta_even_product] at hd
  have hz : 4 * q * baseChange (E 1 * E 3 * (Uval * Vval - Wval ^ 2) - C * a) = 0 := by
    simp only [map_sub, map_mul, map_pow]
    simp only [map_mul] at hd
    linear_combination -hd
  have h4 : (4 : QSeries) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := ℤ)) h
    norm_num [map_ofNat] at hc
  have hc := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero h4 X_ne_zero)
  have hi : E 1 * E 3 * (Uval * Vval - Wval ^ 2) - C * a = 0 :=
    baseChange_injective (by simpa only [map_zero] using hc)
  exact sub_eq_zero.mp hi

/-- The source half of `lem:equal-norms`, proved without any Pending input. -/
theorem sourceNorm : E 1 * E 3 * cubicNorm A B C = a := by
  have h := source_determinant
  rw [source_determinant_factorization] at h
  have hC : C ≠ 0 := by
    intro hz
    have hc := constantCoeff_eq_one.2.2.1
    rw [hz, map_zero] at hc
    omega
  apply mul_left_cancel₀ hC
  calc
    C * (E 1 * E 3 * cubicNorm A B C) = E 1 * E 3 * (C * cubicNorm A B C) := by ring
    _ = C * a := h

end KanadeRussell
