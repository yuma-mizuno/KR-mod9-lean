import KanadeRussell.Tsuchioka.MixedPole

/-! The sixth-root identities that cycle the mixed tensor positions. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

theorem hexagonal_cube (x : K) (hx : x ^ 2 - x + 1 = 0) : x ^ 3 = -1 := by
  linear_combination (x + 1) * hx

theorem hexagonal_cycle (x : K) (hx : x ^ 2 - x + 1 = 0)
    (a b c : K) (hab : a + b = -c) :
    x ^ 2 * (a * x + b) = b * x + c := by
  have hc := hexagonal_cube x hx
  linear_combination a * hc + b * hx - hab

theorem mixed_phase_hexagonal (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (n : Mode) :
    (w ^ (p * n.val)) ^ 2 - w ^ (p * n.val) + 1 = 0 := by
  rcases hp with rfl | rfl
  · have he : w ^ ((2 : ℤ) * n.val) = (w ^ n.val) ^ 2 := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    rw [he]
    simpa only [← pow_mul, Nat.mul_assoc, show (2 : ℕ) * 2 = 4 by decide] using mode_cyclotomic w hw n
  · have he : w ^ ((-2 : ℤ) * n.val) = (w ^ (-(n.val : ℤ))) ^ 2 := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    rw [he]
    simpa only [← pow_mul] using mode_inverse_cyclotomic w hw n

theorem mixed_phase_cycle (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (n : Mode) (i s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    w ^ ((2 * p) * n.val) *
        (tensorExponent (K := K) i s * w ^ (p * n.val) + tensorExponent i t) =
      tensorExponent i t * w ^ (p * n.val) + tensorExponent i u := by
  have he : w ^ ((2 * p) * n.val) = (w ^ (p * n.val)) ^ 2 := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [he]
  exact hexagonal_cycle _ (mixed_phase_hexagonal w hw p hp n) _ _ _
    (tensorExponent_complement i s t u hst hsu htu)

theorem mixed_phase_cycle_neg (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (n : Mode) (i s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    w ^ (-(2 * p) * n.val) *
        (tensorExponent (K := K) i s * w ^ (-p * n.val) + tensorExponent i t) =
      tensorExponent i t * w ^ (-p * n.val) + tensorExponent i u := by
  have hp' : -p = 2 ∨ -p = -2 := by omega
  have h := mixed_phase_cycle w hw (-p) hp' n i s t u hst hsu htu
  simpa only [mul_neg] using h

end KanadeRussell.Tsuchioka.Fock
