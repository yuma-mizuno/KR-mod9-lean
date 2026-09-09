import Mathlib
set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Infra

/-- Integer triangular number, including negative arguments (Appendix E.1). -/
def triangular (z : ℤ) : ℕ := (z * (z + 1) / 2).toNat

theorem triangular_nonneg (z : ℤ) : 0 ≤ z * (z + 1) := by
  have : z ≤ -1 ∨ 0 ≤ z := by omega
  rcases this with h | h <;> nlinarith

theorem twice_triangular (z : ℤ) : 2 * (triangular z : ℤ) = z * (z + 1) := by
  unfold triangular
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg (triangular_nonneg z) (by decide))]
  have hd := (Int.even_mul_succ_self z).two_dvd
  exact Int.mul_ediv_cancel' hd

/-- Exact shift of the nonnegative exponents in the cleared Euler recurrence. -/
theorem triangular_step (n ν : ℕ) :
    triangular ((n : ℤ) - ν) + ν = triangular ((n : ℤ) - (ν + 1)) + n := by
  have h1 := twice_triangular ((n : ℤ) - ν)
  have h2 := twice_triangular ((n : ℤ) - (ν + 1))
  nlinarith

theorem triangular_succ (n ν : ℕ) :
    triangular (((n + 1 : ℕ) : ℤ) - (ν + 1)) = triangular ((n : ℤ) - ν) := by
  congr 1
  push_cast
  ring

/-- An explicit finite coefficient bound for the cleared Euler series. -/
theorem triangular_large (n ν k : ℕ) (hn : 2 * (ν + k + 1) < n) :
    k < triangular ((n : ℤ) - ν) := by
  have ht := twice_triangular ((n : ℤ) - ν)
  have hn' : (2 : ℤ) * (ν + k + 1) < n := by exact_mod_cast hn
  have hnν : (k : ℤ) + 1 ≤ (n : ℤ) - ν := by omega
  have hpos : (0 : ℤ) ≤ (n : ℤ) - ν := by omega
  have : (k : ℤ) < triangular ((n : ℤ) - ν) := by nlinarith
  exact_mod_cast this

/-- D8: the quadratic exponent of the reflected Nahm sum is nonnegative. -/
theorem three_mul_le_quadratic (m n : ℕ) : 3 * m * n ≤ m ^ 2 + 3 * n ^ 2 := by
  nlinarith [sq_nonneg ((2 : ℤ) * m - 3 * n)]

/-- Exponent matching for Euler's evaluation at a positive power of `q`. -/
theorem triangular_add (n k : ℕ) :
    triangular ((n : ℤ) + k) = n.choose 2 + (k + 1) * n + triangular k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := twice_triangular ((n : ℤ) + k)
    have h2 := twice_triangular (((n + 1 : ℕ) : ℤ) + k)
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast at h2
    have he : triangular (((n + 1 : ℕ) : ℤ) + k) =
        triangular ((n : ℤ) + k) + (n + k + 1) := by
      push_cast
      nlinarith
    rw [he, ih]
    ring

end KanadeRussell.Infra
