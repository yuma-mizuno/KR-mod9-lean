import KanadeRussell.Tsuchioka.ProjectedRootPairing

/-! The full D4 orbit pairing is a product of the two normalized Coxeter
weights at every twelfth root, including the absent oscillator phases.
The polynomial certificate is checked for arbitrary lattice inputs. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace KanadeRussell.Tsuchioka.RootData

variable {K : Type*} [Field K] [CharZero K]

def orbitPairingPolynomial (t : K) (beta gamma : Lattice) : K :=
  ∑ p : Fin 12, (pairing ((coxeter^[p.val]) beta) gamma : K) * t ^ p.val

def firstOrbitPolynomial (t : K) : K :=
  2 + t + t ^ 2 - t ^ 4 - t ^ 5 - 2 * t ^ 6 - t ^ 7 - t ^ 8 + t ^ 10 + t ^ 11

def inverseRootWeight (t : K) (beta : Lattice) : K :=
  beta 0 - beta 2 + (beta 2 - beta 3 : K) * t ^ 11 +
    (-(beta 1 : K) + beta 2 + beta 3) * t ^ 10 +
    (beta 1 - beta 2 : K) * t ^ 9

theorem inverseRootWeight_eq (t : K) (ht : t ^ 12 = 1) (beta : Lattice) :
    inverseRootWeight t beta = rootWeight t⁻¹ beta := by
  have hi : t⁻¹ = t ^ 11 := inv_eq_of_mul_eq_one_left (by
    calc
      t ^ 11 * t = t ^ 12 := by ring
      _ = 1 := ht)
  have h22 : (t ^ 11) ^ 2 = t ^ 10 := by
    calc
      (t ^ 11) ^ 2 = t ^ 12 * t ^ 10 := by ring
      _ = t ^ 10 := by rw [ht, one_mul]
  have h33 : (t ^ 11) ^ 3 = t ^ 9 := by
    calc
      (t ^ 11) ^ 3 = (t ^ 12) ^ 2 * t ^ 9 := by ring
      _ = t ^ 9 := by rw [ht]; simp
  simp only [rootWeight, hi, h22, h33, inverseRootWeight]
  ring

theorem orbitPairingPolynomial_factor (t : K) (ht : t ^ 12 = 1)
    (beta gamma : Lattice) :
    orbitPairingPolynomial t beta gamma =
      firstOrbitPolynomial t * inverseRootWeight t beta * rootWeight t gamma := by
  norm_num [orbitPairingPolynomial, firstOrbitPolynomial, inverseRootWeight, rootWeight,
    Fin.sum_univ_succ, Function.iterate_succ_apply', coxeter_apply, pairing]
  push_cast
  linear_combination ((1 - t ^ 2) * (beta 0 : K) * (gamma 1 : K)
    + (t ^ 2 - 2) * (beta 0 : K) * (gamma 2 : K)
    + (-t) * (beta 0 : K) * (gamma 3 : K)
    + (t ^ 9 - t ^ 7 - t ^ 6 - t ^ 4 + t ^ 3 + t + 1) * (beta 1 : K) * (gamma 0 : K)
    + (t ^ 12 - t ^ 11 - t ^ 10 + t ^ 8 - t ^ 7 + 2 * t ^ 6 - t ^ 5 + t ^ 4 - t ^ 2 + t - 2) * (beta 1 : K) * (gamma 1 : K)
    + (-t ^ 12 + t ^ 11 + 2 * t ^ 10 - t ^ 9 - 2 * t ^ 8 + t ^ 7 - t ^ 6 + t ^ 4 - t ^ 3 + 2 * t ^ 2 - t + 1) * (beta 1 : K) * (gamma 2 : K)
    + (t ^ 11 - t ^ 10 - t ^ 9 + t ^ 7 - t ^ 6 + 2 * t ^ 5 - t ^ 4 + t ^ 3 - t + 1) * (beta 1 : K) * (gamma 3 : K)
    + (-t ^ 10 - 2 * t ^ 9 + 2 * t ^ 7 + 2 * t ^ 6 + 2 * t ^ 5 + 2 * t ^ 4 - 2 * t - 2) * (beta 2 : K) * (gamma 0 : K)
    + (-t ^ 13 - t ^ 12 + 2 * t ^ 11 + 2 * t ^ 10 - 2 * t ^ 6 - 2 * t ^ 4 + t ^ 2 + 1) * (beta 2 : K) * (gamma 1 : K)
    + (t ^ 13 + t ^ 12 - 3 * t ^ 11 - 3 * t ^ 10 + 2 * t ^ 9 + 2 * t ^ 8 + 2 * t ^ 6 - 3 * t ^ 2) * (beta 2 : K) * (gamma 2 : K)
    + (-t ^ 12 - t ^ 11 + 2 * t ^ 10 + 2 * t ^ 9 - 2 * t ^ 5 - 2 * t ^ 3 + t) * (beta 2 : K) * (gamma 3 : K)
    + (t ^ 10 - t ^ 8 - t ^ 7 - t ^ 5 + t ^ 4 + t ^ 2 + t) * (beta 3 : K) * (gamma 0 : K)
    + (t ^ 13 - t ^ 12 - t ^ 11 + t ^ 9 - t ^ 8 + 2 * t ^ 7 - t ^ 6 + t ^ 5 - t ^ 3 + t ^ 2 - 2 * t + 1) * (beta 3 : K) * (gamma 1 : K)
    + (-t ^ 13 + t ^ 12 + 2 * t ^ 11 - t ^ 10 - 2 * t ^ 9 + t ^ 8 - t ^ 7 + t ^ 5 - t ^ 4 + 2 * t ^ 3 - t ^ 2 + t) * (beta 3 : K) * (gamma 2 : K)
    + (t ^ 12 - t ^ 11 - t ^ 10 + t ^ 8 - t ^ 7 + 2 * t ^ 6 - t ^ 5 + t ^ 4 - t ^ 2 + t - 2) * (beta 3 : K) * (gamma 3 : K)) * ht

theorem orbitPairingPolynomial_eq_weights (t : K) (ht : t ^ 12 = 1)
    (beta gamma : Lattice) :
    orbitPairingPolynomial t beta gamma =
      firstOrbitPolynomial t * rootWeight t⁻¹ beta * rootWeight t gamma := by
  rw [orbitPairingPolynomial_factor t ht, inverseRootWeight_eq t ht]

theorem firstOrbitPolynomial_eq (t : K) :
    firstOrbitPolynomial t = orbitPairingPolynomial t (simpleRoot 0) (simpleRoot 0) := by
  simp [firstOrbitPolynomial, orbitPairingPolynomial, first_root_orbit_pairing,
    Fin.sum_univ_succ]
  ring

end KanadeRussell.Tsuchioka.RootData
