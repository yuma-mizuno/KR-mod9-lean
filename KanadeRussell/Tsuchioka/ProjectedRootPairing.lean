import KanadeRussell.Tsuchioka.PositiveTensorHeisenberg
import KanadeRussell.Tsuchioka.RootCovariance

/-! The source Cartan pairing for the projected first-root Heisenberg
operators. Polynomial certificates are checked for all lattice inputs,
then substituted at every positive and negative allowed mode. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.RootData

variable {K : Type*} [Field K] [CharZero K]

def firstSpectralScalar (t : K) : K := 1 / 2 + t / 3 - t ^ 3 / 6

def firstPairingPolynomial (t : K) (β : Lattice) : K :=
  (1 / 12 : K) * ∑ p : Fin 12,
    (pairing ((coxeter^[p.val]) (simpleRoot 0)) β : K) * t ^ p.val

/-- The full Fourier polynomial, with the actual D4 Cartan form. -/
theorem firstPairingPolynomial_eq (t : K) (ht : t ^ 4 - t ^ 2 + 1 = 0) (β : Lattice) :
    firstPairingPolynomial t β = firstSpectralScalar t * rootWeight t β := by
  norm_num [firstPairingPolynomial, firstSpectralScalar, Fin.sum_univ_succ,
    Function.iterate_succ_apply', coxeter_apply, pairing, simpleRoot, rootWeight]
  push_cast
  linear_combination (((1 / 12) * t ^ 7 + (1 / 12) * t ^ 6 + (1 / 12) * t ^ 5 - (1 / 12) * t ^ 3 - (1 / 4) * t ^ 2 - (1 / 4) * t - (1 / 3)) * (β 0 : K)
    + (-(1 / 12) * t ^ 7 - (1 / 6) * t ^ 5 + (1 / 12) * t ^ 4 - (1 / 12) * t ^ 3 + (1 / 3) * t ^ 2 - (1 / 12)) * (β 1 : K)
    + ((1 / 12) * t ^ 7 - (1 / 12) * t ^ 6 + (1 / 12) * t ^ 5 - (1 / 6) * t ^ 4 - (1 / 12) * t ^ 3 - (1 / 4) * t ^ 2 - (1 / 12) * t + (1 / 2)) * (β 2 : K)
    + (-(1 / 12) * t ^ 7 - (1 / 12) * t ^ 6 - (1 / 12) * t ^ 5 - (1 / 6) * t ^ 4 + (1 / 12) * t ^ 3 - (1 / 12) * t ^ 2 + (5 / 12) * t) * (β 3 : K)) * ht

theorem firstSpectralScalar_inv (t : K) (ht : t ^ 4 - t ^ 2 + 1 = 0) :
    firstSpectralScalar t⁻¹ = firstSpectralScalar t := by
  have hi : t⁻¹ = t - t ^ 3 := inv_eq_of_mul_eq_one_left (by linear_combination -ht)
  rw [hi]
  unfold firstSpectralScalar
  linear_combination ((1 / 6) * t ^ 5 - (1 / 3) * t ^ 3) * ht

/-- Pairing the Fourier projection of beta_1 with an arbitrary lattice vector. -/
noncomputable def projectedFirstPairing (w : K) (n : ℤ) (β : Lattice) : K :=
  (1 / 12 : K) * ∑ p : Fin 12,
    (pairing ((coxeter^[p.val]) (simpleRoot 0)) β : K) * w ^ (-(n * p.val))

theorem projectedFirstPairing_eq_spectral (w : K) (n : ℤ) (β : Lattice)
    (ht : (w ^ (-n)) ^ 4 - (w ^ (-n)) ^ 2 + 1 = 0) :
    projectedFirstPairing w n β = firstSpectralScalar (w ^ (-n)) * rootWeight (w ^ (-n)) β := by
  have hp (p : Fin 12) : (w ^ (-n)) ^ p.val = w ^ (-(n * p.val)) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  simpa only [firstPairingPolynomial, hp, projectedFirstPairing] using
    firstPairingPolynomial_eq (w ^ (-n)) ht β

end KanadeRussell.Tsuchioka.RootData

namespace KanadeRussell.Tsuchioka.Fock

open RootData

variable {K : Type*} [Field K] [CharZero K]

theorem contraction_eq_firstSpectralScalar (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (n : Mode) : contraction w n.val = firstSpectralScalar (w ^ (-(n.val : ℤ))) := by
  simpa only [projectedFirstPairing, contraction, orbitPairing, rootWeight_first, mul_one] using
    projectedFirstPairing_eq_spectral w n.val (simpleRoot 0) (mode_inverse_cyclotomic w hw n)

theorem projectedFirstPairing_positive (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (n : Mode) (β : Lattice) : projectedFirstPairing w n.val β =
      contraction w n.val * rootWeight (w ^ (-(n.val : ℤ))) β := by
  rw [projectedFirstPairing_eq_spectral w n.val β (mode_inverse_cyclotomic w hw n),
    contraction_eq_firstSpectralScalar w hw n]

theorem projectedFirstPairing_negative (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (n : Mode) (β : Lattice) : projectedFirstPairing w (-(n.val : ℤ)) β =
      contraction w n.val * rootWeight (w ^ (n.val : ℤ)) β := by
  have ht : (w ^ (n.val : ℤ)) ^ 4 - (w ^ (n.val : ℤ)) ^ 2 + 1 = 0 := by
    simpa only [zpow_natCast] using mode_cyclotomic w hw n
  have hs : firstSpectralScalar (w ^ (n.val : ℤ)) = contraction w n.val := by
    rw [← firstSpectralScalar_inv _ ht, contraction_eq_firstSpectralScalar w hw n, zpow_neg]
  rw [projectedFirstPairing_eq_spectral w (-(n.val : ℤ)) β (by simpa using ht)]
  simpa only [neg_neg, hs]

theorem heisenbergPositive_tensorRootMode_projected_commutator (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (β : Lattice) (n : Mode) (i : ℤ) :
    (heisenbergPositive w n).comp (tensorRootMode w β i) -
        (tensorRootMode w β i).comp (heisenbergPositive w n) =
      projectedFirstPairing w n.val β • tensorRootMode w β (i + n.val) := by
  rw [projectedFirstPairing_positive w hw n β]
  exact heisenbergPositive_tensorRootMode_commutator w β n i

theorem heisenbergNegative_tensorRootMode_projected_commutator (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (β : Lattice) (n : Mode) (i : ℤ) :
    (heisenbergNegative n).comp (tensorRootMode w β i) -
        (tensorRootMode w β i).comp (heisenbergNegative n) =
      projectedFirstPairing w (-(n.val : ℤ)) β • tensorRootMode w β (i - n.val) := by
  rw [projectedFirstPairing_negative w hw n β]
  exact heisenbergNegative_tensorRootMode_commutator w β n i

end KanadeRussell.Tsuchioka.Fock
