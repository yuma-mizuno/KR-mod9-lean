import KanadeRussell.Representation.PrincipalModeCartan
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A finite change of coordinates in a normal-ordered quadratic expression.
The operator products retain their original order. Vanishing diagonal pairing
coefficients are allowed: only the coordinate matrices have an inverse relation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open scoped BigOperators

section FiniteAlgebra
variable {K A I : Type*} [CommSemiring K] [Semiring A] [Algebra K A]
  [Fintype I] [DecidableEq I]

/-- Replacing the positive operators by columns of P and the weighted negative
operators by rows of Q preserves their normal-ordered sum when P Q = 1.
The algebra A need not be commutative, and gInv may vanish. -/
theorem normalOrdered_basisChange (Xminus Xplus : I → A) (gInv : I → K)
    (P Q : Matrix I I K) (hPQ : P * Q = 1) :
    (∑ s : I, (∑ r : I, (gInv r * Q s r) • Xminus r) *
      (∑ t : I, P t s • Xplus t)) =
      ∑ r : I, gInv r • (Xminus r * Xplus r) := by
  have hcoeff (r t : I) :
      (∑ s : I, (gInv r * Q s r) * P t s) = gInv r * (P * Q) t r := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  simp_rw [Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm, smul_smul]
  calc
    (∑ s : I, ∑ r : I, ∑ t : I,
        ((gInv r * Q s r) * P t s) • (Xminus r * Xplus t)) =
        ∑ r : I, ∑ t : I,
          (∑ s : I, (gInv r * Q s r) * P t s) • (Xminus r * Xplus t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_smul]
    _ = _ := by
      simp [hcoeff, hPQ, Matrix.one_apply]

end FiniteAlgebra

open Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

/-- The actual principal-mode quadratic summand in any coordinates with
P Q = 1, including inactive Heisenberg coordinates whose inverse pairing is zero. -/
theorem normalOrderedMode_basisChange (w : K) (n : ℤ)
    (P Q : Matrix (Fin 3) (Fin 3) K) (hPQ : P * Q = 1) :
    (∑ s : Fin 3,
      principalModeCombination w (-n)
        (fun r => (modePairingCoefficient w n r)⁻¹ * Q s r) *
      principalModeCombination w n (fun t => P t s)) = normalOrderedMode w n := by
  simpa only [principalModeCombination_apply, normalOrderedMode] using
    normalOrdered_basisChange (principalMode w (-n)) (principalMode w n)
      (fun r => (modePairingCoefficient w n r)⁻¹) P Q hPQ

end KanadeRussell.Representation
