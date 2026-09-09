import KanadeRussell.Tsuchioka.CoefficientDerivations
import KanadeRussell.Tsuchioka.RootFock
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! The diagonal polynomial derivations annihilate every root creation field
and commute with its polynomial substitution. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries PowerSeries
open RootData (Lattice)

variable {K : Type*} [Field K] [CharZero K]

/-- Simultaneous differentiation of the three variables of the given mode. -/
noncomputable def diagonalDerivative (n : Mode) : Derivation K (Space K) (Space K) :=
  MvPolynomial.mkDerivation K fun s : Fin 3 × Mode => if s.2 = n then 1 else 0

@[simp] theorem diagonalDerivative_X (n : Mode) (s : Fin 3 × Mode) :
    diagonalDerivative (K := K) n (MvPolynomial.X s) = if s.2 = n then 1 else 0 := by
  simp [diagonalDerivative]

theorem diagonalDerivative_mul (n : Mode) (f g : Space K) :
    diagonalDerivative n (f * g) =
      diagonalDerivative n f * g + f * diagonalDerivative n g := by
  simpa only [smul_eq_mul, mul_comm, add_comm] using
    (diagonalDerivative (K := K) n).leibniz f g

theorem sum_tensorExponent_left (j : Fin 3) :
    ∑ i : Fin 3, tensorExponent (K := K) i j = 0 := by
  have he (i : Fin 3) : tensorExponent (K := K) i j = tensorExponent j i := by
    simp only [tensorExponent, eq_comm]
  simpa only [he] using sum_tensorExponent (K := K) j

theorem diagonalDerivative_coeff_creationLog (n : Mode) (j : Fin 3) (m : ℕ) :
    diagonalDerivative n (coeff m (creationLog (K := K) j)) = 0 := by
  classical
  rw [creationLog, coeff_mk]
  split_ifs with hm
  · rw [map_sum]
    simp only [diagonalDerivative_mul, MvPolynomial.derivation_C,
      zero_mul, zero_add, diagonalDerivative_X]
    by_cases hmn : (⟨m, hm⟩ : Mode) = n
    · simp only [hmn, if_true, mul_one]
      rw [← map_sum]
      have hs : ∑ i : Fin 3, -4 * tensorExponent (K := K) i j / (m : K) = 0 := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum,
          sum_tensorExponent_left, mul_zero, zero_mul]
      rw [hs, map_zero]
    · simp only [hmn, if_false, mul_zero, Finset.sum_const_zero]
  · exact map_zero _

theorem diagonalDerivative_coeff_rootCreationLog (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) (m : ℕ) :
    diagonalDerivative n (coeff m (rootCreationLog w β j)) = 0 := by
  simp only [rootCreationLog, coeff_mk, diagonalDerivative_mul,
    MvPolynomial.derivation_C, diagonalDerivative_coeff_creationLog, zero_mul,
    mul_zero, add_zero]

theorem diagonalDerivative_coeff_rootCreation (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) (m : ℕ) :
    diagonalDerivative n (coeff m (rootCreation w β j)) = 0 :=
  derivation_coeff_exponential_zero (diagonalDerivative n) (rootCreationLog w β j)
    (constantCoeff_rootCreationLog w β j)
    (diagonalDerivative_coeff_rootCreationLog n w β j) m

theorem laurentDiagonalDerivative_rootCreation (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) :
    laurentDerivation (diagonalDerivative n)
      (rootCreation w β j : LaurentSeries (Space K)) = 0 :=
  laurentDerivation_powerSeries_eq_zero (diagonalDerivative n) (rootCreation w β j)
    (diagonalDerivative_coeff_rootCreation n w β j)

theorem laurentDiagonalDerivative_rootAnnihilation_X (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) (s : Fin 3 × Mode) :
    laurentDerivation (diagonalDerivative n)
        (rootAnnihilation w β j (MvPolynomial.X s)) =
      rootAnnihilation w β j (diagonalDerivative n (MvPolynomial.X s)) := by
  classical
  simp only [rootAnnihilation, MvPolynomial.eval₂Hom_X', map_add,
    laurentDerivation_C, laurentDerivation_single, MvPolynomial.derivation_C,
    map_zero, add_zero, diagonalDerivative_X]
  split_ifs <;> simp

/-- Polynomial substitution by constants commutes with diagonal differentiation. -/
theorem laurentDiagonalDerivative_rootAnnihilation (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) (f : Space K) :
    laurentDerivation (diagonalDerivative n) (rootAnnihilation w β j f) =
      rootAnnihilation w β j (diagonalDerivative n f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [rootAnnihilation, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
      laurentDerivation_C, MvPolynomial.derivation_C, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f s hf =>
    simp only [map_mul, laurentDerivation_mul, diagonalDerivative_mul, map_add,
      hf, laurentDiagonalDerivative_rootAnnihilation_X]

theorem laurentDiagonalDerivative_rootSummand (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) (f : Space K) :
    laurentDerivation (diagonalDerivative n) (rootSummand w β j f) =
      rootSummand w β j (diagonalDerivative n f) := by
  change laurentDerivation _ ((rootCreation w β j : LaurentSeries (Space K)) *
    rootAnnihilation w β j f) = _
  rw [laurentDerivation_mul, laurentDiagonalDerivative_rootCreation, zero_mul,
    zero_add, laurentDiagonalDerivative_rootAnnihilation]
  rfl

theorem laurentDiagonalDerivative_rootField (n : Mode)
    (w : K) (β : Lattice) (f : Space K) :
    laurentDerivation (diagonalDerivative n) (rootField w β f) =
      rootField w β (diagonalDerivative n f) := by
  simp only [rootField, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
    map_sum, laurentDiagonalDerivative_rootSummand, RingHom.id_apply]

/-- Every constructed root mode commutes with every diagonal positive
Heisenberg derivation, for arbitrary lattice elements and polynomial inputs. -/
theorem diagonalDerivative_rootMode (n : Mode) (w : K) (β : Lattice)
    (i : ℤ) (f : Space K) :
    diagonalDerivative n (rootMode w β i f) =
      rootMode w β i (diagonalDerivative n f) := by
  exact congrArg (fun g : LaurentSeries (Space K) => g.coeff (-i))
    (laurentDiagonalDerivative_rootField n w β f)

theorem diagonalDerivative_mode (n : Mode) (w : K) (i : ℤ) (f : Space K) :
    diagonalDerivative n (mode w i f) = mode w i (diagonalDerivative n f) := by
  simpa only [rootMode_first] using
    diagonalDerivative_rootMode n w (RootData.simpleRoot 0) i f

end KanadeRussell.Tsuchioka.Fock
