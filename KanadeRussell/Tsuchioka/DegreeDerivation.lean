import KanadeRussell.Tsuchioka.DiagonalDerivations
import KanadeRussell.Tsuchioka.DegreeOperator
import Mathlib.RingTheory.Derivation.Lie

/-! The polynomial energy is a derivation. Its commutator with diagonal
differentiation gives the Heisenberg grading relation. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

theorem degreeOperator_one : degreeOperator (1 : Space K) = 0 := by
  have h : (1 : Space K) ∈ grade 0 :=
    MvPolynomial.isWeightedHomogeneous_one K variableWeight
  simpa only [Int.cast_zero, zero_smul] using degreeOperator_eq_of_grade 0 1 h

theorem degreeOperator_X (s : Fin 3 × Mode) :
    degreeOperator (MvPolynomial.X s : Space K) = (s.2.val : K) • MvPolynomial.X s := by
  simpa only [variableWeight, Int.cast_natCast] using
    degreeOperator_eq_of_grade (variableWeight s) (MvPolynomial.X s)
      (MvPolynomial.isWeightedHomogeneous_X K variableWeight s)

theorem degreeOperator_mul (f g : Space K) :
    degreeOperator (f * g) = degreeOperator f * g + f * degreeOperator g := by
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    induction g using MvPolynomial.induction_on' with
    | monomial n e =>
      simp only [MvPolynomial.monomial_mul, degreeOperator_monomial,
        map_add, Int.cast_add, add_smul, smul_mul_assoc, mul_smul_comm]
    | add g h hg hh =>
      simp only [mul_add, map_add, hg, hh]
      abel
  | add f h hf hh =>
    simp only [add_mul, map_add, hf, hh]
    abel

noncomputable def energyDerivation : Derivation K (Space K) (Space K) where
  toLinearMap := degreeOperator
  map_one_eq_zero' := degreeOperator_one
  leibniz' f g := by
    simpa only [smul_eq_mul, mul_comm, add_comm] using degreeOperator_mul f g

@[simp] theorem energyDerivation_apply (f : Space K) :
    energyDerivation f = degreeOperator f := rfl

theorem diagonalDerivative_energy_bracket (n : Mode) :
    ⁅diagonalDerivative (K := K) n, energyDerivation (K := K)⁆ =
      (n.val : K) • diagonalDerivative n := by
  classical
  apply MvPolynomial.derivation_ext
  intro s
  simp only [Derivation.commutator_apply, energyDerivation_apply, degreeOperator_X,
    Derivation.map_smul, diagonalDerivative_X, Derivation.smul_apply]
  split_ifs with h
  · rw [h, degreeOperator_one, sub_zero]
  · simp

theorem diagonalDerivative_degreeOperator (n : Mode) (f : Space K) :
    diagonalDerivative n (degreeOperator f) =
      degreeOperator (diagonalDerivative n f) + (n.val : K) • diagonalDerivative n f := by
  have h := congrArg (fun D : Derivation K (Space K) (Space K) => D f)
    (diagonalDerivative_energy_bracket (K := K) n)
  change diagonalDerivative n (degreeOperator f) -
    degreeOperator (diagonalDerivative n f) = (n.val : K) • diagonalDerivative n f at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem diagonalDerivative_commute (m n : Mode) (f : Space K) :
    diagonalDerivative m (diagonalDerivative n f) =
      diagonalDerivative n (diagonalDerivative m f) := by
  classical
  have hz : ⁅diagonalDerivative (K := K) m, diagonalDerivative (K := K) n⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro s
    simp only [Derivation.commutator_apply, diagonalDerivative_X, Derivation.zero_apply]
    split_ifs <;> simp [(diagonalDerivative (K := K) m).map_one_eq_zero,
      (diagonalDerivative (K := K) n).map_one_eq_zero]
  have h := congrArg (fun D : Derivation K (Space K) (Space K) => D f) hz
  exact sub_eq_zero.mp h

end KanadeRussell.Tsuchioka.Fock
