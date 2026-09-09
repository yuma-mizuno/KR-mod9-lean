import KanadeRussell.Tsuchioka.TensorRootFields
import KanadeRussell.Tsuchioka.HeisenbergCyclicSpace

/-! The tensor root fields have the source Heisenberg commutator.
The coefficient shift is proved for every integer root-mode index. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open RootData (Lattice rootWeight)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorRootAnnihilation_diagonalCoordinate (w : K) (β : Lattice)
    (j : Fin 3) (n : Mode) :
    tensorRootAnnihilation w β j (diagonalCoordinate n) =
      HahnSeries.C (diagonalCoordinate n) -
        HahnSeries.single (-(n.val : ℤ))
          (MvPolynomial.C (contraction w n.val * rootWeight (w ^ (n.val : ℤ)) β)) := by
  classical
  have hs : (∑ i : Fin 3, HahnSeries.single (-(n.val : ℤ)) (MvPolynomial.C
      (if i = j then -contraction w n.val * rootWeight (w ^ (n.val : ℤ)) β else 0)) :
      LaurentSeries (Space K)) =
      -HahnSeries.single (-(n.val : ℤ))
        (MvPolynomial.C (contraction w n.val * rootWeight (w ^ (n.val : ℤ)) β)) := by
    rw [Finset.sum_eq_single j]
    · simp [neg_mul, map_neg, HahnSeries.single_neg]
    · intro i hi hij
      simp [hij]
    · simp
  simp only [diagonalCoordinate, map_sum, tensorRootAnnihilation,
    MvPolynomial.eval₂Hom_X', Finset.sum_add_distrib]
  rw [hs, ← map_sum]
  exact (sub_eq_add_neg _ _).symm

theorem tensorRootSummand_heisenbergNegative (w : K) (β : Lattice)
    (j : Fin 3) (n : Mode) (f : Space K) :
    tensorRootSummand w β j (heisenbergNegative n f) =
      (HahnSeries.C (diagonalCoordinate n) -
        HahnSeries.single (-(n.val : ℤ))
          (MvPolynomial.C (contraction w n.val * rootWeight (w ^ (n.val : ℤ)) β))) *
        tensorRootSummand w β j f := by
  rw [heisenbergNegative_apply]
  simp only [tensorRootSummand, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_mul, tensorRootAnnihilation_diagonalCoordinate]
  exact mul_left_comm _ _ _

theorem tensorRootField_heisenbergNegative (w : K) (β : Lattice)
    (n : Mode) (f : Space K) :
    tensorRootField w β (heisenbergNegative n f) =
      (HahnSeries.C (diagonalCoordinate n) -
        HahnSeries.single (-(n.val : ℤ))
          (MvPolynomial.C (contraction w n.val * rootWeight (w ^ (n.val : ℤ)) β))) *
        tensorRootField w β f := by
  simp only [tensorRootField, LinearMap.smul_apply, LinearMap.sum_apply,
    tensorRootSummand_heisenbergNegative, ← Finset.mul_sum]
  simp_rw [laurent_smul_eq_coefficient_smul, ← HahnSeries.C_mul_eq_smul]
  exact mul_left_comm _ _ _

/-- The negative Heisenberg commutator of X has the source shift i-n. -/
theorem tensorRootMode_heisenbergNegative (w : K) (β : Lattice)
    (n : Mode) (i : ℤ) (f : Space K) :
    tensorRootMode w β i (heisenbergNegative n f) =
      heisenbergNegative n (tensorRootMode w β i f) -
        (contraction w n.val * rootWeight (w ^ (n.val : ℤ)) β) •
          tensorRootMode w β (i - n.val) f := by
  change (tensorRootField w β (heisenbergNegative n f)).coeff (-i) =
    diagonalCoordinate n * (tensorRootField w β f).coeff (-i) -
      (contraction w n.val * rootWeight (w ^ (n.val : ℤ)) β) •
        (tensorRootField w β f).coeff (-(i - n.val))
  rw [tensorRootField_heisenbergNegative, sub_mul, HahnSeries.coeff_sub,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_single_mul]
  rw [show -i - (-(n.val : ℤ)) = -(i - n.val) by ring, MvPolynomial.C_mul']
  rfl

end KanadeRussell.Tsuchioka.Fock
