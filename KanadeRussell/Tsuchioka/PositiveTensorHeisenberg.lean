import KanadeRussell.Tsuchioka.ExponentialDerivation
import KanadeRussell.Tsuchioka.TensorHeisenberg

/-! The positive Heisenberg commutator of the source tensor root fields.
Creation contributes a single formal monomial; annihilation commutes with
coefficient differentiation. All mode indices are arbitrary integers. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open PowerSeries FormalSeries
open RootData (Lattice rootWeight)

variable {K : Type*} [Field K] [CharZero K]

theorem diagonalDerivative_coeff_tensorRootCreationLog (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) (m : ℕ) :
    diagonalDerivative n (coeff m (tensorRootCreationLog w β j)) =
      if m = n.val then MvPolynomial.C
        (12 * rootWeight (w ^ (-(n.val : ℤ))) β / (n.val : K)) else 0 := by
  classical
  rw [tensorRootCreationLog, coeff_mk]
  by_cases hmn : m = n.val
  · subst m
    simp [n.property, diagonalDerivative_mul, diagonalDerivative_X]
  · split_ifs with hm
    · have hne : (⟨m, hm⟩ : Mode) ≠ n := fun h => hmn (congrArg Subtype.val h)
      simp [diagonalDerivative_mul, diagonalDerivative_X, hne, hmn]
    · simp [hmn]

theorem laurentDiagonalDerivative_tensorRootCreationLog (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) :
    laurentDerivation (diagonalDerivative n)
        (tensorRootCreationLog w β j : LaurentSeries (Space K)) =
      HahnSeries.single (n.val : ℤ) (MvPolynomial.C
        (12 * rootWeight (w ^ (-(n.val : ℤ))) β / (n.val : K))) := by
  classical
  apply HahnSeries.ext
  funext i
  cases i with
  | ofNat m =>
    simp only [coeff_laurentDerivation, Int.ofNat_eq_natCast,
      LaurentSeries.coeff_coe_powerSeries, diagonalDerivative_coeff_tensorRootCreationLog,
      HahnSeries.coeff_single, Int.natCast_inj]
  | negSucc m =>
    have hne : Int.negSucc m ≠ (n.val : ℤ) := by omega
    simp [coeff_laurentDerivation, PowerSeries.coeff_coe, HahnSeries.coeff_single, hne]

theorem laurentDiagonalDerivative_tensorRootCreation (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) :
    laurentDerivation (diagonalDerivative n)
        (tensorRootCreation w β j : LaurentSeries (Space K)) =
      HahnSeries.single (n.val : ℤ) (MvPolynomial.C
        (12 * rootWeight (w ^ (-(n.val : ℤ))) β / (n.val : K))) *
          (tensorRootCreation w β j : LaurentSeries (Space K)) := by
  rw [tensorRootCreation, laurentDerivation_exponential _ _
    (constantCoeff_tensorRootCreationLog w β j),
    laurentDiagonalDerivative_tensorRootCreationLog, mul_comm]

theorem laurentDiagonalDerivative_tensorRootAnnihilation_X (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) (s : Fin 3 × Mode) :
    laurentDerivation (diagonalDerivative n)
        (tensorRootAnnihilation w β j (MvPolynomial.X s)) =
      tensorRootAnnihilation w β j (diagonalDerivative n (MvPolynomial.X s)) := by
  classical
  simp only [tensorRootAnnihilation, MvPolynomial.eval₂Hom_X', map_add,
    laurentDerivation_C, laurentDerivation_single, MvPolynomial.derivation_C,
    map_zero, add_zero, diagonalDerivative_X]
  split_ifs <;> simp

theorem laurentDiagonalDerivative_tensorRootAnnihilation (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) (f : Space K) :
    laurentDerivation (diagonalDerivative n) (tensorRootAnnihilation w β j f) =
      tensorRootAnnihilation w β j (diagonalDerivative n f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [tensorRootAnnihilation, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
      laurentDerivation_C, MvPolynomial.derivation_C, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f s hf =>
    simp only [map_mul, laurentDerivation_mul, diagonalDerivative_mul, map_add,
      hf, laurentDiagonalDerivative_tensorRootAnnihilation_X]

theorem laurentDiagonalDerivative_tensorRootSummand (n : Mode)
    (w : K) (β : Lattice) (j : Fin 3) (f : Space K) :
    laurentDerivation (diagonalDerivative n) (tensorRootSummand w β j f) =
      tensorRootSummand w β j (diagonalDerivative n f) +
      HahnSeries.single (n.val : ℤ) (MvPolynomial.C
        (12 * rootWeight (w ^ (-(n.val : ℤ))) β / (n.val : K))) *
          tensorRootSummand w β j f := by
  simp only [tensorRootSummand, LinearMap.coe_mk, AddHom.coe_mk]
  rw [laurentDerivation_mul, laurentDiagonalDerivative_tensorRootCreation,
    laurentDiagonalDerivative_tensorRootAnnihilation]
  ring

theorem laurentDiagonalDerivative_tensorRootField (n : Mode)
    (w : K) (β : Lattice) (f : Space K) :
    laurentDerivation (diagonalDerivative n) (tensorRootField w β f) =
      tensorRootField w β (diagonalDerivative n f) +
      HahnSeries.single (n.val : ℤ) (MvPolynomial.C
        (12 * rootWeight (w ^ (-(n.val : ℤ))) β / (n.val : K))) *
          tensorRootField w β f := by
  simp only [tensorRootField, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
    map_sum, laurentDiagonalDerivative_tensorRootSummand, RingHom.id_apply,
    Finset.sum_add_distrib, ← Finset.mul_sum, smul_add]
  simp_rw [laurent_smul_eq_coefficient_smul, ← HahnSeries.C_mul_eq_smul]
  ring

theorem diagonalDerivative_tensorRootMode (n : Mode) (w : K) (β : Lattice)
    (i : ℤ) (f : Space K) :
    diagonalDerivative n (tensorRootMode w β i f) =
      tensorRootMode w β i (diagonalDerivative n f) +
        (12 * rootWeight (w ^ (-(n.val : ℤ))) β / (n.val : K)) •
          tensorRootMode w β (i + n.val) f := by
  have h := congrArg (fun g : LaurentSeries (Space K) => g.coeff (-i))
    (laurentDiagonalDerivative_tensorRootField n w β f)
  simp only [coeff_laurentDerivation, HahnSeries.coeff_add,
    HahnSeries.coeff_single_mul, MvPolynomial.C_mul'] at h
  rw [show -i - (n.val : ℤ) = -(i + n.val) by ring] at h
  exact h

theorem heisenbergPositive_tensorRootMode (w : K) (β : Lattice)
    (n : Mode) (i : ℤ) (f : Space K) :
    heisenbergPositive w n (tensorRootMode w β i f) =
      tensorRootMode w β i (heisenbergPositive w n f) +
        (contraction w n.val * rootWeight (w ^ (-(n.val : ℤ))) β) •
          tensorRootMode w β (i + n.val) f := by
  simp only [heisenbergPositive_apply, diagonalDerivative_tensorRootMode, smul_add,
    map_smul, smul_smul]
  congr 1
  congr 1
  have hn : (n.val : K) ≠ 0 := by exact_mod_cast ne_of_gt (mode_pos n)
  field_simp

/-- Positive Heisenberg modes shift the root-mode index by +n. -/
theorem heisenbergPositive_tensorRootMode_commutator (w : K) (β : Lattice)
    (n : Mode) (i : ℤ) :
    (heisenbergPositive w n).comp (tensorRootMode w β i) -
        (tensorRootMode w β i).comp (heisenbergPositive w n) =
      (contraction w n.val * rootWeight (w ^ (-(n.val : ℤ))) β) •
        tensorRootMode w β (i + n.val) := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    heisenbergPositive_tensorRootMode, add_sub_cancel_left]

/-- Negative Heisenberg modes shift the root-mode index by -n. -/
theorem heisenbergNegative_tensorRootMode_commutator (w : K) (β : Lattice)
    (n : Mode) (i : ℤ) :
    (heisenbergNegative n).comp (tensorRootMode w β i) -
        (tensorRootMode w β i).comp (heisenbergNegative n) =
      (contraction w n.val * rootWeight (w ^ (n.val : ℤ)) β) •
        tensorRootMode w β (i - n.val) := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    tensorRootMode_heisenbergNegative, sub_sub_cancel]

end KanadeRussell.Tsuchioka.Fock
