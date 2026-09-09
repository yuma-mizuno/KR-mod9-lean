import KanadeRussell.Tsuchioka.DegreeDerivation
import KanadeRussell.Tsuchioka.Contractions

/-! The source-normalized diagonal Heisenberg operators on triple Fock space
and their common positive-mode kernel. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open RootData (Lattice)

variable {K : Type*} [Field K] [CharZero K]

theorem diagonalDerivative_eq_sum_pderiv (n : Mode) :
    diagonalDerivative (K := K) n =
      ∑ j : Fin 3, MvPolynomial.pderiv (j, n) := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨j, m⟩
  simp only [Fin.sum_univ_three, Derivation.add_apply, diagonalDerivative_X,
    MvPolynomial.pderiv_X, Pi.single_apply]
  by_cases h : m = n
  · subst m
    fin_cases j <;> simp
  · simp [Prod.mk.injEq, h, Ne.symm h]

noncomputable def diagonalCoordinate (n : Mode) : Space K :=
  ∑ j : Fin 3, MvPolynomial.X (j, n)

theorem diagonalDerivative_coordinate (n m : Mode) :
    diagonalDerivative n (diagonalCoordinate (K := K) m) =
      if m = n then 3 else 0 := by
  classical
  simp only [diagonalCoordinate, map_sum, diagonalDerivative_X]
  split_ifs <;> simp

/-- beta_1(n) = n kappa_n / 12 times the sum of the three partial derivatives. -/
noncomputable def heisenbergPositive (w : K) (n : Mode) : Module.End K (Space K) :=
  (n.val * contraction w n.val / 12 : K) • (diagonalDerivative n).toLinearMap

/-- beta_1(-n) is multiplication by the sum of the three oscillator variables. -/
noncomputable def heisenbergNegative (n : Mode) : Module.End K (Space K) :=
  LinearMap.mulLeft K (diagonalCoordinate n)

@[simp] theorem heisenbergPositive_apply (w : K) (n : Mode) (f : Space K) :
    heisenbergPositive w n f =
      (n.val * contraction w n.val / 12 : K) • diagonalDerivative n f := rfl

@[simp] theorem heisenbergNegative_apply (n : Mode) (f : Space K) :
    heisenbergNegative n f = diagonalCoordinate n * f := rfl

theorem heisenbergPositive_scale_ne_zero (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (n : Mode) : (n.val * contraction w n.val / 12 : K) ≠ 0 :=
  div_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mode_pos n)))
    (contraction_ne_zero w hw n)) (by norm_num)

theorem heisenbergPositive_commute (w : K) (m n : Mode) (f : Space K) :
    heisenbergPositive w m (heisenbergPositive w n f) =
      heisenbergPositive w n (heisenbergPositive w m f) := by
  simp only [heisenbergPositive_apply, Derivation.map_smul, diagonalDerivative_commute m n]
  exact smul_comm _ _ _

theorem heisenbergNegative_commute (m n : Mode) (f : Space K) :
    heisenbergNegative m (heisenbergNegative n f) =
      heisenbergNegative n (heisenbergNegative m f) := by
  simp only [heisenbergNegative_apply]
  ring

/-- The mixed bracket has level three. kappa_n already includes the Fourier
factor 1/12, so the bracket is n kappa_n / 12 times the level scalar. -/
theorem heisenberg_mixed_commutator (w : K) (n m : Mode) (f : Space K) :
    heisenbergPositive w n (heisenbergNegative m f) -
        heisenbergNegative m (heisenbergPositive w n f) =
      if m = n then
        (n.val * contraction w n.val / 12 : K) • ((3 : K) • f)
      else 0 := by
  classical
  simp only [heisenbergPositive_apply, heisenbergNegative_apply,
    diagonalDerivative_mul, diagonalDerivative_coordinate,
    smul_add, mul_smul_comm, add_sub_cancel_right]
  split_ifs
  · congr 1
    simp [Algebra.smul_def, map_ofNat]
  · simp

/-- The vacuum space for the actual diagonal positive Heisenberg action. -/
noncomputable def heisenbergVacuum (w : K) : Submodule K (Space K) :=
  ⨅ n : Mode, LinearMap.ker (heisenbergPositive w n)

theorem mem_heisenbergVacuum (w : K) (f : Space K) :
    f ∈ heisenbergVacuum w ↔ ∀ n : Mode, heisenbergPositive w n f = 0 := by
  simp only [heisenbergVacuum, Submodule.mem_iInf, LinearMap.mem_ker]

theorem mem_heisenbergVacuum_iff_derivative (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) :
    f ∈ heisenbergVacuum w ↔ ∀ n : Mode, diagonalDerivative n f = 0 := by
  rw [mem_heisenbergVacuum]
  simp only [heisenbergPositive_apply, smul_eq_zero,
    heisenbergPositive_scale_ne_zero w hw, false_or]

theorem one_mem_heisenbergVacuum (w : K) : (1 : Space K) ∈ heisenbergVacuum w := by
  rw [mem_heisenbergVacuum]
  intro n
  simp only [heisenbergPositive_apply, Derivation.map_one_eq_zero, smul_zero]

theorem heisenbergPositive_rootMode (w : K) (n : Mode) (β : Lattice)
    (i : ℤ) (f : Space K) :
    heisenbergPositive w n (rootMode w β i f) =
      rootMode w β i (heisenbergPositive w n f) := by
  simp only [heisenbergPositive_apply, diagonalDerivative_rootMode, map_smul]

theorem rootMode_mem_heisenbergVacuum (w : K) (β : Lattice) (i : ℤ)
    (f : Space K) (hf : f ∈ heisenbergVacuum w) :
    rootMode w β i f ∈ heisenbergVacuum w := by
  rw [mem_heisenbergVacuum] at hf ⊢
  intro n
  rw [heisenbergPositive_rootMode, hf, map_zero]

theorem mode_mem_heisenbergVacuum (w : K) (i : ℤ)
    (f : Space K) (hf : f ∈ heisenbergVacuum w) :
    mode w i f ∈ heisenbergVacuum w := by
  simpa only [rootMode_first] using
    rootMode_mem_heisenbergVacuum w (RootData.simpleRoot 0) i f hf

theorem degreeOperator_mem_heisenbergVacuum (w : K)
    (f : Space K) (hf : f ∈ heisenbergVacuum w) :
    degreeOperator f ∈ heisenbergVacuum w := by
  rw [mem_heisenbergVacuum] at hf ⊢
  intro n
  have h := hf n
  simp only [heisenbergPositive_apply] at h ⊢
  rw [diagonalDerivative_degreeOperator, smul_add, ← map_smul, h, map_zero]
  rw [smul_comm, h, smul_zero, add_zero]

end KanadeRussell.Tsuchioka.Fock
