import KanadeRussell.Heisenberg.GradedVacuum
import KanadeRussell.Tsuchioka.TensorCyclicity
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! The actual polynomial oscillators, and every tensor cyclic submodule,
instantiate the grading needed for degreewise vacuum lifting. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Heisenberg
open Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

theorem diagonalDerivative_mem_grade (n : Mode) (d : ℤ) (f : Space K) (hf : f ∈ grade d) :
    diagonalDerivative n f ∈ grade (d-n.val) := by
  have h (j : Fin 3) : MvPolynomial.pderiv (j,n) f ∈ grade (d-n.val) :=
    MvPolynomial.IsWeightedHomogeneous.pderiv hf (by dsimp [variableWeight]; ring)
  rw [diagonalDerivative_eq_sum_pderiv]
  simp only [Fin.sum_univ_three, Derivation.add_apply]
  exact (grade (d-n.val)).add_mem ((grade (d-n.val)).add_mem (h 0) (h 1)) (h 2)

omit [CharZero K] in

theorem diagonalCoordinate_mem_grade (n : Mode) :
    diagonalCoordinate (K := K) n ∈ grade (n.val:ℤ) := by
  apply Submodule.sum_mem
  intro j hj
  exact MvPolynomial.isWeightedHomogeneous_X K variableWeight (j,n)

theorem normalized_diagonal_pair (n : Mode) (f : Space K) :
    diagonalDerivative n (((1/3:K) • heisenbergNegative n) f) =
      ((1/3:K) • heisenbergNegative n) (diagonalDerivative n f) + f := by
  have h (g : Space K) : diagonalDerivative n (heisenbergNegative n g) =
      heisenbergNegative n (diagonalDerivative n g) + (3:K) • g := by
    simp [heisenbergNegative_apply, diagonalDerivative_coordinate,
      Algebra.smul_def, map_ofNat, add_comm, mul_comm]
  simpa only [one_div, Derivation.coeFn_coe] using normalized_pair (diagonalDerivative n).toLinearMap
    (heisenbergNegative n) (3:K) (by norm_num) h f

noncomputable def polynomialGrading : GradedSystem K (Space K) Mode where
  annihilate n := (diagonalDerivative n).toLinearMap
  create n := (1/3:K) • heisenbergNegative n
  weight := Subtype.val
  weight_pos := mode_pos
  weight_finite N := (Set.finite_Iic N).preimage (Set.injOn_of_injective Subtype.val_injective)
  grade := grade
  negative := grade_negative
  lower := diagonalDerivative_mem_grade
  raise n d f hf := by
    apply Submodule.smul_mem
    have hc := (diagonalCoordinate_mem_grade (K := K) n :
      MvPolynomial.IsWeightedHomogeneous variableWeight (diagonalCoordinate n) (n.val:ℤ))
    change MvPolynomial.IsWeightedHomogeneous variableWeight (diagonalCoordinate n * f) (d+n.val)
    simpa only [add_comm] using hc.mul hf
  pair := normalized_diagonal_pair
  positive_commute := diagonalDerivative_commute
  cross_commute i j hij f := by
    simp [LinearMap.smul_apply, heisenbergNegative_apply, map_smul,
      diagonalDerivative_coordinate, Ne.symm hij]

theorem polynomial_vacuum_eq (w : K) (hw : w^4-w^2+1=0) :
    vacuum (polynomialGrading (K := K)).annihilate = heisenbergVacuum w := by
  ext f
  rw [mem_vacuum, mem_heisenbergVacuum_iff_derivative w hw]
  rfl

theorem diagonalDerivative_mem_tensorCyclicSpan (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (n : Mode) (f : Space K) (hf : f ∈ tensorCyclicSpan w seed) :
    diagonalDerivative n f ∈ tensorCyclicSpan w seed := by
  have h := tensorCyclicSpan_algebra_mem w seed (heisenbergPositive w n)
    (heisenbergPositive_mem_tensorOperatorAlgebra w n) f hf
  have hs := (tensorCyclicSpan w seed).smul_mem
    (n.val * contraction w n.val / 12 : K)⁻¹ h
  simpa only [heisenbergPositive_apply, smul_smul,
    inv_mul_cancel₀ (heisenbergPositive_scale_ne_zero w hw n), one_smul] using hs

noncomputable def tensorCyclicGrading (w : K) (hw : w^4-w^2+1=0) (seed : Space K) :
    GradedSystem K (tensorCyclicSpan w seed) Mode :=
  polynomialGrading.restrict (tensorCyclicSpan w seed)
    (diagonalDerivative_mem_tensorCyclicSpan w hw seed)
    (fun n f hf => (tensorCyclicSpan w seed).smul_mem (1/3:K)
      (heisenbergNegative_mem_tensorCyclicSpan w seed n f hf))

theorem tensorCyclicGrading_vacuum (w : K) (hw : w^4-w^2+1=0) (seed : Space K) :
    vacuum (tensorCyclicGrading w hw seed).annihilate =
      (heisenbergVacuum w).comap (tensorCyclicSpan w seed).subtype := by
  rw [tensorCyclicGrading, GradedSystem.vacuum_restrict, polynomial_vacuum_eq w hw]

end KanadeRussell.Heisenberg
