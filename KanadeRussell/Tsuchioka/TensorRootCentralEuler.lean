import KanadeRussell.Tsuchioka.TensorRootCentralAnnihilation
import KanadeRussell.Tsuchioka.TensorCentralEuler

/-! The central Euler residue for every tensor root. Both the creation
and annihilation terms scale by the same Coxeter weight in each degree. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (Lattice simpleRoot rootWeight)

variable {K : Type*} [Field K] [CharZero K]

theorem coeff_tensorRootCreationLog_weight (w : K) (beta : Lattice)
    (j : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (tensorRootCreationLog w beta j) =
      rootWeight (w ^ (-(n : ℤ))) beta •
        PowerSeries.coeff n (tensorRootCreationLog w (simpleRoot 0) j) := by
  simp only [tensorRootCreationLog, PowerSeries.coeff_mk]
  by_cases hn : IsMode n
  · simp only [dif_pos hn, RootData.rootWeight_first, mul_one,
      MvPolynomial.C_mul', smul_smul]
    congr 1
    ring
  · simp [hn]

theorem laurent_coeff_tensorRootCreationLog_weight (w : K) (beta : Lattice)
    (j : Fin 3) (d : ℤ) :
    (tensorRootCreationLog w beta j : LaurentSeries (Space K)).coeff d =
      rootWeight (w ^ (-d)) beta •
        (tensorRootCreationLog w (simpleRoot 0) j : LaurentSeries (Space K)).coeff d := by
  cases d with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, LaurentSeries.coeff_coe_powerSeries] using
      coeff_tensorRootCreationLog_weight w beta j n
  | negSucc n =>
    have hd : Int.negSucc n < 0 := by omega
    simp [PowerSeries.coeff_coe, hd]

theorem tensorCreation_central_euler_coeff_weight (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (beta : Lattice) (j : Fin 3) (d : ℤ) :
    (laurentRescale (phaseUnit w hw 6)
        (laurentEuler (tensorRootCreation w beta j : LaurentSeries (Space K))) *
      (tensorRootCreation w beta j : LaurentSeries (Space K))).coeff d =
      rootWeight (w ^ (-d)) beta •
        (laurentRescale (phaseUnit w hw 6)
          (laurentEuler (tensorRootCreation w (simpleRoot 0) j : LaurentSeries (Space K))) *
          (tensorRootCreation w (simpleRoot 0) j : LaurentSeries (Space K))).coeff d := by
  rw [tensorCreation_central_euler w hw, tensorCreation_central_euler w hw]
  simp only [coeff_laurentRescale, coeff_laurentEuler,
    laurent_coeff_tensorRootCreationLog_weight w beta]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring

theorem tensorNormalProduct_root_central_euler (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (beta : Lattice)
    (j : Fin 3) (f : Space K) (d : ℤ) :
    diagonalEulerCoefficient (phaseUnit w hw 6)
        (tensorNormalProduct w beta beta j j f) d =
      (laurentRescale (phaseUnit w hw 6)
          (laurentEuler (tensorRootCreation w beta j : LaurentSeries (Space K))) *
        (tensorRootCreation w beta j : LaurentSeries (Space K)) * HahnSeries.C f).coeff d -
      (tensorRootCentralAnnihilationEuler w hw beta j f).coeff d := by
  rw [tensorNormalProduct_eq_normalWithPolynomial, normalWithPolynomial_euler,
    tensor_root_polynomial_central_evaluation w hw,
    tensorCreation_central_fusion w hw, one_mul]
  rfl

theorem sum_tensorNormalProduct_central_euler_weight (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (beta : Lattice) (f : Space K) (d : ℤ) :
    (∑ j : Fin 3, diagonalEulerCoefficient (phaseUnit w hw 6)
      (tensorNormalProduct w beta beta j j f) d) =
      rootWeight (w ^ (-d)) beta • ∑ j : Fin 3,
        diagonalEulerCoefficient (phaseUnit w hw 6)
          (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) j j f) d := by
  simp only [tensorNormalProduct_root_central_euler w hw beta,
    tensorNormalProduct_central_euler w hw, Finset.sum_sub_distrib,
    HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero,
    tensorCreation_central_euler_coeff_weight w hw beta,
    sum_tensorRootCentralAnnihilationEuler_eq w hw beta,
    smul_mul_assoc, ← Finset.smul_sum, smul_sub]

/-- The central derivative is -12 times the root's projected Heisenberg
mode, including both signs and all absent oscillator degrees. -/
theorem sum_tensorNormalProduct_root_central_euler (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (beta : Lattice) (f : Space K) (d : ℤ) :
    (∑ j : Fin 3, diagonalEulerCoefficient (phaseUnit w hw 6)
      (tensorNormalProduct w beta beta j j f) d) =
      (-12 * rootWeight (w ^ (-d)) beta) • heisenbergMode w (-d) f := by
  rw [sum_tensorNormalProduct_central_euler_weight w hw,
    sum_tensorNormalProduct_central_euler w hw, smul_smul]
  congr 1
  ring

end KanadeRussell.Tsuchioka.Fock
