import KanadeRussell.Tsuchioka.TensorCentralAnnihilationEuler

/-! The tensor creation contribution at the central pole equals the
negative Heisenberg action, with its source sign and factor twelve. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (Lattice simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem laurentEuler_tensorRootCreation (w : K) (β : Lattice) (j : Fin 3) :
    laurentEuler (tensorRootCreation w β j : LaurentSeries (Space K)) =
      (tensorRootCreation w β j : LaurentSeries (Space K)) *
        laurentEuler (tensorRootCreationLog w β j : LaurentSeries (Space K)) := by
  rw [laurentEuler_powerSeries, laurentEuler_powerSeries]
  change ((PowerSeries.X * PowerSeries.derivative (Space K)
      (exponential (tensorRootCreationLog w β j)) : PowerSeries (Space K)) : LaurentSeries (Space K)) = _
  rw [derivative_exponential (constantCoeff_tensorRootCreationLog w β j)]
  rw [← PowerSeries.coe_mul]
  congr 1
  change PowerSeries.X * (exponential (tensorRootCreationLog w β j) *
      PowerSeries.derivative (Space K) (tensorRootCreationLog w β j)) =
    exponential (tensorRootCreationLog w β j) *
      (PowerSeries.X * PowerSeries.derivative (Space K) (tensorRootCreationLog w β j))
  ring

theorem tensorCreation_central_fusion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) :
    laurentRescale (phaseUnit w hw 6) (tensorRootCreation w β j : LaurentSeries (Space K)) *
      (tensorRootCreation w β j : LaurentSeries (Space K)) = 1 := by
  have h := tensorPoleNormalProduct_six w hw β j (1 : Space K)
  simpa only [map_one, mul_one] using h

theorem tensorCreation_central_euler (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) :
    laurentRescale (phaseUnit w hw 6)
        (laurentEuler (tensorRootCreation w β j : LaurentSeries (Space K))) *
      (tensorRootCreation w β j : LaurentSeries (Space K)) =
      laurentRescale (phaseUnit w hw 6)
        (laurentEuler (tensorRootCreationLog w β j : LaurentSeries (Space K))) := by
  rw [laurentEuler_tensorRootCreation, map_mul]
  calc
    _ = laurentRescale (phaseUnit w hw 6)
        (laurentEuler (tensorRootCreationLog w β j : LaurentSeries (Space K))) *
        (laurentRescale (phaseUnit w hw 6) (tensorRootCreation w β j : LaurentSeries (Space K)) *
          tensorRootCreation w β j) := by ring
    _ = _ := by rw [tensorCreation_central_fusion w hw, mul_one]

theorem tensorCreation_central_euler_coeff_mode (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (j : Fin 3) (n : Mode) :
    (laurentRescale (phaseUnit w hw 6)
        (laurentEuler (tensorRootCreation w (simpleRoot 0) j : LaurentSeries (Space K))) *
      (tensorRootCreation w (simpleRoot 0) j : LaurentSeries (Space K))).coeff n.val =
      (-12 : K) • MvPolynomial.X (j, n) := by
  rw [tensorCreation_central_euler, coeff_laurentRescale, coeff_laurentEuler,
    LaurentSeries.coeff_coe_powerSeries, tensorRootCreationLog, PowerSeries.coeff_mk,
    dif_pos n.property, RootData.rootWeight_first, mul_one, phaseUnit_zpow,
    root_six_neg_phase w hw, zpow_natCast, (mode_odd n).neg_one_pow]
  have hn : (n.val : K) ≠ 0 := by exact_mod_cast ne_of_gt (mode_pos n)
  have hc : (-1 : K) * (n.val : K) * (12 / (n.val : K)) = -12 := by field_simp
  have hnC : ((n.val : ℤ) : Space K) = MvPolynomial.C (n.val : K) := by simp
  rw [hnC]
  simp only [MvPolynomial.C_mul', smul_smul, ← mul_assoc, hc]

theorem tensorCreation_central_euler_coeff_nonpositive (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (β : Lattice) (j : Fin 3) (d : ℤ) (hd : d ≤ 0) :
    (laurentRescale (phaseUnit w hw 6)
        (laurentEuler (tensorRootCreation w β j : LaurentSeries (Space K))) *
      (tensorRootCreation w β j : LaurentSeries (Space K))).coeff d = 0 := by
  rw [tensorCreation_central_euler, coeff_laurentRescale, coeff_laurentEuler]
  rcases lt_or_eq_of_le hd with hd | rfl
  · rw [PowerSeries.coeff_coe, if_pos hd, mul_zero, mul_zero]
  · simp

theorem tensorCreation_central_euler_coeff_not_mode (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (β : Lattice) (j : Fin 3) (n : ℕ) (hn : ¬IsMode n) :
    (laurentRescale (phaseUnit w hw 6)
        (laurentEuler (tensorRootCreation w β j : LaurentSeries (Space K))) *
      (tensorRootCreation w β j : LaurentSeries (Space K))).coeff n = 0 := by
  rw [tensorCreation_central_euler, coeff_laurentRescale, coeff_laurentEuler,
    LaurentSeries.coeff_coe_powerSeries, tensorRootCreationLog, PowerSeries.coeff_mk,
    dif_neg hn, mul_zero, mul_zero]

theorem sum_tensorCreation_central_euler_heisenberg (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : Mode) (f : Space K) :
    ∑ j : Fin 3,
      (laurentRescale (phaseUnit w hw 6)
          (laurentEuler (tensorRootCreation w (simpleRoot 0) j : LaurentSeries (Space K))) *
        (tensorRootCreation w (simpleRoot 0) j : LaurentSeries (Space K)) * HahnSeries.C f).coeff n.val =
      (-12 : K) • heisenbergNegative n f := by
  simp only [HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero,
    tensorCreation_central_euler_coeff_mode]
  rw [← Finset.sum_mul, ← Finset.smul_sum]
  change ((-12 : K) • diagonalCoordinate n) * f = (-12 : K) • (diagonalCoordinate n * f)
  exact smul_mul_assoc _ _ _

end KanadeRussell.Tsuchioka.Fock
