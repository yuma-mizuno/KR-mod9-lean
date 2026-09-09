import KanadeRussell.Tsuchioka.TensorCovariance
import KanadeRussell.Tsuchioka.TensorJointAnnihilation

/-! Full tensor pole fusion, including the finite annihilation polynomial.
The same-position normal product at a Coxeter phase becomes the tensor
field of the sum of the two roots. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open PowerSeries FormalSeries
open RootData (Lattice simpleRoot coxeter rootWeight)

variable {K : Type*} [Field K] [CharZero K]

theorem poleEvaluation_tensorJoint_same (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β γ : Lattice) (j : Fin 3) (p : ℕ) :
    (poleEvaluation w p).comp (tensorJointAnnihilationPolynomial w β γ j j) =
      tensorRootAnnihilation w ((coxeter^[p]) β + γ) j := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, tensorJointAnnihilationPolynomial, tensorRootAnnihilation,
      poleEvaluation, MvPolynomial.eval₂Hom_C]
  · intro s
    simp only [RingHom.comp_apply, tensorJointAnnihilationPolynomial, MvPolynomial.eval₂Hom_X',
      poleEvaluation, map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', ite_true, if_neg (by decide : (1 : Fin 2) ≠ 0),
      tensorRootAnnihilation]
    have he : (HahnSeries.single (-1) (1 : Space K) : LaurentSeries (Space K)) =
        HahnSeries.single (-1) (MvPolynomial.C (1 : K)) := by simp
    rw [scalar_inverseVariable_mul, he, scalar_inverseVariable_mul]
    simp only [one_pow, mul_one]
    rw [add_assoc, ← HahnSeries.single_add, ← map_add]
    have ht : (w ^ (s.2.val : ℤ)) ^ 4 - (w ^ (s.2.val : ℤ)) ^ 2 + 1 = 0 := by
      simpa only [zpow_natCast] using mode_cyclotomic w hw s.2
    have hp : (w ^ (s.2.val : ℤ)) ^ p = (w ^ (p : ℤ)) ^ s.2.val := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
      congr 1
      ring
    rw [RootData.rootWeight_add, RootData.rootWeight_iterate _ ht, hp]
    by_cases hs : s.1 = j
    · simp only [if_pos hs]
      congr 2
      ring
    · simp [hs]

/-- The whole normal expression at the pole fuses, not just its creation part. -/
theorem tensorPoleNormalProduct_same (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β γ : Lattice) (j : Fin 3) (p : ℕ) (f : Space K) :
    laurentRescale (phaseUnit w hw p) (tensorRootCreation w β j : LaurentSeries (Space K)) *
        (tensorRootCreation w γ j : LaurentSeries (Space K)) *
          poleEvaluation w p (tensorJointAnnihilationPolynomial w β γ j j f) =
      tensorRootSummand w ((coxeter^[p]) β + γ) j f := by
  have h := RingHom.congr_fun (poleEvaluation_tensorJoint_same w hw β γ j p) f
  simp only [RingHom.comp_apply] at h
  change laurentRescale _ (tensorRootCreation w β j : LaurentSeries (Space K)) *
    (tensorRootCreation w γ j : LaurentSeries (Space K)) *
      poleEvaluation w p (tensorJointAnnihilationPolynomial w β γ j j f) =
    (tensorRootCreation w ((coxeter^[p]) β + γ) j : LaurentSeries (Space K)) *
      tensorRootAnnihilation w ((coxeter^[p]) β + γ) j f
  rw [h, tensorRootCreation_add, tensorRootCreation_iterate w hw,
    FormalSeries.laurentRescale_powerSeries, phaseUnit_val, map_mul]

theorem tensorNormalProduct_diagonal_same (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β γ : Lattice) (j : Fin 3) (f : Space K) (p : ℕ) (d : ℤ) :
    diagonalCoefficient (phaseUnit w hw p) (tensorNormalProduct w β γ j j f) d =
      (tensorRootSummand w ((coxeter^[p]) β + γ) j f).coeff d := by
  rw [tensorNormalProduct_diagonal, polynomialPoleEvaluation_phaseUnit,
    tensorPoleNormalProduct_same]

theorem tensorNormalProduct_delta_contraction_same (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (β γ : Lattice) (j : Fin 3)
    (f : Space K) (p : ℕ) (a b : ℤ) :
    contract (fun n => ((phaseUnit w hw p ^ n : (Space K)ˣ) : Space K))
        (tensorNormalProduct w β γ j j f) a b =
      MvPolynomial.C (w ^ ((p : ℤ) * a)) *
        (tensorRootSummand w ((coxeter^[p]) β + γ) j f).coeff (a + b) := by
  obtain ⟨l, r, h⟩ := tensorNormalProduct_bounded w β γ j j f
  rw [contract_delta h, tensorNormalProduct_diagonal_same, phaseUnit_zpow]
  simp only [neg_mul_neg]

/-- The central-pole normal expression is the identity; its Euler derivative
is a separate term and is not asserted to vanish. -/
theorem tensorPoleNormalProduct_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (f : Space K) :
    laurentRescale (phaseUnit w hw 6) (tensorRootCreation w β j : LaurentSeries (Space K)) *
        (tensorRootCreation w β j : LaurentSeries (Space K)) *
          poleEvaluation w 6 (tensorJointAnnihilationPolynomial w β β j j f) = HahnSeries.C f := by
  rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, tensorPoleNormalProduct_same,
    RootData.coxeter_six, neg_add_cancel, tensorRootSummand_zero]

theorem tensorNormalProduct_diagonal_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (f : Space K) (d : ℤ) :
    diagonalCoefficient (phaseUnit w hw 6) (tensorNormalProduct w β β j j f) d =
      (HahnSeries.C f).coeff d := by
  rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, tensorNormalProduct_diagonal_same,
    RootData.coxeter_six, neg_add_cancel, tensorRootSummand_zero]

end KanadeRussell.Tsuchioka.Fock
