import KanadeRussell.Tsuchioka.TensorCentralAnnihilationEuler

/-! Central annihilation residues for every lattice root. The normalized
Coxeter weight scales the already constructed first-root Heisenberg action. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (Lattice simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem tensor_root_polynomial_central_evaluation (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (j : Fin 3) (f : Space K) :
    polynomialPoleEvaluation (phaseUnit w hw 6)
      (tensorJointAnnihilationPolynomial w beta beta j j f) = HahnSeries.C f := by
  rw [polynomialPoleEvaluation_phaseUnit]
  have h := RingHom.congr_fun
    (poleEvaluation_tensorJoint_same w hw beta beta j 6) f
  simp only [RingHom.comp_apply, Nat.cast_ofNat] at h
  rw [h, RootData.coxeter_six, neg_add_cancel, tensorRootAnnihilation_zero]

noncomputable def tensorRootCentralAnnihilationEuler (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (j : Fin 3) (f : Space K) : LaurentSeries (Space K) :=
  polynomialPoleEvaluation (phaseUnit w hw 6)
    (polynomialEuler (tensorJointAnnihilationPolynomial w beta beta j j f))

theorem tensorRootCentralAnnihilationEuler_C (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (j : Fin 3) (c : K) : tensorRootCentralAnnihilationEuler w hw beta j (MvPolynomial.C c) = 0 := by
  simp only [tensorRootCentralAnnihilationEuler, tensorJointAnnihilationPolynomial,
    MvPolynomial.eval₂Hom_C, RingHom.comp_apply, polynomialEuler_C, map_zero]

theorem tensorRootCentralAnnihilationEuler_add (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (j : Fin 3) (f g : Space K) :
    tensorRootCentralAnnihilationEuler w hw beta j (f + g) =
      tensorRootCentralAnnihilationEuler w hw beta j f + tensorRootCentralAnnihilationEuler w hw beta j g := by
  simp only [tensorRootCentralAnnihilationEuler, map_add, polynomialEuler_add]

theorem tensorRootCentralAnnihilationEuler_mul (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (j : Fin 3) (f g : Space K) :
    tensorRootCentralAnnihilationEuler w hw beta j (f * g) =
      tensorRootCentralAnnihilationEuler w hw beta j f * HahnSeries.C g +
        HahnSeries.C f * tensorRootCentralAnnihilationEuler w hw beta j g := by
  simp only [tensorRootCentralAnnihilationEuler, map_mul, polynomialEuler_mul, map_add,
    tensor_root_polynomial_central_evaluation w hw beta]

theorem tensorRootCentralAnnihilationEuler_X (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (j : Fin 3) (s : Fin 3 × Mode) :
    tensorRootCentralAnnihilationEuler w hw beta j (MvPolynomial.X s) =
      HahnSeries.single (-(s.2.val : ℤ))
        (MvPolynomial.C (if s.1 = j then (s.2.val : K) * contraction w s.2.val * RootData.rootWeight (w ^ (s.2.val : ℤ)) beta else 0)) := by
  simp only [tensorRootCentralAnnihilationEuler, tensorJointAnnihilationPolynomial,
    MvPolynomial.eval₂Hom_X', RootData.rootWeight_first, mul_one,
    polynomialEuler_add, polynomialEuler_mul, polynomialEuler_C,
    polynomialEuler_X_zero_pow, polynomialEuler_X_one_pow,
    zero_mul, mul_zero, zero_add, add_zero]
  rw [polynomialPoleEvaluation_phaseUnit]
  simp only [map_mul, map_natCast, poleEvaluation, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', if_true, map_pow]
  have hp : (w ^ (6 : ℤ)) ^ s.2.val = (-1 : K) := by
    rw [← zpow_natCast, ← zpow_mul]
    have he : (6 : ℤ) * (s.2.val : ℤ) = -6 * (-(s.2.val : ℤ)) := by ring
    rw [he, root_six_neg_phase w hw, zpow_neg, zpow_natCast, (mode_odd s.2).neg_one_pow]
    simp
  rw [inverseVariable_pow]
  have hn : (s.2.val : LaurentSeries (Space K)) = HahnSeries.C (s.2.val : Space K) := by simp
  rw [hn, ← mul_assoc, ← map_mul, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add]
  simp only [← map_pow, hp]
  by_cases hs : s.1 = j
  · simp only [if_pos hs]
    congr 1
    simp only [← map_natCast MvPolynomial.C, ← map_mul]
    congr 1
    ring
  · simp [hs]

theorem sum_tensorRootCentralAnnihilationEuler_X (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (s : Fin 3 × Mode) :
    ∑ j : Fin 3, tensorRootCentralAnnihilationEuler w hw beta j (MvPolynomial.X s) =
      HahnSeries.single (-(s.2.val : ℤ)) (MvPolynomial.C ((s.2.val : K) * contraction w s.2.val * RootData.rootWeight (w ^ (s.2.val : ℤ)) beta)) := by
  simp only [tensorRootCentralAnnihilationEuler_X]
  rw [Finset.sum_eq_single s.1]
  · simp
  · intro j hj hjs
    simp [Ne.symm hjs]
  · simp

/-- The coefficient derivation determined by the actual oscillator shifts. -/
noncomputable def tensorRootAnnihilationEulerDerivation (w : K) (beta : Lattice) (d : ℤ) :
    Derivation K (Space K) (Space K) :=
  MvPolynomial.mkDerivation K fun s : Fin 3 × Mode =>
    (HahnSeries.single (-(s.2.val : ℤ))
      (MvPolynomial.C ((s.2.val : K) * contraction w s.2.val * RootData.rootWeight (w ^ (s.2.val : ℤ)) beta)) : LaurentSeries (Space K)).coeff d

theorem sum_tensorRootCentralAnnihilationEuler_coeff (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (f : Space K) (d : ℤ) :
    ∑ j : Fin 3, (tensorRootCentralAnnihilationEuler w hw beta j f).coeff d =
      tensorRootAnnihilationEulerDerivation w beta d f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [tensorRootCentralAnnihilationEuler_C, MvPolynomial.derivation_C]
  | add f g hf hg =>
    simp only [tensorRootCentralAnnihilationEuler_add, HahnSeries.coeff_add,
      Finset.sum_add_distrib, hf, hg, map_add]
  | mul_X f s hf =>
    have hx : (∑ j : Fin 3, (tensorRootCentralAnnihilationEuler w hw beta j (MvPolynomial.X s)).coeff d) =
        tensorRootAnnihilationEulerDerivation w beta d (MvPolynomial.X s) := by
      rw [← HahnSeries.coeff_sum, sum_tensorRootCentralAnnihilationEuler_X]
      simp [tensorRootAnnihilationEulerDerivation]
    simp only [tensorRootCentralAnnihilationEuler_mul, HahnSeries.coeff_add,
      HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero,
      HahnSeries.coeff_single_zero_mul, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hf, hx, Derivation.leibniz, smul_eq_mul]
    ring

theorem tensorRootAnnihilationEulerDerivation_eq (w : K) (beta : Lattice) (d : ℤ) :
    tensorRootAnnihilationEulerDerivation w beta d =
      RootData.rootWeight (w ^ (-d)) beta • tensorAnnihilationEulerDerivation w d := by
  apply MvPolynomial.derivation_ext
  intro s
  simp only [tensorRootAnnihilationEulerDerivation, tensorAnnihilationEulerDerivation,
    MvPolynomial.mkDerivation_X, Derivation.smul_apply, HahnSeries.coeff_single]
  by_cases hd : d = -(s.2.val : ℤ)
  · simp only [hd, if_true, neg_neg, MvPolynomial.C_eq_smul_one, smul_smul]
    congr 1
    ring
  · simp only [if_neg hd, smul_zero]

theorem sum_tensorRootCentralAnnihilationEuler_eq (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (beta : Lattice) (f : Space K) (d : ℤ) :
    ∑ j : Fin 3, (tensorRootCentralAnnihilationEuler w hw beta j f).coeff d =
      RootData.rootWeight (w ^ (-d)) beta •
        ∑ j : Fin 3, (tensorCentralAnnihilationEuler w hw j f).coeff d := by
  rw [sum_tensorRootCentralAnnihilationEuler_coeff, tensorRootAnnihilationEulerDerivation_eq,
    sum_tensorCentralAnnihilationEuler_coeff, Derivation.smul_apply]

end KanadeRussell.Tsuchioka.Fock
