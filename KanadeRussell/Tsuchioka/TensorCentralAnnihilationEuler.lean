import KanadeRussell.Tsuchioka.TensorPoleFusion
import KanadeRussell.Tsuchioka.EulerPolynomial
import KanadeRussell.Tsuchioka.CentralDelta

/-! The annihilation contribution at the tensor central pole. It is a
nonzero Heisenberg derivation; no cancellation of this tensor term is assumed. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem mode_odd (n : Mode) : Odd n.val := by
  rw [Nat.odd_iff]
  rcases n.property with h | h | h | h <;> omega

theorem tensor_polynomial_central_evaluation (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) :
    polynomialPoleEvaluation (phaseUnit w hw 6)
      (tensorJointAnnihilationPolynomial w (simpleRoot 0) (simpleRoot 0) j j f) = HahnSeries.C f := by
  rw [polynomialPoleEvaluation_phaseUnit]
  have h := RingHom.congr_fun
    (poleEvaluation_tensorJoint_same w hw (simpleRoot 0) (simpleRoot 0) j 6) f
  simp only [RingHom.comp_apply, Nat.cast_ofNat] at h
  rw [h, RootData.coxeter_six, neg_add_cancel, tensorRootAnnihilation_zero]

noncomputable def tensorCentralAnnihilationEuler (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) : LaurentSeries (Space K) :=
  polynomialPoleEvaluation (phaseUnit w hw 6)
    (polynomialEuler (tensorJointAnnihilationPolynomial w (simpleRoot 0) (simpleRoot 0) j j f))

theorem tensorCentralAnnihilationEuler_C (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (c : K) : tensorCentralAnnihilationEuler w hw j (MvPolynomial.C c) = 0 := by
  simp only [tensorCentralAnnihilationEuler, tensorJointAnnihilationPolynomial,
    MvPolynomial.eval₂Hom_C, RingHom.comp_apply, polynomialEuler_C, map_zero]

theorem tensorCentralAnnihilationEuler_add (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f g : Space K) :
    tensorCentralAnnihilationEuler w hw j (f + g) =
      tensorCentralAnnihilationEuler w hw j f + tensorCentralAnnihilationEuler w hw j g := by
  simp only [tensorCentralAnnihilationEuler, map_add, polynomialEuler_add]

theorem tensorCentralAnnihilationEuler_mul (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f g : Space K) :
    tensorCentralAnnihilationEuler w hw j (f * g) =
      tensorCentralAnnihilationEuler w hw j f * HahnSeries.C g +
        HahnSeries.C f * tensorCentralAnnihilationEuler w hw j g := by
  simp only [tensorCentralAnnihilationEuler, map_mul, polynomialEuler_mul, map_add,
    tensor_polynomial_central_evaluation w hw]

theorem tensorCentralAnnihilationEuler_X (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (s : Fin 3 × Mode) :
    tensorCentralAnnihilationEuler w hw j (MvPolynomial.X s) =
      HahnSeries.single (-(s.2.val : ℤ))
        (MvPolynomial.C (if s.1 = j then (s.2.val : K) * contraction w s.2.val else 0)) := by
  simp only [tensorCentralAnnihilationEuler, tensorJointAnnihilationPolynomial,
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

theorem sum_tensorCentralAnnihilationEuler_X (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (s : Fin 3 × Mode) :
    ∑ j : Fin 3, tensorCentralAnnihilationEuler w hw j (MvPolynomial.X s) =
      HahnSeries.single (-(s.2.val : ℤ)) (MvPolynomial.C ((s.2.val : K) * contraction w s.2.val)) := by
  simp only [tensorCentralAnnihilationEuler_X]
  rw [Finset.sum_eq_single s.1]
  · simp
  · intro j hj hjs
    simp [Ne.symm hjs]
  · simp

/-- The coefficient derivation determined by the actual oscillator shifts. -/
noncomputable def tensorAnnihilationEulerDerivation (w : K) (d : ℤ) :
    Derivation K (Space K) (Space K) :=
  MvPolynomial.mkDerivation K fun s : Fin 3 × Mode =>
    (HahnSeries.single (-(s.2.val : ℤ))
      (MvPolynomial.C ((s.2.val : K) * contraction w s.2.val)) : LaurentSeries (Space K)).coeff d

theorem sum_tensorCentralAnnihilationEuler_coeff (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (d : ℤ) :
    ∑ j : Fin 3, (tensorCentralAnnihilationEuler w hw j f).coeff d =
      tensorAnnihilationEulerDerivation w d f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [tensorCentralAnnihilationEuler_C, MvPolynomial.derivation_C]
  | add f g hf hg =>
    simp only [tensorCentralAnnihilationEuler_add, HahnSeries.coeff_add,
      Finset.sum_add_distrib, hf, hg, map_add]
  | mul_X f s hf =>
    have hx : (∑ j : Fin 3, (tensorCentralAnnihilationEuler w hw j (MvPolynomial.X s)).coeff d) =
        tensorAnnihilationEulerDerivation w d (MvPolynomial.X s) := by
      rw [← HahnSeries.coeff_sum, sum_tensorCentralAnnihilationEuler_X]
      simp [tensorAnnihilationEulerDerivation]
    simp only [tensorCentralAnnihilationEuler_mul, HahnSeries.coeff_add,
      HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero,
      HahnSeries.coeff_single_zero_mul, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hf, hx, Derivation.leibniz, smul_eq_mul]
    ring

theorem tensorAnnihilationEulerDerivation_negative (w : K) (n : Mode) :
    tensorAnnihilationEulerDerivation w (-(n.val : ℤ)) =
      ((n.val : K) * contraction w n.val) • diagonalDerivative n := by
  apply MvPolynomial.derivation_ext
  intro s
  simp only [tensorAnnihilationEulerDerivation, MvPolynomial.mkDerivation_X,
    Derivation.smul_apply, diagonalDerivative_X, HahnSeries.coeff_single]
  by_cases hs : s.2 = n
  · simp [hs, MvPolynomial.C_eq_smul_one]
  · have hv : (-(n.val : ℤ)) ≠ -(s.2.val : ℤ) := by
      intro h
      apply hs
      apply Subtype.ext
      exact_mod_cast (neg_injective h).symm
    simp [hs, hv]

theorem tensorAnnihilationEulerDerivation_nonnegative (w : K) (d : ℤ) (hd : 0 ≤ d) :
    tensorAnnihilationEulerDerivation w d = 0 := by
  apply MvPolynomial.derivation_ext
  intro s
  have hne : d ≠ -(s.2.val : ℤ) := by have hp := mode_pos s.2; omega
  simp [tensorAnnihilationEulerDerivation, HahnSeries.coeff_single, hne]

/-- The summed tensor annihilation Euler coefficient is exactly twelve
times the positive Heisenberg action, at every allowed mode. -/
theorem sum_tensorCentralAnnihilationEuler_heisenberg (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : Mode) (f : Space K) :
    ∑ j : Fin 3, (tensorCentralAnnihilationEuler w hw j f).coeff (-(n.val : ℤ)) =
      (12 : K) • heisenbergPositive w n f := by
  rw [sum_tensorCentralAnnihilationEuler_coeff, tensorAnnihilationEulerDerivation_negative]
  simp only [Derivation.smul_apply, heisenbergPositive_apply, smul_smul]
  congr 1
  ring

end KanadeRussell.Tsuchioka.Fock
