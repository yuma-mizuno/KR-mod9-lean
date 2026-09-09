import KanadeRussell.Tsuchioka.EulerPolynomial

/-! Cancellation of the finite annihilation derivative at the central pole. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem polynomial_central_evaluation (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) :
    polynomialPoleEvaluation (phaseUnit w hw 6)
      (jointAnnihilationPolynomial w (simpleRoot 0) (simpleRoot 0) j j f) = HahnSeries.C f := by
  rw [polynomialPoleEvaluation_phaseUnit]
  have h := RingHom.congr_fun
    (poleEvaluation_jointAnnihilation w (simpleRoot 0) (simpleRoot 0) j j 6) f
  simp only [RingHom.comp_apply] at h
  rw [h, show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, poleAnnihilation_same w hw,
    RootData.coxeter_six, neg_add_cancel, rootAnnihilation_zero]

/-- The first inverse-variable Euler derivative, evaluated at the central pole. -/
noncomputable def centralAnnihilationEuler (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) : LaurentSeries (Space K) :=
  polynomialPoleEvaluation (phaseUnit w hw 6)
    (polynomialEuler (jointAnnihilationPolynomial w (simpleRoot 0) (simpleRoot 0) j j f))

theorem centralAnnihilationEuler_C (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (c : K) :
    centralAnnihilationEuler w hw j (MvPolynomial.C c) = 0 := by
  simp only [centralAnnihilationEuler, jointAnnihilationPolynomial, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, polynomialEuler_C, map_zero]

theorem centralAnnihilationEuler_add (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f g : Space K) :
    centralAnnihilationEuler w hw j (f + g) =
      centralAnnihilationEuler w hw j f + centralAnnihilationEuler w hw j g := by
  simp only [centralAnnihilationEuler, map_add, polynomialEuler_add]

theorem centralAnnihilationEuler_mul (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f g : Space K) :
    centralAnnihilationEuler w hw j (f * g) =
      centralAnnihilationEuler w hw j f * HahnSeries.C g +
        HahnSeries.C f * centralAnnihilationEuler w hw j g := by
  simp only [centralAnnihilationEuler, map_mul, polynomialEuler_mul, map_add,
    polynomial_central_evaluation w hw]

theorem sum_centralAnnihilationEuler_X (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (s : Fin 3 × Mode) :
    ∑ j : Fin 3, centralAnnihilationEuler w hw j (MvPolynomial.X s) = 0 := by
  unfold centralAnnihilationEuler
  rw [← map_sum]
  have hs : ∑ j : Fin 3, tensorExponent (K := K) s.1 j * contraction w s.2.val / 3 = 0 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, sum_tensorExponent, zero_mul]
  have he : ∑ j : Fin 3,
      polynomialEuler (jointAnnihilationPolynomial w (simpleRoot 0) (simpleRoot 0) j j
        (MvPolynomial.X s)) = 0 := by
    simp only [jointAnnihilationPolynomial, MvPolynomial.eval₂Hom_X',
      RootData.rootWeight_first, mul_one, polynomialEuler_add, polynomialEuler_mul,
      polynomialEuler_C, polynomialEuler_X_zero_pow, polynomialEuler_X_one_pow,
      zero_mul, mul_zero, zero_add, add_zero]
    rw [← Finset.sum_mul, ← map_sum, ← map_sum, hs, map_zero, map_zero, zero_mul]
  rw [he, map_zero]

/-- Cancellation holds on every input polynomial, by the product rule and the
vanishing of the summed derivative on each generator. -/
theorem sum_centralAnnihilationEuler (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) :
    ∑ j : Fin 3, centralAnnihilationEuler w hw j f = 0 := by
  induction f using MvPolynomial.induction_on with
  | C c => simp only [centralAnnihilationEuler_C, Finset.sum_const_zero]
  | add f g hf hg =>
    simp only [centralAnnihilationEuler_add, Finset.sum_add_distrib, hf, hg, add_zero]
  | mul_X f s hf =>
    simp only [centralAnnihilationEuler_mul, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hf, sum_centralAnnihilationEuler_X w hw,
      zero_mul, mul_zero, add_zero]

end KanadeRussell.Tsuchioka.Fock
