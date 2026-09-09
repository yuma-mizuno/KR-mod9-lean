import KanadeRussell.Tsuchioka.EulerDiagonal
import KanadeRussell.Tsuchioka.NormalProductEvaluation
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Differentiating the finite inverse-variable polynomial in the normal product. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

variable {A : Type*} [CommRing A]

/-- Euler derivative in the first inverse variable. -/
noncomputable def polynomialEuler (p : MvPolynomial (Fin 2) A) : MvPolynomial (Fin 2) A :=
  MvPolynomial.X 0 * MvPolynomial.pderiv 0 p

@[simp] theorem polynomialEuler_C (c : A) :
    polynomialEuler (MvPolynomial.C c) = 0 := by
  simp [polynomialEuler, MvPolynomial.pderiv_C]

theorem polynomialEuler_add (p q : MvPolynomial (Fin 2) A) :
    polynomialEuler (p + q) = polynomialEuler p + polynomialEuler q := by
  simp only [polynomialEuler, map_add, mul_add]

theorem polynomialEuler_mul (p q : MvPolynomial (Fin 2) A) :
    polynomialEuler (p * q) = polynomialEuler p * q + p * polynomialEuler q := by
  simp only [polynomialEuler, MvPolynomial.pderiv_mul]
  ring

@[simp] theorem polynomialEuler_X_zero :
    polynomialEuler (MvPolynomial.X 0 : MvPolynomial (Fin 2) A) = MvPolynomial.X 0 := by
  simp [polynomialEuler]

@[simp] theorem polynomialEuler_X_one :
    polynomialEuler (MvPolynomial.X 1 : MvPolynomial (Fin 2) A) = 0 := by
  simp [polynomialEuler, MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]

theorem polynomialEuler_X_zero_pow (n : ℕ) :
    polynomialEuler (MvPolynomial.X 0 ^ n : MvPolynomial (Fin 2) A) =
      (n : MvPolynomial (Fin 2) A) * MvPolynomial.X 0 ^ n := by
  induction n with
  | zero => simp [polynomialEuler, MvPolynomial.pderiv_one]
  | succ n hn =>
    rw [pow_succ, polynomialEuler_mul, hn, polynomialEuler_X_zero]
    push_cast
    ring

theorem polynomialEuler_X_one_pow (n : ℕ) :
    polynomialEuler (MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) A) = 0 := by
  induction n with
  | zero => simp [polynomialEuler, MvPolynomial.pderiv_one]
  | succ n hn => simp [pow_succ, polynomialEuler_mul, hn]

end KanadeRussell.Tsuchioka.FormalSeries

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

/-- The inner Euler derivative includes a negative derivative in the inverse
variable. Both terms are evaluated on the finite normal-product polynomial. -/
theorem normalWithPolynomial_euler (u : (Space K)ˣ)
    (f g : LaurentSeries (Space K)) (p : MvPolynomial (Fin 2) (Space K)) (d : ℤ) :
    diagonalEulerCoefficient u (normalWithPolynomial f g p) d =
      (laurentRescale u (laurentEuler f) * g * polynomialPoleEvaluation u p).coeff d -
        (laurentRescale u f * g * polynomialPoleEvaluation u (polynomialEuler p)).coeff d := by
  induction p using MvPolynomial.induction_on generalizing d with
  | C c =>
    rw [normalWithPolynomial, jointLaurentEmbedding, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply, HahnSeries.C_apply, HahnSeries.C_apply,
      mul_comm (separated f g), diagonalEulerCoefficient_single_mul (separated_bounded f g),
      diagonalEulerCoefficient_separated]
    simp only [zpow_zero, Units.val_one, one_mul, sub_zero, Int.cast_zero, zero_mul,
      add_zero, polynomialEuler_C, map_zero, mul_zero, HahnSeries.coeff_zero,
      polynomialPoleEvaluation, MvPolynomial.eval₂Hom_C, HahnSeries.C_apply,
      HahnSeries.coeff_mul_single_zero]
    ring
  | add p q hp hq =>
    obtain ⟨l, r, hb⟩ := normalWithPolynomial_bounded f g p
    obtain ⟨l', r', hc⟩ := normalWithPolynomial_bounded f g q
    rw [normalWithPolynomial_add, diagonalEulerCoefficient_add hb hc, hp, hq,
      polynomialEuler_add]
    simp only [map_add, mul_add, HahnSeries.coeff_add]
    ring
  | mul_X p v hp =>
    obtain ⟨l, r, hb⟩ := normalWithPolynomial_bounded f g p
    have hmul : normalWithPolynomial f g (p * MvPolynomial.X v) =
        jointLaurentEmbedding (MvPolynomial.X v : MvPolynomial (Fin 2) (Space K)) *
          normalWithPolynomial f g p := by
      simp only [normalWithPolynomial, map_mul]
      ring
    rw [hmul, polynomialEuler_mul]
    by_cases hv : v = 0
    · subst v
      simp only [polynomialEuler_X_zero, map_add, map_mul]
      simp only [jointLaurentEmbedding, MvPolynomial.eval₂Hom_X', ite_true,
        HahnSeries.C_apply]
      rw [diagonalEulerCoefficient_single_mul hb, hp, normalWithPolynomial_diagonal]
      simp only [sub_neg_eq_add, sub_zero, zpow_neg_one, mul_one, Int.cast_neg, Int.cast_one,
        polynomialPoleEvaluation, MvPolynomial.eval₂Hom_X', ite_true, HahnSeries.C_apply,
        mul_add, ← mul_assoc, HahnSeries.coeff_mul_single, HahnSeries.coeff_add]
      ring
    · have hv1 : v = 1 := by fin_cases v <;> simp_all
      subst v
      simp only [polynomialEuler_X_one, mul_zero, add_zero, map_mul]
      simp only [jointLaurentEmbedding, MvPolynomial.eval₂Hom_X',
        if_neg (by decide : (1 : Fin 2) ≠ 0), HahnSeries.C_apply]
      rw [diagonalEulerCoefficient_single_mul hb, hp]
      simp only [sub_neg_eq_add, sub_zero, zpow_zero, Units.val_one, one_mul, mul_one,
        Int.cast_zero, zero_mul, add_zero, polynomialPoleEvaluation, MvPolynomial.eval₂Hom_X',
        if_neg (by decide : (1 : Fin 2) ≠ 0), ← mul_assoc, HahnSeries.coeff_mul_single,
        HahnSeries.coeff_add, mul_one]

end KanadeRussell.Tsuchioka.Fock
