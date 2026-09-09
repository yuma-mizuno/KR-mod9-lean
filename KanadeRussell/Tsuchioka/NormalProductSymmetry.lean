import KanadeRussell.Tsuchioka.NormalProductEvaluation

/-! Coefficientwise exchange of the two variables of the common normal product. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (Lattice simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

noncomputable def swapInverseVariables :
    MvPolynomial (Fin 2) (Space K) →+* MvPolynomial (Fin 2) (Space K) :=
  (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)).toRingHom

@[simp] theorem swapInverseVariables_C (c : Space K) :
    swapInverseVariables (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [swapInverseVariables, MvPolynomial.rename_C]

@[simp] theorem swapInverseVariables_X_zero :
    swapInverseVariables (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) (Space K)) =
      MvPolynomial.X 1 := by
  simp [swapInverseVariables, MvPolynomial.rename_X]

@[simp] theorem swapInverseVariables_X_one :
    swapInverseVariables (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) (Space K)) =
      MvPolynomial.X 0 := by
  simp [swapInverseVariables, MvPolynomial.rename_X]

theorem normalWithPolynomial_C_coeff (f g : LaurentSeries (Space K))
    (c : Space K) (a b : ℤ) :
    ((normalWithPolynomial f g (MvPolynomial.C c)).coeff b).coeff a =
      f.coeff a * g.coeff b * c := by
  rw [normalWithPolynomial, jointLaurentEmbedding, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero,
    HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero, separated_coeff]

theorem normalWithPolynomial_mul_X_zero_coeff (f g : LaurentSeries (Space K))
    (p : MvPolynomial (Fin 2) (Space K)) (a b : ℤ) :
    ((normalWithPolynomial f g (p * MvPolynomial.X 0)).coeff b).coeff a =
      ((normalWithPolynomial f g p).coeff b).coeff (a + 1) := by
  have hx : jointLaurentEmbedding (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) (Space K)) =
      HahnSeries.C (HahnSeries.single (-1) 1) := by
    simp [jointLaurentEmbedding]
  rw [normalWithPolynomial, map_mul, ← mul_assoc, hx, HahnSeries.C_apply,
    HahnSeries.coeff_mul_single_zero, HahnSeries.coeff_mul_single]
  simp only [sub_neg_eq_add, mul_one]
  rfl

theorem normalWithPolynomial_mul_X_one_coeff (f g : LaurentSeries (Space K))
    (p : MvPolynomial (Fin 2) (Space K)) (a b : ℤ) :
    ((normalWithPolynomial f g (p * MvPolynomial.X 1)).coeff b).coeff a =
      ((normalWithPolynomial f g p).coeff (b + 1)).coeff a := by
  have hx : jointLaurentEmbedding (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) (Space K)) =
      HahnSeries.single (-1) (HahnSeries.C 1) := by
    simp [jointLaurentEmbedding]
  rw [normalWithPolynomial, map_mul, ← mul_assoc, hx, HahnSeries.coeff_mul_single,
    map_one, mul_one]
  simp only [sub_neg_eq_add]
  rfl

/-- Exchange of variables is proved on the finite polynomial representation;
no transpose of an arbitrary iterated Laurent series is assumed. -/
theorem normalWithPolynomial_swapped (f g : LaurentSeries (Space K))
    (p : MvPolynomial (Fin 2) (Space K)) (a b : ℤ) :
    ((normalWithPolynomial f g p).coeff b).coeff a =
      ((normalWithPolynomial g f (swapInverseVariables p)).coeff a).coeff b := by
  induction p using MvPolynomial.induction_on generalizing a b with
  | C c =>
    rw [swapInverseVariables_C, normalWithPolynomial_C_coeff,
      normalWithPolynomial_C_coeff]
    ring
  | add p q hp hq =>
    simp only [map_add, normalWithPolynomial_add, HahnSeries.coeff_add, hp, hq]
  | mul_X p v hp =>
    rcases (show v = 0 ∨ v = 1 by omega) with hv | hv
    · subst v
      rw [map_mul, swapInverseVariables_X_zero, normalWithPolynomial_mul_X_zero_coeff,
        normalWithPolynomial_mul_X_one_coeff]
      exact hp (a + 1) b
    · subst v
      rw [map_mul, swapInverseVariables_X_one, normalWithPolynomial_mul_X_one_coeff,
        normalWithPolynomial_mul_X_zero_coeff]
      exact hp a (b + 1)

theorem jointAnnihilationPolynomial_swapped (w : K) (β γ : Lattice) (s t : Fin 3) :
    swapInverseVariables.comp (jointAnnihilationPolynomial w β γ s t) =
      jointAnnihilationPolynomial w γ β t s := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, jointAnnihilationPolynomial, MvPolynomial.eval₂Hom_C,
      swapInverseVariables_C]
  · intro v
    simp only [RingHom.comp_apply, jointAnnihilationPolynomial, MvPolynomial.eval₂Hom_X',
      map_add, map_mul, map_pow, swapInverseVariables_C, swapInverseVariables_X_zero,
      swapInverseVariables_X_one]
    ring

/-- The normal product of the concrete first-root operators is symmetric
under simultaneous exchange of tensor positions and field variables. -/
theorem normalProduct_swapped (w : K) (s t : Fin 3) (f : Space K) (a b : ℤ) :
    ((normalProduct w s t f).coeff b).coeff a =
      ((normalProduct w t s f).coeff a).coeff b := by
  rw [normalProduct_eq_normalWithPolynomial, normalProduct_eq_normalWithPolynomial]
  rw [normalWithPolynomial_swapped]
  have h := RingHom.congr_fun
    (jointAnnihilationPolynomial_swapped w (simpleRoot 0) (simpleRoot 0) s t) f
  simp only [RingHom.comp_apply] at h
  rw [h]

end KanadeRussell.Tsuchioka.Fock
