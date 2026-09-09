import KanadeRussell.Tsuchioka.TensorNormalOrdering
import KanadeRussell.Tsuchioka.NormalProductSymmetry

/-! Finite two-variable annihilation for tensor root fields. It supplies
separate Laurent bounds, coefficientwise exchange symmetry, and commutation
of modes acting in distinct tensor positions. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (Lattice rootWeight)

variable {K : Type*} [Field K] [CharZero K]

noncomputable def tensorJointAnnihilationPolynomial (w : K) (β γ : Lattice) (j k : Fin 3) :
    Space K →+* MvPolynomial (Fin 2) (Space K) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) fun s =>
    MvPolynomial.C (MvPolynomial.X s) +
      MvPolynomial.C (MvPolynomial.C (if s.1 = j then
        -contraction w s.2.val * rootWeight (w ^ (s.2.val : ℤ)) β else 0)) *
          MvPolynomial.X 0 ^ s.2.val +
      MvPolynomial.C (MvPolynomial.C (if s.1 = k then
        -contraction w s.2.val * rootWeight (w ^ (s.2.val : ℤ)) γ else 0)) *
          MvPolynomial.X 1 ^ s.2.val

theorem jointLaurentEmbedding_tensorAnnihilation (w : K) (β γ : Lattice) (j k : Fin 3) :
    jointLaurentEmbedding.comp (tensorJointAnnihilationPolynomial w β γ j k) =
      (mapLaurent (tensorRootAnnihilation w β j)).comp (tensorRootAnnihilation w γ k) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, tensorJointAnnihilationPolynomial, tensorRootAnnihilation,
      jointLaurentEmbedding, MvPolynomial.eval₂Hom_C, FormalSeries.mapLaurent_C]
  · intro s
    simp only [RingHom.comp_apply, tensorJointAnnihilationPolynomial, MvPolynomial.eval₂Hom_X',
      jointLaurentEmbedding, map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', ite_true,
      if_neg (by decide : (1 : Fin 2) ≠ 0), tensorRootAnnihilation,
      FormalSeries.mapLaurent_C, FormalSeries.mapLaurent_single]
    simp only [ite_true, ← map_mul, map_one]
    rw [doubleC_inverseVariable_mul, constant_inverseVariable_mul]

theorem tensorNormalProduct_eq_normalWithPolynomial (w : K) (β γ : Lattice)
    (s t : Fin 3) (f : Space K) :
    tensorNormalProduct w β γ s t f =
      normalWithPolynomial (tensorRootCreation w β s) (tensorRootCreation w γ t)
        (tensorJointAnnihilationPolynomial w β γ s t f) := by
  have h := RingHom.congr_fun (jointLaurentEmbedding_tensorAnnihilation w β γ s t) f
  simp only [RingHom.comp_apply] at h
  rw [normalWithPolynomial, h, tensorNormalProduct, separated,
    FormalSeries.mapLaurent_powerSeries]

theorem tensorNormalProduct_bounded (w : K) (β γ : Lattice) (s t : Fin 3) (f : Space K) :
    ∃ l r : ℤ, RectangularBound (tensorNormalProduct w β γ s t f) l r := by
  rw [tensorNormalProduct_eq_normalWithPolynomial]
  exact normalWithPolynomial_bounded _ _ _

theorem tensorNormalProduct_contraction_finite (w : K) (β γ : Lattice)
    (s t : Fin 3) (f : Space K) (c : ℤ → Space K) (a b : ℤ) :
    (Function.support (fun n => c n *
      ((tensorNormalProduct w β γ s t f).coeff (b - n)).coeff (a + n))).Finite := by
  obtain ⟨l, r, h⟩ := tensorNormalProduct_bounded w β γ s t f
  exact rectangular_contraction_finite h c a b

theorem tensorJointAnnihilationPolynomial_swapped (w : K) (β γ : Lattice) (s t : Fin 3) :
    swapInverseVariables.comp (tensorJointAnnihilationPolynomial w β γ s t) =
      tensorJointAnnihilationPolynomial w γ β t s := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, tensorJointAnnihilationPolynomial, MvPolynomial.eval₂Hom_C,
      swapInverseVariables_C]
  · intro v
    simp only [RingHom.comp_apply, tensorJointAnnihilationPolynomial, MvPolynomial.eval₂Hom_X',
      map_add, map_mul, map_pow, swapInverseVariables_C, swapInverseVariables_X_zero,
      swapInverseVariables_X_one]
    ring

theorem tensorNormalProduct_swapped (w : K) (β γ : Lattice) (s t : Fin 3)
    (f : Space K) (a b : ℤ) :
    ((tensorNormalProduct w β γ s t f).coeff b).coeff a =
      ((tensorNormalProduct w γ β t s f).coeff a).coeff b := by
  rw [tensorNormalProduct_eq_normalWithPolynomial, tensorNormalProduct_eq_normalWithPolynomial]
  rw [normalWithPolynomial_swapped]
  have h := RingHom.congr_fun (tensorJointAnnihilationPolynomial_swapped w β γ s t) f
  simp only [RingHom.comp_apply] at h
  rw [h]

/-- Modes in distinct tensor positions commute on every polynomial input. -/
theorem tensorRootSummand_modes_commute_distinct (w : K) (β γ : Lattice)
    (s t : Fin 3) (hst : s ≠ t) (a b : ℤ) (f : Space K) :
    (tensorRootSummand w β s ((tensorRootSummand w γ t f).coeff (-b))).coeff (-a) =
      (tensorRootSummand w γ t ((tensorRootSummand w β s f).coeff (-a))).coeff (-b) := by
  rw [← tensorTwoSummands_coeff, ← tensorTwoSummands_coeff,
    tensorTwoSummands_distinct_normalOrdered w β γ s t hst,
    tensorTwoSummands_distinct_normalOrdered w γ β t s hst.symm]
  exact tensorNormalProduct_swapped w β γ s t f (-a) (-b)

theorem tensorNormalProduct_diagonal (w : K) (β γ : Lattice) (s t : Fin 3)
    (f : Space K) (u : (Space K)ˣ) (d : ℤ) :
    diagonalCoefficient u (tensorNormalProduct w β γ s t f) d =
      (laurentRescale u (tensorRootCreation w β s) *
        (tensorRootCreation w γ t : LaurentSeries (Space K)) *
          polynomialPoleEvaluation u (tensorJointAnnihilationPolynomial w β γ s t f)).coeff d := by
  rw [tensorNormalProduct_eq_normalWithPolynomial, normalWithPolynomial_diagonal]

end KanadeRussell.Tsuchioka.Fock
