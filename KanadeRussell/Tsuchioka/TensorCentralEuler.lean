import KanadeRussell.Tsuchioka.TensorCentralCreationEuler

/-! The summed tensor central Euler derivative is the actual signed
Heisenberg mode. It does not vanish away from total mode zero. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

/-- Both normalized Heisenberg halves, with zero in the absent principal degrees. -/
noncomputable def heisenbergMode (w : K) (i : ℤ) : Module.End K (Space K) :=
  if h : IsMode i.natAbs then
    if 0 < i then heisenbergPositive w (⟨i.natAbs, h⟩ : Mode)
    else heisenbergNegative (⟨i.natAbs, h⟩ : Mode)
  else 0

theorem heisenbergMode_positive (w : K) (n : Mode) :
    heisenbergMode w n.val = heisenbergPositive w n := by
  simp [heisenbergMode, n.property, mode_pos n]

theorem heisenbergMode_negative (w : K) (n : Mode) :
    heisenbergMode w (-(n.val : ℤ)) = heisenbergNegative n := by
  simp [heisenbergMode, n.property]

theorem heisenbergMode_not_mode (w : K) (i : ℤ) (hi : ¬IsMode i.natAbs) :
    heisenbergMode w i = 0 := by simp [heisenbergMode, hi]

@[simp] theorem heisenbergMode_zero (w : K) : heisenbergMode w 0 = 0 := by
  simp [heisenbergMode, IsMode]

theorem tensorAnnihilationEulerDerivation_not_mode (w : K) (m : ℕ) (hm : ¬IsMode m) :
    tensorAnnihilationEulerDerivation w (-(m : ℤ)) = 0 := by
  apply MvPolynomial.derivation_ext
  intro s
  have hne : (-(m : ℤ)) ≠ -(s.2.val : ℤ) := by
    intro h
    have he : m = s.2.val := by exact_mod_cast neg_injective h
    exact hm (he ▸ s.2.property)
  simp only [tensorAnnihilationEulerDerivation, MvPolynomial.mkDerivation_X,
    Derivation.zero_apply, HahnSeries.coeff_single, if_neg hne]

theorem tensorNormalProduct_central_euler (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) (d : ℤ) :
    diagonalEulerCoefficient (phaseUnit w hw 6)
        (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) j j f) d =
      (laurentRescale (phaseUnit w hw 6)
          (laurentEuler (tensorRootCreation w (simpleRoot 0) j : LaurentSeries (Space K))) *
        (tensorRootCreation w (simpleRoot 0) j : LaurentSeries (Space K)) * HahnSeries.C f).coeff d -
      (tensorCentralAnnihilationEuler w hw j f).coeff d := by
  rw [tensorNormalProduct_eq_normalWithPolynomial, normalWithPolynomial_euler,
    tensor_polynomial_central_evaluation w hw, tensorCreation_central_fusion w hw, one_mul]
  rfl

theorem sum_tensorNormalProduct_central_euler_negative (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : Mode) (f : Space K) :
    ∑ j : Fin 3, diagonalEulerCoefficient (phaseUnit w hw 6)
        (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) j j f) (-(n.val : ℤ)) =
      (-12 : K) • heisenbergPositive w n f := by
  simp only [tensorNormalProduct_central_euler w hw, Finset.sum_sub_distrib,
    HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero,
    tensorCreation_central_euler_coeff_nonpositive w hw _ _ _ (by omega : -(n.val : ℤ) ≤ 0),
    zero_mul, Finset.sum_const_zero, zero_sub, Finset.sum_neg_distrib,
    sum_tensorCentralAnnihilationEuler_heisenberg w hw, neg_smul]

theorem sum_tensorNormalProduct_central_euler_positive (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : Mode) (f : Space K) :
    ∑ j : Fin 3, diagonalEulerCoefficient (phaseUnit w hw 6)
        (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) j j f) n.val =
      (-12 : K) • heisenbergNegative n f := by
  simp only [tensorNormalProduct_central_euler w hw, Finset.sum_sub_distrib]
  rw [sum_tensorCreation_central_euler_heisenberg w hw,
    sum_tensorCentralAnnihilationEuler_coeff, tensorAnnihilationEulerDerivation_nonnegative w n.val (by omega)]
  simp

theorem sum_tensorNormalProduct_central_euler_not_mode_positive (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (m : ℕ) (hm : ¬IsMode m) (f : Space K) :
    ∑ j : Fin 3, diagonalEulerCoefficient (phaseUnit w hw 6)
        (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) j j f) m = 0 := by
  simp only [tensorNormalProduct_central_euler w hw, Finset.sum_sub_distrib,
    HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero,
    tensorCreation_central_euler_coeff_not_mode w hw _ _ m hm,
    zero_mul, Finset.sum_const_zero, zero_sub, Finset.sum_neg_distrib]
  rw [sum_tensorCentralAnnihilationEuler_coeff,
    tensorAnnihilationEulerDerivation_nonnegative w m (by omega)]
  simp

theorem sum_tensorNormalProduct_central_euler_not_mode_negative (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (m : ℕ) (hm : ¬IsMode m) (f : Space K) :
    ∑ j : Fin 3, diagonalEulerCoefficient (phaseUnit w hw 6)
        (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) j j f) (-(m : ℤ)) = 0 := by
  simp only [tensorNormalProduct_central_euler w hw, Finset.sum_sub_distrib,
    HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero,
    tensorCreation_central_euler_coeff_nonpositive w hw _ _ _ (by omega : -(m : ℤ) ≤ 0),
    zero_mul, Finset.sum_const_zero, zero_sub, Finset.sum_neg_distrib]
  rw [sum_tensorCentralAnnihilationEuler_coeff, tensorAnnihilationEulerDerivation_not_mode w m hm]
  simp

/-- The central inner Euler derivative supplies the full Heisenberg mode
at the opposite Laurent degree, with the source factor -12. -/
theorem sum_tensorNormalProduct_central_euler (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (d : ℤ) :
    ∑ j : Fin 3, diagonalEulerCoefficient (phaseUnit w hw 6)
        (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) j j f) d =
      (-12 : K) • heisenbergMode w (-d) f := by
  cases d with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast]
    by_cases hm : IsMode m
    · have h := sum_tensorNormalProduct_central_euler_positive w hw (⟨m, hm⟩ : Mode) f
      rw [heisenbergMode_negative w (⟨m, hm⟩ : Mode)]
      exact h
    · rw [sum_tensorNormalProduct_central_euler_not_mode_positive w hw m hm]
      rw [heisenbergMode_not_mode w _ (by simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hm)]
      simp
  | negSucc m =>
    have he : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := rfl
    rw [he, neg_neg]
    by_cases hm : IsMode (m + 1)
    · rw [heisenbergMode_positive w (⟨m + 1, hm⟩ : Mode)]
      exact sum_tensorNormalProduct_central_euler_negative w hw (⟨m + 1, hm⟩ : Mode) f
    · rw [sum_tensorNormalProduct_central_euler_not_mode_negative w hw (m + 1) hm]
      rw [heisenbergMode_not_mode w _ (by simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hm)]
      simp

end KanadeRussell.Tsuchioka.Fock
