import KanadeRussell.Tsuchioka.ScalarContraction
import KanadeRussell.Tsuchioka.TensorModeResidues
import KanadeRussell.Tsuchioka.TensorCentralEuler

/-! All tensor first-root pole residues, including the central Heisenberg
term, as linear maps in the finite Fourier kernel. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

/-- Finite contraction against one normal product, as a linear map in the kernel. -/
noncomputable def tensorNormalResidue (w : K) (s t : Fin 3) (f : Space K) (a b : ℤ) :
    (ℤ → K) →ₗ[K] Space K where
  toFun c := scalarContract c (tensorNormalProduct w (RootData.simpleRoot 0) (RootData.simpleRoot 0) s t f) (-a) (-b)
  map_add' c d := by
    obtain ⟨l, r, h⟩ := tensorNormalProduct_bounded w (RootData.simpleRoot 0) (RootData.simpleRoot 0) s t f
    exact scalarContract_add h c d (-a) (-b)
  map_smul' z c := by
    obtain ⟨l, r, h⟩ := tensorNormalProduct_bounded w (RootData.simpleRoot 0) (RootData.simpleRoot 0) s t f
    change scalarContract (fun n => z * c n) (tensorNormalProduct w (RootData.simpleRoot 0) (RootData.simpleRoot 0) s t f) (-a) (-b) =
      z • scalarContract c (tensorNormalProduct w (RootData.simpleRoot 0) (RootData.simpleRoot 0) s t f) (-a) (-b)
    exact scalarContract_mul h c z (-a) (-b)

@[simp] theorem tensorNormalResidue_apply (w : K) (s t : Fin 3) (f : Space K) (a b : ℤ)
    (c : ℤ → K) :
    tensorNormalResidue w s t f a b c =
      scalarContract c (tensorNormalProduct w (RootData.simpleRoot 0) (RootData.simpleRoot 0) s t f) (-a) (-b) := rfl

noncomputable def tensorSameResidue (w : K) (f : Space K) (a b : ℤ) :
    (ℤ → K) →ₗ[K] Space K :=
  (1 / 144 : K) • ∑ j : Fin 3, tensorNormalResidue w j j f a b

theorem tensorSameResidue_apply (w : K) (f : Space K) (a b : ℤ) (c : ℤ → K) :
    tensorSameResidue w f a b c =
      (1 / 144 : K) • ∑ j : Fin 3, tensorNormalResidue w j j f a b c := by
  simp only [tensorSameResidue, LinearMap.smul_apply, LinearMap.sum_apply]

/-- The central delta residue of each complete normal product, as an
identity operator in total mode zero. -/
theorem tensorFirstRoot_delta_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) (a b : ℤ) :
    contract (fun n : ℤ => MvPolynomial.C ((-1 : K) ^ n))
        (tensorNormalProduct w (RootData.simpleRoot 0) (RootData.simpleRoot 0) j j f) (-a) (-b) =
      if a + b = 0 then (-1 : K) ^ a • f else 0 := by
  have hc : (fun n : ℤ => MvPolynomial.C ((-1 : K) ^ n)) =
      (fun n => ((phaseUnit w hw 6 ^ n : (Space K)ˣ) : Space K)) := by
    funext n
    rw [phaseUnit_zpow, root_six_neg_phase w hw]
  rw [hc, show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl,
    tensorNormalProduct_delta_contraction_same, RootData.coxeter_six, neg_add_cancel, tensorRootSummand_zero]
  norm_num only [Nat.cast_ofNat]
  rw [show (6 : ℤ) * (-a) = -6 * a by ring, root_six_neg_phase w hw]
  by_cases hab : a + b = 0
  · have hz : -a + -b = 0 := by omega
    simp [HahnSeries.C_apply, hz, hab, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  · have hz : -a + -b ≠ 0 := by omega
    simp [HahnSeries.C_apply, HahnSeries.coeff_single, hz, hab]

theorem tensorFirstRoot_delta_sum_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    (1 / 144 : K) • ∑ j : Fin 3,
      contract (fun n : ℤ => MvPolynomial.C ((-1 : K) ^ n))
        (tensorNormalProduct w (RootData.simpleRoot 0) (RootData.simpleRoot 0) j j f) (-a) (-b) =
      if a + b = 0 then ((-1 : K) ^ a / 48) • f else 0 := by
  simp only [tensorFirstRoot_delta_six w hw]
  by_cases hab : a + b = 0
  · simp only [if_pos hab, Fin.sum_univ_three, ← add_smul, smul_smul]
    congr 1
    ring
  · simp [hab]

theorem tensorSameResidue_delta_four (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorSameResidue w f a b (Scalar.delta (w ^ (-4 : ℤ))) =
      (w ^ (-2 * a + 2 * b) / 12) • tensorRootMode w (RootData.simpleRoot 0) (a + b) f := by
  simpa only [tensorSameResidue_apply, tensorNormalResidue_apply, scalarContract_delta_phase] using
    tensorFirstRoot_delta_four w hw f a b

theorem tensorSameResidue_delta_eight (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorSameResidue w f a b (Scalar.delta (w ^ 4)) =
      (w ^ (2 * a - 2 * b) / 12) • tensorRootMode w (RootData.simpleRoot 0) (a + b) f := by
  have hp : w ^ 4 = w ^ (-8 : ℤ) := by
    rw [Coefficients.zpow_mod_twelve w hw]
    norm_num only [show (-8 : ℤ) % 12 = 4 by decide, show (4 : ℤ).toNat = 4 by decide]
  rw [hp]
  simpa only [tensorSameResidue_apply, tensorNormalResidue_apply, scalarContract_delta_phase] using
    tensorFirstRoot_delta_eight w hw f a b

theorem tensorSameResidue_delta_five (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorSameResidue w f a b (Scalar.delta (w ^ (-5 : ℤ))) =
      (w ^ (4 * a + 9 * b) / 12) • tensorRootMode w (RootData.simpleRoot 1) (a + b) f := by
  simpa only [tensorSameResidue_apply, tensorNormalResidue_apply, scalarContract_delta_phase] using
    tensorFirstRoot_delta_five w hw f a b

theorem tensorSameResidue_delta_seven (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorSameResidue w f a b (Scalar.delta (w ^ 5)) =
      (w ^ (9 * a + 4 * b) / 12) • tensorRootMode w (RootData.simpleRoot 1) (a + b) f := by
  have hp : w ^ 5 = w ^ (-7 : ℤ) := by
    rw [Coefficients.zpow_mod_twelve w hw]
    norm_num only [show (-7 : ℤ) % 12 = 5 by decide, show (5 : ℤ).toNat = 5 by decide]
  rw [hp]
  simpa only [tensorSameResidue_apply, tensorNormalResidue_apply, scalarContract_delta_phase] using
    tensorFirstRoot_delta_seven w hw f a b

theorem tensorSameResidue_delta_central (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorSameResidue w f a b (Scalar.delta (-1 : K)) =
      if a + b = 0 then ((-1 : K) ^ a / 48) • f else 0 := by
  simpa only [tensorSameResidue_apply, tensorNormalResidue_apply, scalarContract, Scalar.delta] using
    tensorFirstRoot_delta_sum_six w hw f a b

/-- The individual Euler residue retains the derivative of the normal product. -/
theorem tensorNormalResidue_euler_central (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) (a b : ℤ) :
    tensorNormalResidue w j j f a b (Scalar.eulerDelta (-1 : K)) =
      MvPolynomial.C ((-1 : K) ^ a) *
        diagonalEulerCoefficient (phaseUnit w hw 6) (tensorNormalProduct w (RootData.simpleRoot 0) (RootData.simpleRoot 0) j j f) (-a + -b) +
      (a : K) • tensorNormalResidue w j j f a b (Scalar.delta (-1 : K)) := by
  obtain ⟨l, r, h⟩ := tensorNormalProduct_bounded w (RootData.simpleRoot 0) (RootData.simpleRoot 0) j j f
  have hc : (fun n : ℤ => (MvPolynomial.C (Scalar.delta (-1 : K) n) : Space K)) =
      (fun n => ((phaseUnit w hw 6 ^ n : (Space K)ˣ) : Space K)) := by
    funext n
    simp only [Scalar.delta, phaseUnit_zpow, root_six_neg_phase w hw]
  have he : (fun n : ℤ => (MvPolynomial.C (Scalar.eulerDelta (-1 : K) n) : Space K)) =
      (fun n : ℤ => (n : Space K) * ((phaseUnit w hw 6 ^ n : (Space K)ˣ) : Space K)) := by
    funext n
    simp only [Scalar.eulerDelta, map_mul, map_intCast, phaseUnit_zpow,
      root_six_neg_phase w hw]
  simp only [tensorNormalResidue_apply, scalarContract]
  rw [he, hc, contract_eulerDelta h, contract_delta h, phaseUnit_zpow]
  simp only [neg_neg, root_six_neg_phase w hw, Int.cast_neg, Algebra.smul_def,
    MvPolynomial.algebraMap_eq, map_intCast]
  ring

theorem tensorSameResidue_euler_eq_heisenberg_delta (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (f : Space K) (a b : ℤ) :
    tensorSameResidue w f a b (Scalar.eulerDelta (-1 : K)) =
      (-((-1 : K) ^ a) / 12) • heisenbergMode w (a + b) f +
        (a : K) • tensorSameResidue w f a b (Scalar.delta (-1 : K)) := by
  simp only [tensorSameResidue_apply, tensorNormalResidue_euler_central w hw,
    Finset.sum_add_distrib, ← Finset.mul_sum, sum_tensorNormalProduct_central_euler w hw,
    ← Finset.smul_sum, MvPolynomial.C_mul', smul_add, smul_smul]
  rw [show -(-a + -b) = a + b by ring]
  module

theorem tensorSameResidue_euler_central (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorSameResidue w f a b (Scalar.eulerDelta (-1 : K)) =
      (-((-1 : K) ^ a) / 12) • heisenbergMode w (a + b) f +
        (if a + b = 0 then ((a : K) * (-1 : K) ^ a / 48) • f else 0) := by
  rw [tensorSameResidue_euler_eq_heisenberg_delta w hw, tensorSameResidue_delta_central w hw]
  by_cases hab : a + b = 0 <;> simp only [hab, if_true, if_false, smul_smul, smul_zero] <;> module

end KanadeRussell.Tsuchioka.Fock
