import KanadeRussell.Tsuchioka.ScalarContraction
import KanadeRussell.Tsuchioka.CentralDelta
import KanadeRussell.Tsuchioka.MixedPole

/-! Linear residue maps and all pole evaluations needed by the G2 anticommutator. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

/-- Finite contraction against one normal product, as a linear map in the kernel. -/
noncomputable def normalResidue (w : K) (s t : Fin 3) (f : Space K) (a b : ℤ) :
    (ℤ → K) →ₗ[K] Space K where
  toFun c := scalarContract c (normalProduct w s t f) (-a) (-b)
  map_add' c d := by
    obtain ⟨l, r, h⟩ := normalProduct_bounded w s t f
    exact scalarContract_add h c d (-a) (-b)
  map_smul' z c := by
    obtain ⟨l, r, h⟩ := normalProduct_bounded w s t f
    change scalarContract (fun n => z * c n) (normalProduct w s t f) (-a) (-b) =
      z • scalarContract c (normalProduct w s t f) (-a) (-b)
    exact scalarContract_mul h c z (-a) (-b)

@[simp] theorem normalResidue_apply (w : K) (s t : Fin 3) (f : Space K) (a b : ℤ)
    (c : ℤ → K) :
    normalResidue w s t f a b c =
      scalarContract c (normalProduct w s t f) (-a) (-b) := rfl

noncomputable def sameResidue (w : K) (f : Space K) (a b : ℤ) :
    (ℤ → K) →ₗ[K] Space K :=
  (1 / 144 : K) • ∑ j : Fin 3, normalResidue w j j f a b

noncomputable def mixedResidue (w : K) (f : Space K) (a b : ℤ) :
    (ℤ → K) →ₗ[K] Space K :=
  (1 / 144 : K) • ∑ s : Fin 3, ∑ t : Fin 3,
    if s = t then 0 else normalResidue w s t f a b

theorem sameResidue_apply (w : K) (f : Space K) (a b : ℤ) (c : ℤ → K) :
    sameResidue w f a b c =
      (1 / 144 : K) • ∑ j : Fin 3, normalResidue w j j f a b c := by
  simp only [sameResidue, LinearMap.smul_apply, LinearMap.sum_apply]

theorem mixedResidue_apply (w : K) (f : Space K) (a b : ℤ) (c : ℤ → K) :
    mixedResidue w f a b c =
      (1 / 144 : K) • ∑ s : Fin 3, ∑ t : Fin 3,
        if s = t then 0 else normalResidue w s t f a b c := by
  simp only [mixedResidue, LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1

theorem sameResidue_delta_four (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    sameResidue w f a b (Scalar.delta (w ^ (-4 : ℤ))) =
      (w ^ (-2 * a + 2 * b) / 12) • mode w (a + b) f := by
  simpa only [sameResidue_apply, normalResidue_apply, scalarContract_delta_phase] using
    firstRoot_delta_four w hw f a b

theorem sameResidue_delta_eight (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    sameResidue w f a b (Scalar.delta (w ^ 4)) =
      (w ^ (2 * a - 2 * b) / 12) • mode w (a + b) f := by
  have hp : w ^ 4 = w ^ (-8 : ℤ) := by
    rw [Coefficients.zpow_mod_twelve w hw]
    norm_num only [show (-8 : ℤ) % 12 = 4 by decide, show (4 : ℤ).toNat = 4 by decide]
  rw [hp]
  simpa only [sameResidue_apply, normalResidue_apply, scalarContract_delta_phase] using
    firstRoot_delta_eight w hw f a b

theorem sameResidue_delta_five (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    sameResidue w f a b (Scalar.delta (w ^ (-5 : ℤ))) =
      (w ^ (4 * a + 9 * b) / 12) • secondRootMode w (a + b) f := by
  simpa only [sameResidue_apply, normalResidue_apply, scalarContract_delta_phase] using
    firstRoot_delta_five w hw f a b

theorem sameResidue_delta_seven (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    sameResidue w f a b (Scalar.delta (w ^ 5)) =
      (w ^ (9 * a + 4 * b) / 12) • secondRootMode w (a + b) f := by
  have hp : w ^ 5 = w ^ (-7 : ℤ) := by
    rw [Coefficients.zpow_mod_twelve w hw]
    norm_num only [show (-7 : ℤ) % 12 = 5 by decide, show (5 : ℤ).toNat = 5 by decide]
  rw [hp]
  simpa only [sameResidue_apply, normalResidue_apply, scalarContract_delta_phase] using
    firstRoot_delta_seven w hw f a b

theorem sameResidue_delta_central (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    sameResidue w f a b (Scalar.delta (-1 : K)) =
      if a + b = 0 then ((-1 : K) ^ a / 48) • f else 0 := by
  simpa only [sameResidue_apply, normalResidue_apply, scalarContract, Scalar.delta] using
    firstRoot_delta_sum_six w hw f a b

theorem normalResidue_delta_one (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (s t : Fin 3) (f : Space K) (a b : ℤ) :
    normalResidue w s t f a b (Scalar.delta (1 : K)) =
      (poleNormalProduct w hw (RootData.simpleRoot 0) (RootData.simpleRoot 0) s t 0 f).coeff
        (-(a + b)) := by
  have h := normalProduct_delta_contraction w hw s t f 0 (-a) (-b)
  rw [show -a + -b = -(a + b) by ring] at h
  simpa only [normalResidue_apply, scalarContract, Scalar.delta, phaseUnit_zpow,
    neg_zero, zero_mul, zpow_zero, one_zpow, map_one, one_mul] using h

/-- The six mixed-position residues at ratio one give the coefficient 1/6
of the negative first-root mode after restoring the full-field normalization. -/
theorem mixedResidue_delta_one (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    mixedResidue w f a b (Scalar.delta (1 : K)) =
      ((-1 : K) ^ (a + b) / 6) • mode w (a + b) f := by
  have h := congrArg (fun z : LaurentSeries (Space K) => z.coeff (-(a + b)))
    (sum_mixed_pole_zero w hw f)
  simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul] at h
  have hi (s t : Fin 3) :
      (if s = t then (0 : LaurentSeries (Space K))
        else poleNormalProduct w hw (RootData.simpleRoot 0) (RootData.simpleRoot 0) s t 0 f).coeff (-(a + b)) =
      if s = t then 0 else
        (poleNormalProduct w hw (RootData.simpleRoot 0) (RootData.simpleRoot 0) s t 0 f).coeff (-(a + b)) := by
    split_ifs <;> rfl
  simp_rw [hi] at h
  rw [sum_rootSummand_coeff, negative_firstRoot_mode w hw] at h
  rw [mixedResidue_apply]
  simp_rw [normalResidue_delta_one w hw]
  rw [h, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

end KanadeRussell.Tsuchioka.Fock
