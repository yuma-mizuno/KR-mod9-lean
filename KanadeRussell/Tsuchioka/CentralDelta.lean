import KanadeRussell.Tsuchioka.ModeResidues

/-! Integer sign phases, negative-root modes, and the central delta residue. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem neg_one_zpow_neg (a : ℤ) : (-1 : K) ^ (-a) = (-1 : K) ^ a := by
  by_cases ha : Even a <;> simp [neg_one_zpow_eq_ite, ha]

theorem root_six_phase (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (a : ℤ) :
    w ^ (6 * a) = (-1 : K) ^ a := by
  rw [zpow_mul, show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast,
    root_pow_six w hw]

theorem root_six_neg_phase (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (a : ℤ) :
    w ^ (-6 * a) = (-1 : K) ^ a := by
  rw [show (-6 : ℤ) * a = 6 * (-a) by ring, root_six_phase w hw, neg_one_zpow_neg]

theorem negative_firstRoot_mode (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (i : ℤ) (f : Space K) :
    rootMode w (-simpleRoot 0) i f = (-1 : K) ^ i • mode w i f := by
  have h := rootMode_iterate w hw (simpleRoot 0) 6 i f
  rw [RootData.coxeter_six, rootMode_first] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [root_six_phase w hw] at h
  exact h

/-- The central delta residue of each complete normal product, as an
identity operator in total mode zero. -/
theorem firstRoot_delta_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) (a b : ℤ) :
    contract (fun n : ℤ => MvPolynomial.C ((-1 : K) ^ n))
        (normalProduct w j j f) (-a) (-b) =
      if a + b = 0 then (-1 : K) ^ a • f else 0 := by
  have hc : (fun n : ℤ => MvPolynomial.C ((-1 : K) ^ n)) =
      (fun n => ((phaseUnit w hw 6 ^ n : (Space K)ˣ) : Space K)) := by
    funext n
    rw [phaseUnit_zpow, root_six_neg_phase w hw]
  rw [hc, normalProduct_delta_contraction, poleNormalProduct_six]
  rw [show (6 : ℤ) * (-a) = -6 * a by ring, root_six_neg_phase w hw]
  by_cases hab : a + b = 0
  · have hz : -a + -b = 0 := by omega
    simp [HahnSeries.C_apply, hz, hab, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  · have hz : -a + -b ≠ 0 := by omega
    simp [HahnSeries.C_apply, HahnSeries.coeff_single, hz, hab]

theorem firstRoot_delta_sum_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    (1 / 144 : K) • ∑ j : Fin 3,
      contract (fun n : ℤ => MvPolynomial.C ((-1 : K) ^ n))
        (normalProduct w j j f) (-a) (-b) =
      if a + b = 0 then ((-1 : K) ^ a / 48) • f else 0 := by
  simp only [firstRoot_delta_six w hw]
  by_cases hab : a + b = 0
  · simp only [if_pos hab, Fin.sum_univ_three, ← add_smul, smul_smul]
    congr 1
    ring
  · simp [hab]

end KanadeRussell.Tsuchioka.Fock
