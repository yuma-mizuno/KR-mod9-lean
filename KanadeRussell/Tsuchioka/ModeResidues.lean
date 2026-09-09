import KanadeRussell.Tsuchioka.NormalProductEvaluation

/-!
The noncentral delta residues, expressed as actual first- and second-root modes
with the phases and the 1/12 normalization in the source relations.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries
open RootData (Lattice simpleRoot coxeter)

variable {K : Type*} [Field K] [CharZero K]

theorem sum_rootSummand_coeff (w : K) (β : Lattice) (f : Space K) (i : ℤ) :
    ∑ j : Fin 3, (rootSummand w β j f).coeff (-i) =
      (12 : K) • rootMode w β i f := by
  have h : rootMode w β i f =
      (1 / 12 : K) • ∑ j : Fin 3, (rootSummand w β j f).coeff (-i) := by
    change (rootField w β f).coeff (-i) = _
    simp only [rootField, LinearMap.smul_apply, LinearMap.sum_apply,
      HahnSeries.coeff_smul, HahnSeries.coeff_sum]
  rw [h, smul_smul]
  norm_num

/-- A checked root addition determines the full delta residue of one tensor
summand. The four applications below discharge the root-addition premise. -/
theorem firstRoot_delta_fusion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p q : ℕ) (β : Lattice)
    (hfusion : (coxeter^[p]) (simpleRoot 0) + simpleRoot 0 = (coxeter^[q]) β)
    (j : Fin 3) (f : Space K) (a b : ℤ) :
    contract (fun n : ℤ => MvPolynomial.C (w ^ (-(p : ℤ) * n)))
        (normalProduct w j j f) (-a) (-b) =
      w ^ (((q : ℤ) - p) * a + q * b) •
        (rootSummand w β j f).coeff (-(a + b)) := by
  have hc : (fun n : ℤ => MvPolynomial.C (w ^ (-(p : ℤ) * n))) =
      (fun n => ((phaseUnit w hw p ^ n : (Space K)ˣ) : Space K)) := by
    funext n
    exact (phaseUnit_zpow w hw p n).symm
  rw [hc, normalProduct_delta_contraction, poleNormalProduct_same, hfusion,
    rootSummand_iterate w hw, coeff_laurentRescale, phaseUnit_zpow]
  rw [show -a + -b = -(a + b) by ring]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rw [← mul_assoc, ← map_mul, ← zpow_add₀ (Coefficients.root_ne_zero w hw)]
  congr 2
  ring

/-- Summing all tensor positions and restoring the field normalization gives
the coefficient 1/12 multiplying the fused root mode. -/
theorem firstRoot_delta_sum_fusion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p q : ℕ) (β : Lattice)
    (hfusion : (coxeter^[p]) (simpleRoot 0) + simpleRoot 0 = (coxeter^[q]) β)
    (f : Space K) (a b : ℤ) :
    (1 / 144 : K) • ∑ j : Fin 3,
      contract (fun n : ℤ => MvPolynomial.C (w ^ (-(p : ℤ) * n)))
        (normalProduct w j j f) (-a) (-b) =
      (w ^ (((q : ℤ) - p) * a + q * b) / 12) • rootMode w β (a + b) f := by
  simp_rw [firstRoot_delta_fusion w hw p q β hfusion]
  rw [← Finset.smul_sum, sum_rootSummand_coeff, smul_smul, smul_smul]
  congr 1
  ring

theorem firstRoot_delta_four (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    (1 / 144 : K) • ∑ j : Fin 3,
      contract (fun n : ℤ => MvPolynomial.C (w ^ (-4 * n)))
        (normalProduct w j j f) (-a) (-b) =
      (w ^ (-2 * a + 2 * b) / 12) • mode w (a + b) f := by
  have h := firstRoot_delta_sum_fusion w hw 4 2 (simpleRoot 0)
    RootData.first_fusion_four f a b
  norm_num only [Nat.cast_ofNat, rootMode_first] at h
  exact h

theorem firstRoot_delta_eight (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    (1 / 144 : K) • ∑ j : Fin 3,
      contract (fun n : ℤ => MvPolynomial.C (w ^ (-8 * n)))
        (normalProduct w j j f) (-a) (-b) =
      (w ^ (2 * a - 2 * b) / 12) • mode w (a + b) f := by
  have h := firstRoot_delta_sum_fusion w hw 8 10 (simpleRoot 0)
    RootData.first_fusion_eight f a b
  norm_num only [Nat.cast_ofNat, rootMode_first] at h
  have hp : w ^ (2 * a + 10 * b) = w ^ (2 * a - 2 * b) := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  rw [hp] at h
  exact h

theorem firstRoot_delta_five (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    (1 / 144 : K) • ∑ j : Fin 3,
      contract (fun n : ℤ => MvPolynomial.C (w ^ (-5 * n)))
        (normalProduct w j j f) (-a) (-b) =
      (w ^ (4 * a + 9 * b) / 12) • secondRootMode w (a + b) f := by
  have h := firstRoot_delta_sum_fusion w hw 5 9 (simpleRoot 1)
    RootData.first_fusion_five f a b
  norm_num only [Nat.cast_ofNat] at h
  exact h

theorem firstRoot_delta_seven (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    (1 / 144 : K) • ∑ j : Fin 3,
      contract (fun n : ℤ => MvPolynomial.C (w ^ (-7 * n)))
        (normalProduct w j j f) (-a) (-b) =
      (w ^ (9 * a + 4 * b) / 12) • secondRootMode w (a + b) f := by
  have h := firstRoot_delta_sum_fusion w hw 7 4 (simpleRoot 1)
    RootData.first_fusion_seven f a b
  norm_num only [Nat.cast_ofNat] at h
  have hp : w ^ (-3 * a + 4 * b) = w ^ (9 * a + 4 * b) := by
    apply Coefficients.zpow_eq_of_mod w hw
    omega
  rw [hp] at h
  exact h

end KanadeRussell.Tsuchioka.Fock
