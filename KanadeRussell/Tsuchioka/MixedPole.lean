import KanadeRussell.Tsuchioka.ModeResidues

/-! The mixed-position pole at ratio one fuses to the negative first root. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open PowerSeries FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorExponent_complement (i s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    tensorExponent (K := K) i s + tensorExponent i t = -tensorExponent i u := by
  have hc : (Finset.univ : Finset (Fin 3)) = {s, t, u} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    omega
  have h := sum_tensorExponent (K := K) i
  rw [hc, Finset.sum_insert (by simp [hst, hsu]),
    Finset.sum_insert (by simp [htu]), Finset.sum_singleton] at h
  linear_combination h

theorem creationLog_complement (s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    creationLog (K := K) s + creationLog t = -creationLog u := by
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_neg, creationLog, coeff_mk]
  by_cases hn : IsMode n
  · simp only [dif_pos hn]
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← add_mul, ← map_add, ← neg_mul, ← map_neg]
    congr 2
    rw [← add_div, ← mul_add, tensorExponent_complement i s t u hst hsu htu]
    ring
  · simp [hn]

theorem creation_complement (w : K) (s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    creation (K := K) s * creation t = rootCreation w (-simpleRoot 0) u := by
  change exponential (creationLog s) * exponential (creationLog t) =
    exponential (rootCreationLog w (-simpleRoot 0) u)
  rw [← exponential_add (constantCoeff_creationLog s) (constantCoeff_creationLog t),
    creationLog_complement s t u hst hsu htu, rootCreationLog_neg, rootCreationLog_first]

theorem poleAnnihilation_zero_complement (w : K) (s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    poleAnnihilation w (simpleRoot 0) (simpleRoot 0) s t 0 =
      rootAnnihilation w (-simpleRoot 0) u := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [poleAnnihilation, rootAnnihilation, MvPolynomial.eval₂Hom_C]
  · intro v
    simp only [poleAnnihilation, rootAnnihilation, MvPolynomial.eval₂Hom_X',
      zero_mul, zpow_zero, mul_one, RootData.rootWeight_first, RootData.rootWeight_neg]
    rw [tensorExponent_complement v.1 s t u hst hsu htu]
    congr 2
    ring

theorem laurentRescale_phase_zero (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : LaurentSeries (Space K)) :
    laurentRescale (phaseUnit w hw 0) f = f := by
  apply HahnSeries.ext
  funext n
  rw [coeff_laurentRescale, phaseUnit_zpow]
  simp

/-- At ratio one, distinct tensor positions produce the negative-root field
in the remaining tensor position. -/
theorem poleNormalProduct_zero_complement (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (s t u : Fin 3) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (f : Space K) :
    poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) s t 0 f =
      rootSummand w (-simpleRoot 0) u f := by
  rw [poleNormalProduct, laurentRescale_phase_zero,
    poleAnnihilation_zero_complement w s t u hst hsu htu]
  simp only [rootCreation_first]
  change (creation (K := K) s : LaurentSeries (Space K)) *
    (creation (K := K) t : LaurentSeries (Space K)) *
    rootAnnihilation w (-simpleRoot 0) u f =
    (rootCreation w (-simpleRoot 0) u : LaurentSeries (Space K)) *
      rootAnnihilation w (-simpleRoot 0) u f
  rw [← PowerSeries.coe_mul, creation_complement w s t u hst hsu htu]

/-- Each remaining tensor position occurs twice among the six ordered
distinct pairs. -/
theorem sum_mixed_pole_zero (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (f : Space K) :
    ∑ s : Fin 3, ∑ t : Fin 3,
      (if s = t then 0 else poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) s t 0 f) =
      (2 : K) • ∑ u : Fin 3, rootSummand w (-simpleRoot 0) u f := by
  simp only [Fin.sum_univ_three]
  norm_num only [Fin.reduceEq, ite_true, ite_false, add_zero, zero_add]
  rw [poleNormalProduct_zero_complement w hw 0 1 2 (by decide) (by decide) (by decide),
    poleNormalProduct_zero_complement w hw 0 2 1 (by decide) (by decide) (by decide),
    poleNormalProduct_zero_complement w hw 1 0 2 (by decide) (by decide) (by decide),
    poleNormalProduct_zero_complement w hw 1 2 0 (by decide) (by decide) (by decide),
    poleNormalProduct_zero_complement w hw 2 0 1 (by decide) (by decide) (by decide),
    poleNormalProduct_zero_complement w hw 2 1 0 (by decide) (by decide) (by decide),
    two_smul K]
  simp only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, if_false]
  ac_rfl

end KanadeRussell.Tsuchioka.Fock
