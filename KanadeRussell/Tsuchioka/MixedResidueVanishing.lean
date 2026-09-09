import KanadeRussell.Tsuchioka.MixedPoleSupport
import KanadeRussell.Tsuchioka.ResidueMaps

/-! Vanishing of the two mixed sixth-root residues in the partial mode relations. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem normalResidue_delta_phase (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (s t : Fin 3) (f : Space K) (a b : ℤ) :
    normalResidue w s t f a b (Scalar.delta (w ^ (-p))) =
      MvPolynomial.C (w ^ (-p * a)) *
        (poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) s t p f).coeff (-(a + b)) := by
  have h := normalProduct_delta_contraction w hw s t f p (-a) (-b)
  rw [show p * (-a) = -p * a by ring, show -a + -b = -(a + b) by ring] at h
  simpa only [normalResidue_apply, scalarContract, Scalar.delta, phaseUnit_zpow,
    ← zpow_mul] using h

theorem mixedPoleSum_coeff (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (f : Space K) (d : ℤ) :
    (mixedPoleSum w hw p f).coeff d =
      ∑ s : Fin 3, ∑ t : Fin 3, if s = t then 0 else
        (poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) s t p f).coeff d := by
  simp only [mixedPoleSum, HahnSeries.coeff_sum]
  congr 1
  funext s
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> rfl

theorem mixedResidue_delta_phase (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (f : Space K) (a b : ℤ) :
    mixedResidue w f a b (Scalar.delta (w ^ (-p))) =
      (1 / 144 : K) •
        (MvPolynomial.C (w ^ (-p * a)) * (mixedPoleSum w hw p f).coeff (-(a + b))) := by
  rw [mixedResidue_apply, mixedPoleSum_coeff]
  simp only [normalResidue_delta_phase w hw, Finset.mul_sum, mul_ite, mul_zero]

theorem mixedResidue_delta_phase_zero (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (f : Space K) (a b : ℤ) (hab : ¬3 ∣ a + b) :
    mixedResidue w f a b (Scalar.delta (w ^ (-p))) = 0 := by
  rw [mixedResidue_delta_phase w hw, mixedPoleSum_coeff_zero w hw p hp f
    (-(a + b)) (by simpa only [dvd_neg] using hab), mul_zero, smul_zero]

theorem mixedResidue_delta_two (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) (hab : ¬3 ∣ a + b) :
    mixedResidue w f a b (Scalar.delta (w ^ (-2 : ℤ))) = 0 :=
  mixedResidue_delta_phase_zero w hw 2 (Or.inl rfl) f a b hab

theorem mixedResidue_delta_neg_two (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) (hab : ¬3 ∣ a + b) :
    mixedResidue w f a b (Scalar.delta (w ^ 2)) = 0 := by
  simpa only [neg_neg, zpow_ofNat] using
    mixedResidue_delta_phase_zero w hw (-2) (Or.inr rfl) f a b hab

end KanadeRussell.Tsuchioka.Fock
