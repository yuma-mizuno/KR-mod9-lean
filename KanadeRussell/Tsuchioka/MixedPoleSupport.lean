import KanadeRussell.Tsuchioka.MixedPoleCycle

/-! The mixed-pole tensor sum has only total degrees divisible by three. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

noncomputable def mixedPoleSum (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (f : Space K) : LaurentSeries (Space K) :=
  ∑ s : Fin 3, ∑ t : Fin 3,
    if s = t then 0 else poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) s t p f

theorem mixedPoleSum_eq_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (f : Space K) :
    mixedPoleSum w hw p f =
      (poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) 0 1 p f +
        poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) 1 2 p f +
        poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) 2 0 p f) +
      (poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) 1 0 p f +
        poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) 0 2 p f +
        poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) 2 1 p f) := by
  simp only [mixedPoleSum, Fin.sum_univ_three, ite_true,
    show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    if_false, zero_add, add_zero]
  abel

theorem mixedPoleSum_rescale (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (f : Space K) :
    laurentRescale (phaseUnit w hw (2 * p)) (mixedPoleSum w hw p f) =
      mixedPoleSum w hw p f := by
  simp only [mixedPoleSum_eq_six, map_add]
  rw [poleNormalProduct_cyclic w hw p hp 0 1 2 (by decide) (by decide) (by decide),
    poleNormalProduct_cyclic w hw p hp 1 2 0 (by decide) (by decide) (by decide),
    poleNormalProduct_cyclic w hw p hp 2 0 1 (by decide) (by decide) (by decide),
    poleNormalProduct_cyclic w hw p hp 1 0 2 (by decide) (by decide) (by decide),
    poleNormalProduct_cyclic w hw p hp 0 2 1 (by decide) (by decide) (by decide),
    poleNormalProduct_cyclic w hw p hp 2 1 0 (by decide) (by decide) (by decide)]
  abel

theorem mixed_cycle_phase_ne_one (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (d : ℤ) (hd : ¬3 ∣ d) :
    w ^ (-(2 * p) * d) ≠ 1 := by
  intro he
  obtain ⟨k, hk⟩ := ((Coefficients.primitive_root w hw).zpow_eq_one_iff_dvd
    (-(2 * p) * d)).mp he
  apply hd
  rcases hp with rfl | rfl
  · exact ⟨-k, by omega⟩
  · exact ⟨k, by omega⟩

/-- The source's mixed-pole vanishing, on every polynomial input. -/
theorem mixedPoleSum_coeff_zero (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (f : Space K) (d : ℤ) (hd : ¬3 ∣ d) :
    (mixedPoleSum w hw p f).coeff d = 0 := by
  have hc := congrArg (fun F : LaurentSeries (Space K) => F.coeff d)
    (mixedPoleSum_rescale w hw p hp f)
  rw [coeff_laurentRescale, phaseUnit_zpow] at hc
  have hz : MvPolynomial.C (w ^ (-(2 * p) * d) - 1) * (mixedPoleSum w hw p f).coeff d = 0 := by
    rw [map_sub, map_one, sub_mul, one_mul, hc, sub_self]
  have hne : (MvPolynomial.C (w ^ (-(2 * p) * d) - 1) : Space K) ≠ 0 := by
    intro h
    have he : w ^ (-(2 * p) * d) - 1 = 0 :=
      (MvPolynomial.C_injective _ _).eq_iff.mp (by simpa only [map_zero] using h)
    exact mixed_cycle_phase_ne_one w hw p hp d hd (sub_eq_zero.mp he)
  exact (mul_eq_zero.mp hz).resolve_left hne

end KanadeRussell.Tsuchioka.Fock
