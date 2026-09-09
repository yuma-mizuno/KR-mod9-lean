import KanadeRussell.Tsuchioka.MixedCreationCycle

/-! Cyclic covariance of the complete mixed-pole normal product. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem poleAnnihilation_cyclic (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    (laurentRescale (phaseUnit w hw (2 * p))).comp
        (poleAnnihilation w (simpleRoot 0) (simpleRoot 0) s t p) =
      poleAnnihilation w (simpleRoot 0) (simpleRoot 0) t u p := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, poleAnnihilation, MvPolynomial.eval₂Hom_C,
      laurentRescale_C]
  · intro v
    simp only [RingHom.comp_apply, poleAnnihilation, MvPolynomial.eval₂Hom_X',
      RootData.rootWeight_first, mul_one, map_add, laurentRescale_C,
      laurentRescale_single, phaseUnit_zpow]
    rw [show -(2 * p) * -(v.2.val : ℤ) = (2 * p) * v.2.val by ring, ← map_mul]
    congr 2
    congr 1
    have h := mixed_phase_cycle w hw p hp v.2 v.1 s t u hst hsu htu
    linear_combination (contraction w v.2.val / 3) * h

theorem poleAnnihilation_cyclic_apply (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (f : Space K) :
    laurentRescale (phaseUnit w hw (2 * p))
        (poleAnnihilation w (simpleRoot 0) (simpleRoot 0) s t p f) =
      poleAnnihilation w (simpleRoot 0) (simpleRoot 0) t u p f :=
  RingHom.congr_fun (poleAnnihilation_cyclic w hw p hp s t u hst hsu htu) f

/-- Rescaling cycles the mixed tensor positions on every polynomial input. -/
theorem poleNormalProduct_cyclic (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) (hp : p = 2 ∨ p = -2) (s t u : Fin 3)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (f : Space K) :
    laurentRescale (phaseUnit w hw (2 * p))
        (poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) s t p f) =
      poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) t u p f := by
  simp only [poleNormalProduct, rootCreation_first]
  rw [map_mul, mixedCreation_laurent_cyclic w hw p hp s t u hst hsu htu,
    poleAnnihilation_cyclic_apply w hw p hp s t u hst hsu htu]

end KanadeRussell.Tsuchioka.Fock
