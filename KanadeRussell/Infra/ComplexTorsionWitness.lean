import KanadeRussell.Tsuchioka.ComplexPhase
import KanadeRussell.Infra.TwelfthRootTorsionWeights

/-! A unit square root of the existing concrete Tsuchioka phase. This
discharges the square-root parameter in the actual Jacobi addition proof. -/
set_option autoImplicit false
namespace KanadeRussell.Infra

theorem exists_complex_torsion_units :
    ∃ w a : ℂˣ, (w : ℂ) = Tsuchioka.complexPhase ∧
      (w : ℂ)^4-(w : ℂ)^2+1=0 ∧ a^2=w := by
  have hw := Tsuchioka.complexPhase_relation
  have hw0 := TwelfthRootTorsionWeights.root_ne_zero Tsuchioka.complexPhase hw
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq Tsuchioka.complexPhase (by decide : 0 < 2)
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp only [zero_pow (by decide : 2 ≠ 0)] at ha
    exact hw0 ha.symm
  refine ⟨Units.mk0 Tsuchioka.complexPhase hw0, Units.mk0 a ha0, rfl, hw, ?_⟩
  apply Units.ext
  exact ha

end KanadeRussell.Infra
