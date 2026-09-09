import KanadeRussell.Product.Weierstrass
import KanadeRussell.Infra.BaseChange
import RogersRamanujan.RingTheory.LaurentSeriesRedo.Topology
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology MvLaurentSeries
open scoped DiscreteUniformity
namespace KanadeRussell.Product.LevelNine

theorem baseChange2_eq_expand (f : PowerSeries ℤ) :
    baseChange2 (R := ℤ) f = LaurentSeries₁.ofPowerSeries ℤ (expand 2 (by decide) f) := by
  let g := (LaurentSeries₁.ofPowerSeries ℤ).comp (expand 2 (by decide)).toRingHom
  have hg : Continuous g := LaurentSeries₁.coe_continuous.comp (Infra.continuous_expand 2 (by decide))
  have hx : g X = xPow () 2 := by
    change LaurentSeries₁.ofPowerSeries ℤ (expand 2 (by decide) (X : PowerSeries ℤ)) = _
    rw [expand_X]
    exact MvLaurentSeries.coe_X_pow () 2
  have h := eq_intEval g hg
  rw [hx] at h
  exact congrArg (fun F : PowerSeries ℤ →+* Laurent ℤ => F f) h.symm

theorem baseChange2_injective : Function.Injective (baseChange2 (R := ℤ)) := by
  intro f g h
  simp only [baseChange2_eq_expand] at h
  have he := LaurentSeries₁.coe_injective h
  apply PowerSeries.ext
  intro n
  have hc := congrArg (PowerSeries.coeff (2*n)) he
  simpa only [coeff_expand_mul] using hc

end KanadeRussell.Product.LevelNine
