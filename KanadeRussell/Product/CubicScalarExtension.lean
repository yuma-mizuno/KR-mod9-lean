import KanadeRussell.Product.LaurentSubstitution
import KanadeRussell.Infra.LambertUnitArgument
set_option backward.isDefEq.respectTransparency false

/-! A faithful Laurent coefficient extension containing a primitive cube root.
The coefficient topology is formal and discrete; no analytic continuation is used. -/
open PowerSeries PowerSeries.WithPiTopology MvLaurentSeries
open scoped DiscreteUniformity
namespace KanadeRussell.Product.CubicScalarExtension

abbrev L := MvLaurentSeries Unit ℂ
noncomputable def scalar : ℂ →+* L := (LaurentSeries₁.ofPowerSeries ℂ).comp PowerSeries.C
noncomputable def omega : ℂ := Complex.exp (2*Real.pi*Complex.I/3)
noncomputable def w : L := scalar omega
noncomputable def p : Lˣ := xPowUnits () 1
noncomputable def eval : PowerSeries ℤ →+* L := intEval ((p:L)^2)

theorem omega_primitive : IsPrimitiveRoot omega 3 :=
  Complex.isPrimitiveRoot_exp 3 (by decide)

theorem omega_relation : omega^2+omega+1 = 0 := by
  have hh := omega_primitive.geom_sum_eq_zero (by decide : 1 < 3)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one] at hh
  linear_combination hh

theorem w_relation : w^2+w+1 = 0 := by
  have hh := congrArg scalar omega_relation
  simpa only [map_add, map_pow, map_one, map_zero, w] using hh

theorem w_cube : w^3 = 1 := by
  have hh := congrArg scalar omega_primitive.pow_eq_one
  simpa only [map_pow, map_one, w] using hh

theorem isUnit_w : IsUnit w := by
  have hw : IsUnit omega := isUnit_iff_ne_zero.mpr (omega_primitive.ne_zero (by decide))
  exact hw.map scalar

theorem isUnit_one_sub_w : IsUnit (1-w) := by
  have hh : IsUnit (1-omega) := isUnit_iff_ne_zero.mpr
    (sub_ne_zero.mpr (Ne.symm (omega_primitive.ne_one (by decide))))
  simpa only [map_sub, map_one, w] using hh.map scalar

theorem isUnit_six : IsUnit (6:L) := by
  have hh : IsUnit (6:ℂ) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using hh.map scalar

theorem p_nilpotent : IsTopologicallyNilpotent (p:L) :=
  (isTopologicallyNilpotent_xPow_iff () 1).mpr (by decide)

theorem eval_continuous : Continuous eval := by unfold eval; fun_prop

theorem eval_eq_expand (f : PowerSeries ℤ) :
    eval f = LaurentSeries₁.ofPowerSeries ℂ
      (expand 2 (by decide) (PowerSeries.map (Int.castRingHom ℂ) f)) := by
  letI : UniformSpace ℂ := ⊥
  let g := (LaurentSeries₁.ofPowerSeries ℂ).comp
    ((expand 2 (by decide)).toRingHom.comp (PowerSeries.map (Int.castRingHom ℂ)))
  have hm : Continuous (PowerSeries.map (Int.castRingHom ℂ)) := by fun_prop
  have hexp : Continuous (expand 2 (by decide) (R:=ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro f
    rw [ContinuousAt, tendsto_iff_coeff_tendsto]
    intro n
    simp only [coeff_expand]
    split_ifs
    · exact (continuous_coeff ℂ (n/2)).continuousAt
    · exact tendsto_const_nhds
  have hg : Continuous g := by
    change Continuous (fun f : PowerSeries ℤ => LaurentSeries₁.ofPowerSeries ℂ
      (expand 2 (by decide) (PowerSeries.map (Int.castRingHom ℂ) f)))
    exact LaurentSeries₁.coe_continuous.comp (hexp.comp hm)
  have hx : g q = xPow () 2 := by
    change LaurentSeries₁.ofPowerSeries ℂ
      (expand 2 (by decide) (PowerSeries.map (Int.castRingHom ℂ) q)) = _
    rw [q, PowerSeries.map_X, expand_X]
    exact MvLaurentSeries.coe_X_pow () 2
  have hh := eq_intEval g hg
  rw [hx] at hh
  have hp : (p:L)^2 = xPow () 2 := by
    change (xPow () 1 : L)^2 = _
    rw [xPow_pow]
    norm_num
  rw [eval, hp]
  exact congrArg (fun F : PowerSeries ℤ →+* L => F f) hh.symm

/-- Equality in this coefficient extension implies equality of the original integer series. -/
theorem eval_injective : Function.Injective eval := by
  intro f g h
  simp only [eval_eq_expand] at h
  have he := LaurentSeries₁.coe_injective h
  apply PowerSeries.ext
  intro n
  have hh := congrArg (PowerSeries.coeff (2*n)) he
  simp only [coeff_expand_mul, coeff_map, Int.coe_castRingHom] at hh
  exact_mod_cast hh

end KanadeRussell.Product.CubicScalarExtension
