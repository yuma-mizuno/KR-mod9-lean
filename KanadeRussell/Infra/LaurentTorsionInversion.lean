import KanadeRussell.Infra.LaurentTorsionCombinations
import KanadeRussell.Infra.JacobiInversion
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Infra.LaurentTorsionInversion
open LaurentTorsionCombinations LaurentLambertTails JacobiFirstJet JacobiJets
open Product.CubicScalarExtension (L scalar p)
local instance : UniformSpace ℂ := ⊥

private theorem order_twelve (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0) : w^12=1 := by
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
    TwelfthRootTorsionWeights.pow_twelve (w : ℂ) hw

private theorem reflected_power (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0)
    (j : ℕ) (hj : j < 12) : w^(12-j)=(w^j)⁻¹ := by
  have he : w^(12-j)*w^j=1 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega), order_twelve w hw]
  exact eq_inv_of_mul_eq_one_left he

private theorem denominator_unit (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0)
    (j : ℕ) (hj : 1 ≤ j) (hj12 : j < 12) : IsUnit (1-(constantUnit (w^j) : L)) := by
  simpa only [constantUnit_val, Units.val_pow_eq_pow_val, map_pow] using
    TwelfthRootJacobiArguments.mapped_torsion_denominator_isUnit scalar (w : ℂ) hw j hj hj12

/-- The shared actual centered logarithmic jet is odd in the twelfth-root index. -/
theorem centeredZ_reflection (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0)
    (j : ℕ) (hj : 1 ≤ j) (hj12 : j < 12) : centeredZ w (12-j) = -centeredZ w j := by
  have hi : constantUnit (w^(12-j))=(constantUnit (w^j))⁻¹ := by
    rw [reflected_power w hw j hj12]
    exact map_inv (Units.map scalar.toMonoidHom) _
  simp only [centeredZ, hi, JacobiInversion.logarithmic_inv p _ (denominator_unit w hw j hj hj12)]
  have hh : (2 : L)*scalar (1/2)=1 := by
    rw [← map_ofNat scalar 2, ← map_mul]
    norm_num
  linear_combination -hh

/-- The actual centered elliptic function is even in the twelfth-root index. -/
theorem centeredP_reflection (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0)
    (j : ℕ) (hj : 1 ≤ j) (hj12 : j < 12) : centeredP w (12-j) = centeredP w j := by
  have hi : constantUnit (w^(12-j))=(constantUnit (w^j))⁻¹ := by
    rw [reflected_power w hw j hj12]
    exact map_inv (Units.map scalar.toMonoidHom) _
  have ho : (constantUnit (w^j))^12=1 := by
    have hh : (w^j)^12=1 := by
      rw [← pow_mul, Nat.mul_comm j 12, pow_mul, order_twelve w hw, one_pow]
    change (Units.map scalar.toMonoidHom (w^j))^12=1
    rw [← map_pow, hh, map_one]
  simp only [centeredP, ellipticE, hi]
  rw [JacobiInversion.elliptic_inv_finite_order p _ (by decide : 12 ≠ 0) ho
    Product.CubicScalarExtension.p_nilpotent (denominator_unit w hw j hj hj12)]

/-- The order-two centered logarithmic jet vanishes. -/
theorem centeredZ_six (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0) : centeredZ w 6=0 := by
  have he : w^6=-1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using
      TwelfthRootTorsionWeights.pow_six (w : ℂ) hw
  have hi : constantUnit (w^6)=(-1 : Lˣ) := by
    rw [he]
    apply Units.ext
    simp [constantUnit]
  have h2 : IsUnit (2 : L) := by
    have h : IsUnit (2 : ℂ) := isUnit_iff_ne_zero.mpr (by norm_num)
    simpa only [map_ofNat] using h.map scalar
  have ha := JacobiInversion.logarithmic_neg_one_twice p h2
  have hh : (2 : L)*scalar (1/2)=1 := by
    rw [← map_ofNat scalar 2, ← map_mul]
    norm_num
  apply h2.mul_left_cancel
  simp only [centeredZ, hi, mul_sub, mul_zero]
  linear_combination ha-hh

end KanadeRussell.Infra.LaurentTorsionInversion
