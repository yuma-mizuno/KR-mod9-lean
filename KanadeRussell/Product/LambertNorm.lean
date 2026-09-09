import KanadeRussell.Product.LambertDifferences
import KanadeRussell.Product.Reduction
set_option backward.isDefEq.respectTransparency false

/-! An exact Lambert-trace characterization of ProductNorm. The characterization
uses the proved Weierstrass differences and requires no cubic theta identity. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Product

noncomputable def lambertTrace : PowerSeries ℤ := lambert 1 - 4*lambert 3 + 3*lambert 9

/-- Sum of the three proved differences, with a common unit denominator. -/
theorem lambertTrace_theta :
    (E 3)^2 * P^2 * lambertTrace =
      q * (E 9)^6 * (thetaNumerator - 3*q*P^2) := by
  have h1 := lambert_difference_one
  have h2 := lambert_difference_two
  have h4 := lambert_difference_four
  have ht := lambert_residue_trace
  dsimp [P, lambertTrace, thetaNumerator] at *
  linear_combination (J 2)^2*(J 4)^2*h1 + (J 1)^2*(J 4)^2*h2 +
    (J 1)^2*(J 2)^2*h4 - (E 3)^2*(J 1*J 2*J 4)^2*ht

/-- ProductNorm is exactly one cleared Lambert trace identity. No BBG identity
is assumed in either direction. -/
theorem productNorm_iff_lambertTrace :
    ProductNorm ↔ (E 3)^2 * lambertTrace =
      q*a*(E 9)^3*E 3 - 3*q^2*(E 9)^6 := by
  rw [productNorm_iff_theta]
  have ht := lambertTrace_theta
  have hs := congrArg (fun z : PowerSeries ℤ => z^2) J_product
  have hres : E 3 * P^2 *
      ((E 3)^2*lambertTrace - (q*a*(E 9)^3*E 3 - 3*q^2*(E 9)^6)) =
      q*(E 9)^6 * (E 3*thetaNumerator - a*(E 1)^2*(E 9)^3) := by
    dsimp [P] at *
    linear_combination E 3*ht - q*a*(E 9)^3*hs
  have hl : E 3*P^2 ≠ 0 := ((isUnit_E 3 (by decide)).mul (isUnit_P.pow 2)).ne_zero
  have hr : q*(E 9)^6 ≠ 0 := mul_ne_zero (by simp [q]) ((isUnit_E 9 (by decide)).pow 6).ne_zero
  constructor
  · intro h
    rw [h, sub_self, mul_zero] at hres
    exact sub_eq_zero.mp ((mul_eq_zero.mp hres).resolve_left hl)
  · intro h
    rw [h, sub_self, mul_zero] at hres
    exact sub_eq_zero.mp ((mul_eq_zero.mp hres.symm).resolve_left hr)

/-- A sufficient pair of classical theta mechanisms: the square expansion at
q and q³, and the cleared trisection relation. The hypotheses remain explicit;
this theorem is not an unconditional proof of ProductNorm. -/
theorem productNorm_of_theta_relations (a₃ : PowerSeries ℤ)
    (hsq : a^2 = 1 + 12*lambert 1 - 36*lambert 3)
    (hsq₃ : a₃^2 = 1 + 12*lambert 3 - 36*lambert 9)
    (htri : (a-a₃)*E 3 = 6*q*(E 9)^3) : ProductNorm := by
  apply productNorm_iff_lambertTrace.mpr
  have h : (12 : PowerSeries ℤ) *
      ((E 3)^2*lambertTrace - (q*a*(E 9)^3*E 3 - 3*q^2*(E 9)^6)) = 0 := by
    dsimp [lambertTrace]
    linear_combination (E 3)^2*(hsq₃-hsq) + (E 3*(a+a₃)-6*q*(E 9)^3)*htri
  have hn : (12 : PowerSeries ℤ) ≠ 0 := by
    intro hz
    have hc := congrArg (PowerSeries.constantCoeff (R := ℤ)) hz
    norm_num only [map_ofNat, map_zero] at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hn)

end KanadeRussell.Product
