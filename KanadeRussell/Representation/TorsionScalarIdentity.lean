import KanadeRussell.Infra.LaurentTorsionCombinations

/-! Algebraic descent of the actual weighted torsion relation to the exact
root-denominator scalar identity through the proved faithful Laurent map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Infra Infra.LaurentTorsionCombinations Infra.LaurentLambertTails
open Infra.TwelfthRootTorsionWeights
open Product.CubicScalarExtension (L scalar)

theorem principalScalar_identity_of_torsion_square (w : ℂˣ)
    (hw : (w : ℂ)^4-(w : ℂ)^2+1=0)
    (hsquare : 3*((centeredZ w 1+centeredZ w 5)^2+
        (-centeredZ w 1+2*centeredZ w 2+centeredZ w 5)^2) =
      centeredP w 1+9*centeredP w 2-2*centeredP w 3+
        centeredP w 4+centeredP w 5+3*centeredP w 6) :
    (principalScalarT (K := ℂ))^2+2 • principalScalarT+3 • principalScalarU^2 =
      PowerSeries.map (Int.castRingHom ℂ)
        (2 • Product.lambert 1+6 • Product.lambert 3+4 • Product.lambert 4-
          24 • Product.lambert 6-12 • Product.lambert 12) := by
  have hi : (scalar ((w : ℂ)^3))^2 = -1 := by
    rw [← map_pow, square_imaginary (w : ℂ) hw, map_neg, map_one]
  have hq : (scalar (2*(w : ℂ)^2-1))^2 = -3 := by
    rw [← map_pow, square_sqrt_neg_three (w : ℂ) hw, map_neg, map_ofNat]
  have hZ : (centeredZ w 1+centeredZ w 5)^2 = -4*(1+eval2 principalScalarT)^2 := by
    rw [centeredZ_T w hw]
    simp only [mul_pow, hi]
    ring
  have hU : (-centeredZ w 1+2*centeredZ w 2+centeredZ w 5)^2 =
      -12*(eval2 principalScalarU)^2 := by
    rw [centeredZ_U w hw]
    simp only [mul_pow, hq]
    ring
  have hE := ellipticE_combination w hw
  have hc : scalar (-157/12)+13*scalar (1/12) = (-12 : L) := by
    have h := congrArg scalar (by norm_num : (-157/12 : ℂ)+13*(1/12) = -12)
    simpa only [map_add, map_mul, map_ofNat, map_neg] using h
  have h12 : IsUnit (12 : L) := by
    simpa only [map_ofNat] using
      (show IsUnit (12 : ℂ) from isUnit_iff_ne_zero.mpr (by norm_num)).map scalar
  apply eval2_injective
  apply h12.mul_left_cancel
  rw [hZ,hU] at hsquare
  simp only [centeredP, central_lambertTail] at hsquare
  simp only [map_add, map_sub, map_mul, map_pow, nsmul_eq_mul, map_natCast]
    at hE hsquare ⊢
  linear_combination -hsquare-hE-hc

end KanadeRussell.Representation
