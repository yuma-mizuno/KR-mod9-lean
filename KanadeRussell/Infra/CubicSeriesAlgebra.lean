import KanadeRussell.Infra.CubicKernelAlgebra
import KanadeRussell.Infra.SecondCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Coefficient assembly of the cubic identity and its two symmetric kernels. -/
open PowerSeries
namespace KanadeRussell.Infra.CubicSeriesAlgebra
open SecondCoefficient
variable {R : Type*} [CommRing R]

noncomputable def expression (a w : R) (H B D : PowerSeries R) : PowerSeries R :=
  PowerSeries.C a*H-PowerSeries.C (3*w)*(1+X)*B+
    PowerSeries.C (3*w^2)*(1+X)*(1+X)*D

/-- The actual first two power-series coefficients imply the square identity. -/
theorem square_of_coefficients (a w s t : R) (H B D : PowerSeries R)
    (h6 : IsUnit (6:R)) (hw : w^2+w+1 = 0)
    (hH0 : constantCoeff H = 0) (hH1 : coeff 1 H = -3)
    (hB : constantCoeff B = 1) (hD : constantCoeff D = 1)
    (hpair1 : coeff 1 (B*D) = 0) (hpair2 : coeff 2 (B*D) = -9*s)
    (hcenter : coeff 1 (expression a 1 H B D) = 0)
    (hroot : coeff 2 (expression a w H B D * expression a (w^2) H B D) = 27*(3-3*t)) :
    a^2 = 9*s-3*t := by
  let u := coeff 1 B
  let b := coeff 2 B
  let c := coeff 2 D
  have hD1 : coeff 1 D = -u := by
    simp only [coeff_one_mul, hB, hD, mul_one] at hpair1
    dsimp only [u]
    linear_combination hpair1
  have hs : b+c-u^2 = -9*s := by
    simp only [coeff_two_mul, hB, hD, hD1, one_mul, mul_one] at hpair2
    dsimp only [b,c,u] at *
    linear_combination hpair2
  have hcentral : coeff 1 (expression a 1 H B D) = -3*a+3-6*u := by
    simp [expression, coeff_one_mul, hH1, hB, hD, hD1, u]
    ring
  have ha : a = 1-2*u := by
    rw [hcentral] at hcenter
    have hz : (6:R)*(a-1+2*u) = 0 := by linear_combination -2*hcenter
    have hh := h6.mul_left_cancel (show (6:R)*(a-1+2*u) = (6:R)*0 by simpa using hz)
    linear_combination hh
  have hw3 : w^3 = 1 := by linear_combination (w-1)*hw
  have hw4 : w^4 = w := by rw [show (4:ℕ)=3+1 by decide, pow_succ, hw3, one_mul]
  have hextract : coeff 2 (expression a w H B D * expression a (w^2) H B D) =
      9*((w^2-w)*((-a-w^2*(u+b)+w*(1-2*u+c))-
        (-a-w*(u+b)+w^2*(1-2*u+c)))+
      (-a+2*w^2-w+u)*(-a+2*w-w^2+u)) := by
    simp [expression, coeff_two_mul, coeff_one_mul, hH0, hH1, hB, hD, hD1,
      ← pow_mul, hw4]
    simp only [← map_pow, coeff_C, coeff_X]
    norm_num
    dsimp only [u,b,c]
    linear_combination 9*(coeff 1 B)*(2*a-w^2-w-2*(coeff 1 B)+
      (coeff 1 B)*(w^2+w+1))*hw
  have he : (w^2-w)*((-a-w^2*(u+b)+w*(1-2*u+c))-
        (-a-w*(u+b)+w^2*(1-2*u+c)))+
      (-a+2*w^2-w+u)*(-a+2*w-w^2+u) = 9-9*t := by
    rw [hextract] at hroot
    let E := (w^2-w)*((-a-w^2*(u+b)+w*(1-2*u+c))-
        (-a-w*(u+b)+w^2*(1-2*u+c)))+
      (-a+2*w^2-w+u)*(-a+2*w-w^2+u)
    have hz : (6:R)^2*(E-9+9*t) = 0 := by dsimp [E]; linear_combination 4*hroot
    have hh := (h6.pow 2).mul_left_cancel (show (6:R)^2*(E-9+9*t) = (6:R)^2*0 by simpa using hz)
    change E = _
    linear_combination hh
  exact CubicKernelAlgebra.square_of_symmetric_jets a u b c w s t h6 hw ha hs he

end KanadeRussell.Infra.CubicSeriesAlgebra
