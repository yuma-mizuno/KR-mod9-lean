import Mathlib
set_option backward.isDefEq.respectTransparency false

/-! Integer polynomial elimination for the symmetric-kernel proof of the A₂ square. -/
namespace KanadeRussell.Infra.CubicKernelAlgebra
variable {R : Type*} [CommRing R]

/-- Only the first cube coefficient and the symmetric sum of the second
coefficients are needed; no individual logarithmic derivatives are assumed. -/
theorem square_of_symmetric_jets (a u b c w s t : R) (h6 : IsUnit (6:R))
    (hw : w^2+w+1 = 0) (ha : a = 1-2*u) (hs : b+c-u^2 = -9*s)
    (he : (w^2-w)*((-a-w^2*(u+b)+w*(1-2*u+c))-
        (-a-w*(u+b)+w^2*(1-2*u+c))) +
      (-a+2*w^2-w+u)*(-a+2*w-w^2+u) = 9-9*t) : a^2 = 9*s-3*t := by
  have hz : (6:R)*(a^2-9*s+3*t) = 0 := by
    linear_combination 2*he - 2*(-2*a+2*u-w^2-w-2)*ha +
      2*w^2*(w-1)^2*hs -
      2*(9*s*w^2-27*s*w+27*s-u^2*w^2+3*u^2*w-3*u^2+
        u*w^2-3*u*w+6*u-3*w^2+10*w-11)*hw
  have hc := h6.mul_left_cancel (show (6:R)*(a^2-9*s+3*t) = (6:R)*0 by
    simpa only [mul_zero] using hz)
  linear_combination hc

end KanadeRussell.Infra.CubicKernelAlgebra
