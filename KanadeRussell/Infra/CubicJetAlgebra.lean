import Mathlib
set_option backward.isDefEq.respectTransparency false

/-! Exact algebra used after the first two coefficients of cubic Jacobi dissection. -/
namespace KanadeRussell.Infra.CubicJetAlgebra
variable {R : Type*} [CommRing R]

/-- Second-coefficient elimination at a primitive cube root, with v²=-3.
All coefficient identities are explicit premises; this is a polynomial lemma. -/
theorem square_of_jets (a x y d v s t : R) (h6 : IsUnit (6:R))
    (hv : v^2 = -3)
    (hx : 6*x = 1-a)
    (hy : y = x^2-s)
    (hd : 6*d = 3-a*v)
    (he : -2*v*(9*d^2-3*t) = -6*a-3-5*v+(18+6*v)*x-18*v*y) :
    a^2 = 9*s-3*t := by
  have hz : 4*v*(a^2-9*s+3*t) = 0 := by
    linear_combination 2*he + v*(6*d+3-a*v)*hd - 36*v*hy +
      (-6*v*x+v+a*v+6)*hx + a*(a*v-6)*hv
  have hh : (6:R)^2*(a^2-9*s+3*t) = 0 := by
    linear_combination -3*v*hz + 12*(a^2-9*s+3*t)*hv
  have hc := (h6.pow 2).mul_left_cancel (show (6:R)^2*(a^2-9*s+3*t) = (6:R)^2*0 by
    simpa only [mul_zero] using hh)
  linear_combination hc

/-- Cleared Lambert normalization yields the required A₂ square expansion. -/
theorem square_of_lambert_jets (a x y d v t l l3 : R) (h6 : IsUnit (6:R))
    (hv : v^2 = -3)
    (hx : 6*x = 1-a)
    (hy : y = x^2-(l-l3))
    (hd : 6*d = 3-a*v)
    (ht : 3*t = -1-3*l+27*l3)
    (he : -2*v*(9*d^2-3*t) = -6*a-3-5*v+(18+6*v)*x-18*v*y) :
    a^2 = 1+12*l-36*l3 := by
  have hh := square_of_jets a x y d v (l-l3) t h6 hv hx hy hd he
  linear_combination hh - ht

end KanadeRussell.Infra.CubicJetAlgebra
