import Mathlib

/-! Finite algebraic elimination of twelve torsion addition relations.
The addition relations are explicit premises: this file does not assert the
Frobenius–Stickelberger identity for any actual theta or Lambert series. -/
set_option autoImplicit false
namespace KanadeRussell.Infra.TorsionAdditionCertificate
variable {R : Type*} [CommRing R]

/-- The exact denominator-cleared quadratic certificate, after oddness of Z
and evenness of P have reduced the torsion indices to 1,...,6. -/
theorem quadratic_certificate (z1 z2 z3 z4 z5 : R) :
    15*(2*z1-z2)^2 -6*(z1+z2-z3)^2 -6*(z1+z3-z4)^2
      -6*(z1+z4-z5)^2 -6*(z1+z5)^2 +9*(2*z2-z4)^2
      -6*(z2+z3-z5)^2 +18*(z2+z4)^2 +15*(z2+2*z5)^2
      +6*(2*z3)^2 -6*(z3+z4+z5)^2 -(3*z4)^2 =
        18*((z1+z5)^2+(-z1+2*z2+z5)^2) := by ring

variable (z1 z2 z3 z4 z5 p1 p2 p3 p4 p5 p6 : R)
variable
    (h11 : (2*z1-z2)^2 = 2*p1+p2)
    (h12 : (z1+z2-z3)^2 = p1+p2+p3)
    (h13 : (z1+z3-z4)^2 = p1+p3+p4)
    (h14 : (z1+z4-z5)^2 = p1+p4+p5)
    (h15 : (z1+z5)^2 = p1+p5+p6)
    (h22 : (2*z2-z4)^2 = 2*p2+p4)
    (h23 : (z2+z3-z5)^2 = p2+p3+p5)
    (h24 : (z2+z4)^2 = p2+p4+p6)
    (h25 : (z2+2*z5)^2 = p2+2*p5)
    (h33 : (2*z3)^2 = 2*p3+p6)
    (h34 : (z3+z4+z5)^2 = p3+p4+p5)
    (h44 : (3*z4)^2 = 3*p4)

include h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h44

/-- No integer cancellation is used in the commutative-ring conclusion. -/
theorem mixed_square_cleared :
    18*((z1+z5)^2+(-z1+2*z2+z5)^2) =
      6*(p1+9*p2-2*p3+p4+p5+3*p6) := by
  linear_combination 15*h11-6*h12-6*h13-6*h14-6*h15+9*h22-6*h23+
    18*h24+15*h25+6*h33-6*h34-h44

/-- The reduced normalization is valid when 6 is a unit. -/
theorem mixed_square_of_isUnit_six (h6 : IsUnit (6 : R)) :
    3*((z1+z5)^2+(-z1+2*z2+z5)^2) = p1+9*p2-2*p3+p4+p5+3*p6 := by
  apply h6.mul_left_cancel
  have h := mixed_square_cleared z1 z2 z3 z4 z5 p1 p2 p3 p4 p5 p6
    h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h44
  convert h using 1; ring

end KanadeRussell.Infra.TorsionAdditionCertificate
