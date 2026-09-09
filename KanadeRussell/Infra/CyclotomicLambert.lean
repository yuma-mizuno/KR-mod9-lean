import KanadeRussell.Infra.JacobiJets
set_option backward.isDefEq.respectTransparency false

/-! Root-of-unity pairing of Lambert summands with every denominator justified. -/
namespace KanadeRussell.Infra.CyclotomicLambert
variable {R : Type*} [CommRing R]

theorem denominator_factor (w x : R) (hw : w^2+w+1 = 0) :
    (1-x)*(1-w*x)*(1-w^2*x) = 1-x^3 := by
  linear_combination (-x*(x-1)*(w*x-x-1))*hw

theorem numerator_pair (w x : R) (hw : w^2+w+1 = 0) :
    (1-x)^2*(w*x*(1-w^2*x)^2+w^2*x*(1-w*x)^2) =
      -x*((1-w*x)*(1-w^2*x))^2+9*x^3 := by
  linear_combination x*(w^4*x^4-4*w^3*x^3+w^3*x^2+w^2*x^2+
    10*w*x^2-4*w*x-9*x^2+1)*hw

/-- The rational Lambert pairing is valid whenever the four displayed denominators are units. -/
theorem pair (w x : R) (hw : w^2+w+1 = 0)
    (h1 : IsUnit (1-x)) (h3 : IsUnit (1-x^3))
    (hw1 : IsUnit (1-w*x)) (hw2 : IsUnit (1-w^2*x)) :
    w*x*bInv (1-w*x)^2+w^2*x*bInv (1-w^2*x)^2 =
      -x*bInv (1-x)^2+9*x^3*bInv (1-x^3)^2 := by
  have hf := denominator_factor w x hw
  have hleft : (1-x^3)^2*(w*x*bInv (1-w*x)^2+w^2*x*bInv (1-w^2*x)^2) =
      (1-x)^2*(w*x*(1-w^2*x)^2+w^2*x*(1-w*x)^2) := by
    calc
      _ = (1-x)^2*(w*x*(1-w^2*x)^2*((1-w*x)*bInv (1-w*x))^2+
        w^2*x*(1-w*x)^2*((1-w^2*x)*bInv (1-w^2*x))^2) := by rw [← hf]; ring
      _ = _ := by rw [hw1.mul_bInv_cancel, hw2.mul_bInv_cancel]; ring
  have hright : (1-x^3)^2*(-x*bInv (1-x)^2+9*x^3*bInv (1-x^3)^2) =
      -x*((1-w*x)*(1-w^2*x))^2+9*x^3 := by
    calc
      _ = -x*(1-x^3)^2*bInv (1-x)^2+9*x^3*((1-x^3)*bInv (1-x^3))^2 := by ring
      _ = -x*(1-x^3)^2*bInv (1-x)^2+9*x^3 := by rw [h3.mul_bInv_cancel]; ring
      _ = -x*((1-w*x)*(1-w^2*x))^2*((1-x)*bInv (1-x))^2+9*x^3 := by rw [← hf]; ring
      _ = _ := by rw [h1.mul_bInv_cancel]; ring
  apply (h3.pow 2).mul_left_cancel
  rw [hleft, hright, numerator_pair w x hw]

end KanadeRussell.Infra.CyclotomicLambert
