import KanadeRussell.Infra.CubicSeriesAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Extracting the cubic comparison directly from three cube identities. -/
open PowerSeries
namespace KanadeRussell.Infra.CubicSeriesAlgebra
open SecondCoefficient
variable {R : Type*} [CommRing R]

theorem coeff_one_cube (f : PowerSeries R) :
    coeff 1 (f^3) = 3*(constantCoeff f)^2*coeff 1 f := by
  rw [show f^3 = f*f*f by ring]
  simp only [coeff_one_mul, map_mul]
  ring

theorem coeff_two_cube (f : PowerSeries R) :
    coeff 2 (f^3) = 3*(constantCoeff f)^2*coeff 2 f+
      3*constantCoeff f*(coeff 1 f)^2 := by
  rw [show f^3 = f*f*f by ring]
  simp only [coeff_two_mul, coeff_one_mul, map_mul]
  ring

private theorem expression_constant (a z : R) (H B D : PowerSeries R)
    (hH : constantCoeff H = 0) (hB : constantCoeff B = 1) (hD : constantCoeff D = 1) :
    constantCoeff (expression a z H B D) = 3*(z^2-z) := by
  simp [expression, hH, hB, hD]
  ring

/-- This theorem uses identities of actual power series, not presumed derivative values. -/
theorem square_of_cube_relations (a w s t e : R) (H B D f f1 f2 K : PowerSeries R)
    (h6 : IsUnit (6:R)) (he : IsUnit e) (hw : w^2+w+1 = 0)
    (hH0 : constantCoeff H = 0) (hH1 : coeff 1 H = -3)
    (hB : constantCoeff B = 1) (hD : constantCoeff D = 1)
    (hpair1 : coeff 1 (B*D) = 0) (hpair2 : coeff 2 (B*D) = -9*s)
    (hf0 : constantCoeff f = 0)
    (hcube : f^3 = PowerSeries.C e*expression a 1 H B D)
    (hcube1 : f1^3 = PowerSeries.C e*expression a w H B D)
    (hcube2 : f2^3 = PowerSeries.C e*expression a (w^2) H B D)
    (hprod : f1*f2 = -PowerSeries.C (w^2)*(1+X)*K)
    (hK1 : coeff 1 K = 0) (hK2 : coeff 2 K = -constantCoeff K*t) : a^2 = 9*s-3*t := by
  have hcenter : coeff 1 (expression a 1 H B D) = 0 := by
    have hh := congrArg (coeff 1) hcube
    rw [coeff_one_cube, hf0, coeff_C_mul] at hh
    have hz : e*coeff 1 (expression a 1 H B D) = e*0 := by simpa using hh.symm
    exact he.mul_left_cancel hz
  have hw3 : w^3 = 1 := by linear_combination (w-1)*hw
  have hw4 : w^4 = w := by rw [show (4:ℕ)=3+1 by decide, pow_succ, hw3, one_mul]
  have hw6 : w^6 = 1 := by rw [show (6:ℕ)=3*2 by decide, pow_mul, hw3, one_pow]
  have hm : PowerSeries.C (e^2)*
      (expression a w H B D*expression a (w^2) H B D) = -(1+X)^3*K^3 := by
    calc
      _ = (PowerSeries.C e*expression a w H B D)*(PowerSeries.C e*expression a (w^2) H B D) := by rw [map_pow]; ring
      _ = f1^3*f2^3 := by rw [hcube1,hcube2]
      _ = (f1*f2)^3 := by ring
      _ = (-PowerSeries.C (w^2)*(1+X)*K)^3 := by rw [hprod]
      _ = -PowerSeries.C (w^6)*(1+X)^3*K^3 := by simp only [map_pow]; ring
      _ = _ := by rw [hw6,map_one]; ring
  have ht0 : constantCoeff (expression a w H B D*expression a (w^2) H B D) = 27 := by
    rw [map_mul, expression_constant a w H B D hH0 hB hD,
      expression_constant a (w^2) H B D hH0 hB hD]
    rw [← pow_mul, show (2*2:ℕ)=4 by decide, hw4]
    linear_combination (-9*(w^2-3*w+3))*hw
  have hk : -(constantCoeff K)^3 = 27*e^2 := by
    have hh := congrArg constantCoeff hm
    simp only [map_mul, constantCoeff_C, ht0, map_neg, map_pow, map_add, map_one,
      constantCoeff_X] at hh
    linear_combination -hh
  have hroot : coeff 2 (expression a w H B D*expression a (w^2) H B D) = 27*(3-3*t) := by
    have hh := congrArg (coeff 2) hm
    rw [coeff_C_mul] at hh
    simp only [map_neg, coeff_two_mul, coeff_one_cube, coeff_two_cube, map_pow,
      map_add, map_one, constantCoeff_X, coeff_X, coeff_one, hK1, hK2] at hh
    norm_num at hh
    have hr : e^2*coeff 2 (expression a w H B D*expression a (w^2) H B D) =
        e^2*(27*(3-3*t)) := by
      rw [coeff_two_mul]
      linear_combination hh + (3-3*t)*hk
    exact (he.pow 2).mul_left_cancel hr
  exact square_of_coefficients a w s t H B D h6 hw hH0 hH1 hB hD hpair1 hpair2 hcenter hroot

end KanadeRussell.Infra.CubicSeriesAlgebra
