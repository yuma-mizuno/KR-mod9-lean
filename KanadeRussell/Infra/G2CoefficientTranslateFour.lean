import KanadeRussell.Infra.G2CoefficientEvaluation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.G2JacobiCoefficients
open ThetaAddition JacobiIntegerShift
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

theorem jacobi_four_shift (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (z k : ℤ) :
    jacobi (p^4) (p^(z+8*k)) =
      (↑(((-1:Rˣ)^k)*p^(-z*k-4*k*(k-1))):R)*jacobi (p^4) (p^z) := by
  have hp4 : IsTopologicallyNilpotent ((p^4:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 4 ≠ 0)
  have h := jacobi_shift (p^4) (p^z) k hp4
  have he : (p^4)^(2*k)*p^z=p^(z+8*k) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul,ofMul_zpow,ofMul_pow]
    module
  rw [he] at h
  rw [h]
  congr 2
  apply Additive.ofMul.injective
  simp only [shiftFactor,ofMul_mul,ofMul_zpow,ofMul_pow]
  module

theorem jacobi_triple_translate_four (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n : ℤ) :
    (jacobi (p^4) (p^(4-2*m+2*(n+4)))*jacobi (p^4) (p^(2*m-4*(n+4)+2))*
      jacobi (p^4) (p^(6-2*(n+4)))) =
    (↑(p^(6*m-12*n-26)):R)*(jacobi (p^4) (p^(4-2*m+2*n))*
      jacobi (p^4) (p^(2*m-4*n+2))*jacobi (p^4) (p^(6-2*n))) := by
  rw [show 4-2*m+2*(n+4)=(4-2*m+2*n)+8*1 by ring,
    show 2*m-4*(n+4)+2=(2*m-4*n+2)+8*(-2) by ring,
    show 6-2*(n+4)=(6-2*n)+8*(-1) by ring,
    jacobi_four_shift p hp _ 1,jacobi_four_shift p hp _ (-2),jacobi_four_shift p hp _ (-1)]
  have he : (((-1:Rˣ)^(1:ℤ))*p^(-(4-2*m+2*n)*1-4*1*(1-1))) *
      (((-1:Rˣ)^(-2:ℤ))*p^(-(2*m-4*n+2)*(-2)-4*(-2)*((-2)-1))) *
      (((-1:Rˣ)^(-1:ℤ))*p^(-(6-2*n)*(-1)-4*(-1)*((-1)-1))) = p^(6*m-12*n-26) := by
    have h2 : (-1:Rˣ)^(-2:ℤ)=1 := by norm_num [zpow_neg,zpow_ofNat]
    have h1 : (-1:Rˣ)^(-1:ℤ)= -1 := by norm_num [zpow_neg,zpow_ofNat]
    rw [zpow_one,h2,h1]
    calc
      _ = p^((-(4-2*m+2*n)*1-4*1*(1-1))+(-(2*m-4*n+2)*(-2)-4*(-2)*((-2)-1))+
          (-(6-2*n)*(-1)-4*(-1)*((-1)-1))) := by simp only [neg_mul,mul_neg,neg_neg,one_mul,mul_one]; rw [← zpow_add,← zpow_add]
      _ = _ := by congr 1; ring
  calc
    _ = (↑((((-1:Rˣ)^(1:ℤ))*p^(-(4-2*m+2*n)*1-4*1*(1-1))) *
      (((-1:Rˣ)^(-2:ℤ))*p^(-(2*m-4*n+2)*(-2)-4*(-2)*((-2)-1))) *
      (((-1:Rˣ)^(-1:ℤ))*p^(-(6-2*n)*(-1)-4*(-1)*((-1)-1)))):R)*
      (jacobi (p^4) (p^(4-2*m+2*n))*jacobi (p^4) (p^(2*m-4*n+2))*jacobi (p^4) (p^(6-2*n))) := by
        simp only [Units.val_mul]; ring
    _ = _ := by rw [he]

open A2CoefficientResidues
open scoped QTheory

theorem coefficient_translate_four (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n : ℤ) :
    coefficient p m (n+4) = (↑(p^(-2*m+4*n+6)):R)*coefficient p m n := by
  have hp4 : IsTopologicallyNilpotent ((p^4:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 4 ≠ 0)
  have hu : IsUnit (euler (p^4)) := isUnit_qPochhammerInf
    (hp4.pow (by decide : 2 ≠ 0)) (hp4.pow (by decide : 2 ≠ 0))
  apply hu.mul_left_cancel
  rw [mul_left_comm (euler (p^4)),G2CoefficientEvaluation.coefficient_evaluation p hp m (n+4),
    G2CoefficientEvaluation.coefficient_evaluation p hp m n]
  split_ifs with hm
  · rw [mul_zero]
  · rw [jacobi_triple_translate_four p hp m n]
    have he : ((-1:Rˣ)^(m%3)*p^(residueExponent (m-(n+4)) (n+4) (m/3) (m%3)))*
        p^(6*m-12*n-26) = p^(-2*m+4*n+6)*
        ((-1:Rˣ)^(m%3)*p^(residueExponent (m-n) n (m/3) (m%3))) := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul,ofMul_zpow,residueExponent]
      module
    calc
      _ = (↑(((-1:Rˣ)^(m%3)*p^(residueExponent (m-(n+4)) (n+4) (m/3) (m%3)))*
          p^(6*m-12*n-26)):R)*euler p^2*
          (jacobi (p^4) (p^(4-2*m+2*n))*jacobi (p^4) (p^(2*m-4*n+2))*jacobi (p^4) (p^(6-2*n))) := by
            simp only [Units.val_mul]; ring
      _ = _ := by rw [he]; simp only [Units.val_mul]; ring
end KanadeRussell.Infra.G2JacobiCoefficients
