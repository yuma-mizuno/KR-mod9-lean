import KanadeRussell.Infra.G2JacobiCoefficients
import KanadeRussell.Infra.A2CoefficientRecurrences
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.G2JacobiCoefficients
open A2JacobiCoefficients
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

def longEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun z := (z.1,z.1-z.2+1)
  invFun z := (z.1,z.1-z.2+1)
  left_inv := by rintro ⟨i,j⟩; dsimp; congr 1; omega
  right_inv := by rintro ⟨i,j⟩; dsimp; congr 1; omega

theorem coefficient_short_reflection (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n : ℤ) :
    coefficient p (3*n-m+1) n = -coefficient p m n := by
  have h := (Equiv.prodComm ℤ ℤ).hasSum_iff.mpr (summable_coefficient p hp (3*n-m+1) n).hasSum
  apply h.unique
  apply ((summable_coefficient p hp m n).hasSum.neg).congr_fun
  rintro ⟨i,j⟩
  change A2JacobiCoefficients.coefficient p (3*n-m+1-n-2*j+i) (n-j-i)*
    A2JacobiCoefficients.coefficient p j i = _
  rw [show 3*n-m+1-n-2*j+i=(n-i-j)-(m-n-2*i+j)+1 by ring,
    show n-j-i=n-i-j by ring,coefficient_reflection p hp,
    coefficient_swap p i j,neg_mul]

theorem coefficient_long_reflection (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n : ℤ) :
    coefficient p m (m-n+1) = -coefficient p m n := by
  have h := longEquiv.hasSum_iff.mpr (summable_coefficient p hp m (m-n+1)).hasSum
  apply h.unique
  apply ((summable_coefficient p hp m n).hasSum.neg).congr_fun
  rintro ⟨i,j⟩
  change A2JacobiCoefficients.coefficient p (m-(m-n+1)-2*i+(i-j+1)) ((m-n+1)-i-(i-j+1))*
    A2JacobiCoefficients.coefficient p i (i-j+1) = _
  rw [show m-(m-n+1)-2*i+(i-j+1)=n-i-j by ring,
    show (m-n+1)-i-(i-j+1)=m-n-2*i+j by ring,
    coefficient_swap p (m-n-2*i+j) (n-i-j),coefficient_reflection_second p hp,mul_neg]

def twelveEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun z := (z.1+3,z.2-3)
  invFun z := (z.1-3,z.2+3)
  left_inv := by rintro ⟨i,j⟩; dsimp; congr 1 <;> omega
  right_inv := by rintro ⟨i,j⟩; dsimp; congr 1 <;> omega

theorem coefficient_translate_twelve (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n : ℤ) :
    coefficient p (m+12) n = (↑(p^(4*m-6*n+22)):R)*coefficient p m n := by
  have h := twelveEquiv.hasSum_iff.mpr (summable_coefficient p hp (m+12) n).hasSum
  apply h.unique
  apply ((summable_coefficient p hp m n).hasSum.mul_left (↑(p^(4*m-6*n+22)):R)).congr_fun
  rintro ⟨i,j⟩
  change A2JacobiCoefficients.coefficient p (m+12-n-2*(i+3)+(j-3)) (n-(i+3)-(j-3))*
    A2JacobiCoefficients.coefficient p (i+3) (j-3) = _
  rw [show m+12-n-2*(i+3)+(j-3)=(m-n-2*i+j)+3*1 by ring,
    show n-(i+3)-(j-3)=(n-i-j)+3*0 by ring,
    coefficient_translate p hp (m-n-2*i+j) (n-i-j) 1 0,
    show i+3=i+3*1 by ring,show j-3=j+3*(-1) by ring,
    coefficient_translate p hp i j 1 (-1)]
  rw [mul_mul_mul_comm,← Units.val_mul,← zpow_add]
  have he : ((4*(m-n-2*i+j)-2*(n-i-j)-2)*1+(4*(n-i-j)-2*(m-n-2*i+j)-2)*0+6*(1^2+0^2-1*0))+
      ((4*i-2*j-2)*1+(4*j-2*i-2)*(-1)+6*(1^2+(-1)^2-1*(-1)))=4*m-6*n+22 := by ring
  rw [he]
end KanadeRussell.Infra.G2JacobiCoefficients
