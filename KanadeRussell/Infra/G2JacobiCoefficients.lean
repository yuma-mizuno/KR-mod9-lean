import KanadeRussell.Infra.A2JacobiCoefficients
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.G2JacobiCoefficients
open ThetaAddition

def coefficientEquiv : (ℤ × ℤ) × (ℤ × ℤ) ≃ (ℤ × ℤ) × (ℤ × ℤ) where
  toFun z := ((z.1.1-z.1.2-2*z.2.1+z.2.2,z.1.2-z.2.1-z.2.2),z.2)
  invFun z := ((z.1.1+z.1.2+3*z.2.1,z.1.2+z.2.1+z.2.2),z.2)
  left_inv := by rintro ⟨⟨m,n⟩,i,j⟩; dsimp; congr 2 <;> omega
  right_inv := by rintro ⟨⟨m,n⟩,i,j⟩; dsimp; congr 2 <;> omega

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def coefficient (p : Rˣ) (m n : ℤ) : R :=
  ∑' ij : ℤ × ℤ, A2JacobiCoefficients.coefficient p (m-n-2*ij.1+ij.2) (n-ij.1-ij.2) *
    A2JacobiCoefficients.coefficient p ij.1 ij.2

omit [T2Space R] in
theorem summable_coefficient (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n : ℤ) :
    Summable (fun ij : ℤ × ℤ => A2JacobiCoefficients.coefficient p
      (m-n-2*ij.1+ij.2) (n-ij.1-ij.2)*A2JacobiCoefficients.coefficient p ij.1 ij.2) := by
  have h := A2JacobiCoefficients.hasSum_triple_product p 1 1 hp
  simp only [one_zpow,Units.val_one,mul_one] at h
  have hh := coefficientEquiv.hasSum_iff.mpr (h.mul_of_nonarchimedean' h)
  exact hh.summable.prod_factor (m,n)

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
theorem monomial_transport (x y : Rˣ) (m n i j : ℤ) :
    x^(m-n-2*i+j)*(x*y)^(n-i-j) * ((x^3*y)^i*y^j) = x^m*y^n := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul,ofMul_zpow,ofMul_pow]
  module

omit [T2Space R] in
theorem hasSum_grouped_product (p x y : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    HasSum (fun mn : ℤ × ℤ => coefficient p mn.1 mn.2*(↑(x^mn.1*y^mn.2):R))
      ((jacobi p x*jacobi p (x*y)*jacobi p (x*(x*y))) *
        (jacobi p (x^3*y)*jacobi p y*jacobi p ((x^3*y)*y))) := by
  have h := (A2JacobiCoefficients.hasSum_triple_product p x (x*y) hp).mul_of_nonarchimedean'
    (A2JacobiCoefficients.hasSum_triple_product p (x^3*y) y hp)
  have hh := coefficientEquiv.hasSum_iff.mpr h
  apply hh.prod_fiberwise
  intro mn
  have hf := (summable_coefficient p hp mn.1 mn.2).hasSum.mul_right (↑(x^mn.1*y^mn.2):R)
  apply hf.congr_fun
  intro ij
  change (_ * (↑(x^(mn.1-mn.2-2*ij.1+ij.2)*(x*y)^(mn.2-ij.1-ij.2)):R)) *
    (_ * (↑((x^3*y)^ij.1*y^ij.2):R)) = _
  rw [mul_mul_mul_comm,← Units.val_mul,monomial_transport]
  rfl

omit [T2Space R] in
theorem hasSum_six_product (p x y : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    HasSum (fun mn : ℤ × ℤ => coefficient p mn.1 mn.2*(↑(x^mn.1*y^mn.2):R))
      (jacobi p x*jacobi p y*jacobi p (x*y)*jacobi p (x^2*y)*
        jacobi p (x^3*y)*jacobi p (x^3*y^2)) := by
  have h := hasSum_grouped_product p x y hp
  have h1 : x*(x*y)=x^2*y := by simp only [pow_two,mul_assoc]
  have h2 : (x^3*y)*y=x^3*y^2 := by simp only [pow_two,mul_assoc]
  rw [h1,h2] at h
  convert h using 1; ring
end KanadeRussell.Infra.G2JacobiCoefficients
