import KanadeRussell.Infra.JacobiIntegerShift
import KanadeRussell.Infra.WeierstrassAddition

/-! Functional equations of the actual six-factor G2 Jacobi product. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.G2JacobiFunctionalEquations
open ThetaAddition JacobiIntegerShift
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def g2Product (p x y : Rˣ) : R :=
  jacobi p x*jacobi p y*jacobi p (x*y)*jacobi p (x^2*y)*
    jacobi p (x^3*y)*jacobi p (x^3*y^2)

/-- Short-root reflection, including the exact antisymmetric factor. -/
theorem short_reflection (p x y : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    g2Product p x⁻¹ (x^3*y) = -((x⁻¹ : Rˣ) : R)*g2Product p x y := by
  have h1 : x⁻¹*(x^3*y)=x^2*y := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv]
    module
  have h2 : x⁻¹^2*(x^3*y)=x*y := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv]
    module
  have h3 : x⁻¹^3*(x^3*y)=y := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv]
    module
  have h4 : x⁻¹^3*(x^3*y)^2=x^3*y^2 := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv]
    module
  rw [g2Product, h1, h2, h3, h4, jacobi_inv p x hp]
  unfold g2Product
  ring

/-- Long-root reflection, including the exact antisymmetric factor. -/
theorem long_reflection (p x y : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    g2Product p (x*y) y⁻¹ = -((y⁻¹ : Rˣ) : R)*g2Product p x y := by
  have h1 : (x*y)*y⁻¹=x := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    module
  have h2 : (x*y)^2*y⁻¹=x^2*y := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv]
    module
  have h3 : (x*y)^3*y⁻¹=x^3*y^2 := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv]
    module
  have h4 : (x*y)^3*y⁻¹^2=x^3*y := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv]
    module
  rw [g2Product, h1, h2, h3, h4, jacobi_inv p y hp]
  unfold g2Product
  ring

/-- Translation of both arguments, with the six exact Jacobi shift factors. -/
theorem shift_factored (p x y : Rˣ) (r s : ℤ)
    (hp : IsTopologicallyNilpotent (p : R)) :
    g2Product p (p^(2*r)*x) (p^(2*s)*y) =
      (↑(shiftFactor p x r*shiftFactor p y s*shiftFactor p (x*y) (r+s)*
        shiftFactor p (x^2*y) (2*r+s)*shiftFactor p (x^3*y) (3*r+s)*
          shiftFactor p (x^3*y^2) (3*r+2*s)) : R)*g2Product p x y := by
  have h1 : (p^(2*r)*x)*(p^(2*s)*y)=p^(2*(r+s))*(x*y) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul,ofMul_zpow]
    module
  have h2 : (p^(2*r)*x)^2*(p^(2*s)*y)=p^(2*(2*r+s))*(x^2*y) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul,ofMul_zpow,ofMul_pow]
    module
  have h3 : (p^(2*r)*x)^3*(p^(2*s)*y)=p^(2*(3*r+s))*(x^3*y) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul,ofMul_zpow,ofMul_pow]
    module
  have h4 : (p^(2*r)*x)^3*(p^(2*s)*y)^2=p^(2*(3*r+2*s))*(x^3*y^2) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul,ofMul_zpow,ofMul_pow]
    module
  rw [g2Product,h1,h2,h3,h4,jacobi_shift p x r hp,jacobi_shift p y s hp,
    jacobi_shift p (x*y) (r+s) hp,jacobi_shift p (x^2*y) (2*r+s) hp,
    jacobi_shift p (x^3*y) (3*r+s) hp,jacobi_shift p (x^3*y^2) (3*r+2*s) hp]
  simp only [Units.val_mul,g2Product]
  ring

/-- The translation giving the twelve-step recurrence in the first Fourier index. -/
theorem translate_twelve (p x y : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    g2Product p (p^(4 : ℤ)*x) (p^(-6 : ℤ)*y) =
      (↑(p^(-22 : ℤ)*x^(-12 : ℤ)) : R)*g2Product p x y := by
  have h := shift_factored p x y 2 (-3) hp
  norm_num only [Int.reduceMul,Int.reduceAdd] at h
  have hf : shiftFactor p x 2*shiftFactor p y (-3)*shiftFactor p (x*y) (-1)*
      shiftFactor p (x^2*y) 1*shiftFactor p (x^3*y) 3*shiftFactor p (x^3*y^2) 0 =
        p^(-22 : ℤ)*x^(-12 : ℤ) := by
    norm_num [shiftFactor,zpow_ofNat,zpow_neg,mul_zpow]
    apply Additive.ofMul.injective
    simp only [ofMul_mul,ofMul_pow,ofMul_inv]
    module
  rw [hf] at h
  exact h

/-- The translation giving the four-step recurrence in the second Fourier index. -/
theorem translate_four (p x y : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    g2Product p (p^(-2 : ℤ)*x) (p^(4 : ℤ)*y) =
      (↑(p^(-6 : ℤ)*y^(-4 : ℤ)) : R)*g2Product p x y := by
  have h := shift_factored p x y (-1) 2 hp
  norm_num only [Int.reduceMul,Int.reduceAdd] at h
  have hf : shiftFactor p x (-1)*shiftFactor p y 2*shiftFactor p (x*y) 1*
      shiftFactor p (x^2*y) 0*shiftFactor p (x^3*y) (-1)*shiftFactor p (x^3*y^2) 1 =
        p^(-6 : ℤ)*y^(-4 : ℤ) := by
    norm_num [shiftFactor,zpow_ofNat,zpow_neg,mul_zpow]
    apply Additive.ofMul.injective
    simp only [ofMul_mul,ofMul_pow,ofMul_inv]
    module
  rw [hf] at h
  exact h
end KanadeRussell.Infra.G2JacobiFunctionalEquations
