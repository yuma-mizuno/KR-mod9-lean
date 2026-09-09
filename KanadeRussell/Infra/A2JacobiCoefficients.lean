import KanadeRussell.Product.CubicFrame
import KanadeRussell.Infra.JacobiTrisection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.A2JacobiCoefficients
open ThetaAddition

def coefficientEquiv : (ℤ × ℤ) × ℤ ≃ (ℤ × ℤ) × ℤ where
  toFun mnk := ((mnk.1.1-mnk.2,mnk.1.2-mnk.2),mnk.2)
  invFun ijk := ((ijk.1.1+ijk.2,ijk.1.2+ijk.2),ijk.2)
  left_inv := by rintro ⟨⟨m,n⟩,k⟩; simp
  right_inv := by rintro ⟨⟨i,j⟩,k⟩; simp

variable {R : Type*} [CommRing R]

def coefficientTerm (p : Rˣ) (m n k : ℤ) : R :=
  ↑(((-1:Rˣ)^(m+n-k))*p^((m-k)*(m-k-1)+(n-k)*(n-k-1)+k*(k-1)))

theorem coefficientTerm_eq (p : Rˣ) (m n k : ℤ) :
    coefficientTerm p m n k =
      (↑(((-1:Rˣ)^(m+n))*p^(m*(m-1)+n*(n-1))):R)*
        jacobiTerm (p^3) (p^(4-2*m-2*n)) k := by
  have hs : (-1:Rˣ)^(m+n-k)=(-1:Rˣ)^(m+n)*(-1:Rˣ)^k := by
    rw [zpow_sub]
    simp only [← inv_zpow,inv_neg,inv_one]
  simp only [coefficientTerm,jacobiTerm,← Units.val_mul]
  congr 1
  rw [hs]
  apply Additive.ofMul.injective
  simp only [ofMul_mul,ofMul_zpow,ofMul_pow]
  module

theorem tripleTerm_eq (p x y : Rˣ) (m n k : ℤ) :
    (jacobiTerm p x (m-k)*jacobiTerm p y (n-k))*jacobiTerm p (x*y) k =
      coefficientTerm p m n k * (↑(x^m*y^n):R) := by
  have hs : ((-1:Rˣ)^(m-k)*(-1:Rˣ)^(n-k))*(-1:Rˣ)^k=(-1:Rˣ)^(m+n-k) := by
    rw [← zpow_add,← zpow_add]
    congr 1; ring
  simp only [jacobiTerm,coefficientTerm,← Units.val_mul,mul_zpow]
  congr 1
  calc
    _ = (((-1:Rˣ)^(m-k)*(-1:Rˣ)^(n-k))*(-1:Rˣ)^k)*
      (x^(m-k)*y^(n-k)*x^k*y^k*p^((m-k)*(m-k-1))*p^((n-k)*(n-k-1))*p^(k*(k-1))) := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul]
        abel
    _ = _ := by
      rw [hs]
      apply Additive.ofMul.injective
      simp only [ofMul_mul,ofMul_zpow]
      module

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def coefficient (p : Rˣ) (m n : ℤ) : R :=
  (↑(((-1:Rˣ)^(m+n))*p^(m*(m-1)+n*(n-1))):R)*
    jacobi (p^3) (p^(4-2*m-2*n))

omit [T2Space R] in
theorem hasSum_coefficient (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n : ℤ) :
    HasSum (coefficientTerm p m n) (coefficient p m n) := by
  have hp3 : IsTopologicallyNilpotent ((p^3:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 3 ≠ 0)
  have h := (hasSum_jacobiTerm (p^3) (p^(4-2*m-2*n)) hp3).mul_left
    (↑(((-1:Rˣ)^(m+n))*p^(m*(m-1)+n*(n-1))):R)
  exact h.congr_fun (fun k => coefficientTerm_eq p m n k)

omit [T2Space R] in
theorem hasSum_triple_product (p x y : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    HasSum (fun mn : ℤ × ℤ => coefficient p mn.1 mn.2*(↑(x^mn.1*y^mn.2):R))
      (jacobi p x*jacobi p y*jacobi p (x*y)) := by
  have hxy : HasSum (fun ij : ℤ × ℤ => jacobiTerm p x ij.1*jacobiTerm p y ij.2)
      (jacobi p x*jacobi p y) :=
    (hasSum_jacobiTerm p x hp).mul_of_nonarchimedean' (hasSum_jacobiTerm p y hp)
  have ht : HasSum (fun ijk : (ℤ × ℤ) × ℤ =>
      (jacobiTerm p x ijk.1.1*jacobiTerm p y ijk.1.2)*jacobiTerm p (x*y) ijk.2)
      (jacobi p x*jacobi p y*jacobi p (x*y)) :=
    hxy.mul_of_nonarchimedean' (hasSum_jacobiTerm p (x*y) hp)
  have hh := coefficientEquiv.hasSum_iff.mpr ht
  have hf (mn : ℤ × ℤ) : HasSum (fun k : ℤ =>
      (jacobiTerm p x (mn.1-k)*jacobiTerm p y (mn.2-k))*jacobiTerm p (x*y) k)
      (coefficient p mn.1 mn.2*(↑(x^mn.1*y^mn.2):R)) := by
    exact ((hasSum_coefficient p hp mn.1 mn.2).mul_right (↑(x^mn.1*y^mn.2):R)).congr_fun
      (fun k => tripleTerm_eq p x y mn.1 mn.2 k)
  exact hh.prod_fiberwise hf
open scoped QTheory

/-- The raw constant coefficient is exactly Euler's product, not an unspecified scalar. -/
theorem coefficient_zero (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    coefficient p 0 0 = ((p:R)^2;(p:R)^2)_∞ := by
  norm_num [coefficient]
  change jacobi (p^(3:ℕ)) (p^(4:ℕ)) = ((p:R)^2;(p:R)^2)_∞
  have he : (p^(3:ℕ))^(2:ℕ)/p^(2:ℕ)=p^(4:ℕ) := by
    apply Additive.ofMul.injective
    simp only [ofMul_div,ofMul_pow]
    module
  rw [← he,Product.CubicFrame.jacobi_complement,Product.jacobi_cubic_argument p hp]

/-- Cooper's coefficient formula normalized to the six Pochhammer factors. -/
noncomputable def normalizedCoefficient (p : Rˣ) (m n : ℤ) : R :=
  bInv (((p:R)^2;(p:R)^2)_∞)^3 * coefficient p m n

omit [T2Space R] in
theorem hasSum_normalized_product (p x y : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    HasSum (fun mn : ℤ × ℤ => normalizedCoefficient p mn.1 mn.2*(↑(x^mn.1*y^mn.2):R))
      (bInv (((p:R)^2;(p:R)^2)_∞)^3*(jacobi p x*jacobi p y*jacobi p (x*y))) := by
  have hh := (hasSum_triple_product p x y hp).mul_left (bInv (((p:R)^2;(p:R)^2)_∞)^3)
  apply hh.congr_fun
  intro mn
  simp only [normalizedCoefficient,mul_assoc]

theorem normalizedCoefficient_zero (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    ((p:R)^2;(p:R)^2)_∞^2 * normalizedCoefficient p 0 0 = 1 := by
  have hu := isUnit_qPochhammerInf (hp.pow (by decide : 2 ≠ 0)) (hp.pow (by decide : 2 ≠ 0))
  rw [normalizedCoefficient,coefficient_zero p hp]
  calc
    _ = (((p:R)^2;(p:R)^2)_∞*bInv (((p:R)^2;(p:R)^2)_∞))^3 := by ring
    _ = 1 := by rw [hu.mul_bInv_cancel]; ring
end KanadeRussell.Infra.A2JacobiCoefficients
