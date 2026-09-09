import KanadeRussell.Infra.A2CoefficientResidues
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.A2JacobiCoefficients
open ThetaAddition
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
theorem coefficient_swap (p : Rˣ) (m n : ℤ) : coefficient p n m = coefficient p m n := by
  unfold coefficient
  rw [show n+m=m+n by omega, show n*(n-1)+m*(m-1)=m*(m-1)+n*(n-1) by ring,
    show 4-2*n-2*m=4-2*m-2*n by ring]

theorem coefficient_translate (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n s t : ℤ) :
    coefficient p (m+3*s) (n+3*t) =
      (↑(p^((4*m-2*n-2)*s+(4*n-2*m-2)*t+6*(s^2+t^2-s*t))):R)*coefficient p m n := by
  rw [A2CoefficientResidues.coefficient_class p hp (m+3*s) (n+3*t) (s+t) (m+n) (by ring),
    A2CoefficientResidues.coefficient_class p hp m n 0 (m+n) (by ring)]
  rw [← mul_assoc,← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul,ofMul_zpow,A2CoefficientResidues.residueExponent]
  module

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem reflection_term (p : Rˣ) (m n k : ℤ) :
    coefficientTerm p (n-m+1) n (n-k) = -coefficientTerm p m n k := by
  have he : (n-m+1-(n-k))*(n-m+1-(n-k)-1)+(n-(n-k))*(n-(n-k)-1)+(n-k)*(n-k-1) =
      (m-k)*(m-k-1)+(n-k)*(n-k-1)+k*(k-1) := by ring
  have hs : (n-m+1)+n-(n-k) = 1+2*(k-m)+(m+n-k) := by ring
  simp only [coefficientTerm,he,hs,zpow_add,zpow_mul]
  norm_num [zpow_ofNat]

def reflectionEquiv (n : ℤ) : ℤ ≃ ℤ where
  toFun k := n-k
  invFun k := n-k
  left_inv k := by dsimp; omega
  right_inv k := by dsimp; omega

theorem coefficient_reflection (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n : ℤ) :
    coefficient p (n-m+1) n = -coefficient p m n := by
  have h := (reflectionEquiv n).hasSum_iff.mpr (hasSum_coefficient p hp (n-m+1) n)
  exact h.unique ((hasSum_coefficient p hp m n).neg.congr_fun (fun k => reflection_term p m n k))

theorem coefficient_reflection_second (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n : ℤ) :
    coefficient p m (m-n+1) = -coefficient p m n := by
  rw [coefficient_swap p (m-n+1) m,coefficient_reflection p hp n m,coefficient_swap p m n]
end KanadeRussell.Infra.A2JacobiCoefficients
