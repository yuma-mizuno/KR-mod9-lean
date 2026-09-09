import KanadeRussell.Infra.JacobiProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 50000
namespace KanadeRussell.Infra.A2ThetaFactorization
open ThetaAddition

def parityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun
    | Sum.inl (a,b) => (a+b,2*b)
    | Sum.inr (a,b) => (a+b+1,2*b+1)
  invFun mn := if mn.2 % 2 = 0 then
    Sum.inl (mn.1-mn.2/2,mn.2/2)
    else Sum.inr (mn.1-(mn.2-1)/2-1,(mn.2-1)/2)
  left_inv := by
    rintro (⟨a,b⟩ | ⟨a,b⟩) <;> simp only
    · rw [if_pos (by omega)]; congr 2 <;> omega
    · rw [if_neg (by omega)]; congr 2 <;> omega
  right_inv := by
    rintro ⟨m,n⟩
    simp only
    split_ifs <;> apply Prod.ext <;> simp only <;> omega

variable {R : Type*} [CommRing R]
def term (p u v : Rˣ) (mn : ℤ × ℤ) : R :=
  ↑(u^mn.1*v^mn.2*p^(mn.1*mn.1+mn.2*mn.2-mn.1*mn.2))

theorem term_even (p u v : Rˣ) (a b : ℤ) :
    term p u v (a+b,2*b) = ThetaAddition.term p u a *
      ThetaAddition.term (p^3) (u*v^2) b := by
  simp only [term, ThetaAddition.term, ← Units.val_mul]
  congr 1
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow]
  module

theorem term_odd (p u v : Rˣ) (a b : ℤ) :
    term p u v (a+b+1,2*b+1) = (u:R)*v*p *
      (ThetaAddition.term p (u*p) a * ThetaAddition.term (p^3) (u*v^2*p^3) b) := by
  simp only [term, ThetaAddition.term, ← Units.val_mul]
  congr 1
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow]
  module

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R]

omit [T2Space R] in
/-- A convergent rank-two A₂ theta sum is exactly two products of unary theta functions. -/
theorem hasSum_factorization (p u v : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    HasSum (term p u v)
      (ThetaAddition.theta p u * ThetaAddition.theta (p^3) (u*v^2) +
        (u:R)*v*p*(ThetaAddition.theta p (u*p)*ThetaAddition.theta (p^3) (u*v^2*p^3))) := by
  have hp3 : IsTopologicallyNilpotent ((p^3:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 3 ≠ 0)
  have he : HasSum (fun ab : ℤ × ℤ => ThetaAddition.term p u ab.1 *
      ThetaAddition.term (p^3) (u*v^2) ab.2)
      (ThetaAddition.theta p u * ThetaAddition.theta (p^3) (u*v^2)) := (ThetaAddition.summable_theta p u hp).hasSum.mul_of_nonarchimedean'
    (ThetaAddition.summable_theta (p^3) (u*v^2) hp3).hasSum
  have ho : HasSum (fun ab : ℤ × ℤ => (u:R)*v*p *
      (ThetaAddition.term p (u*p) ab.1 * ThetaAddition.term (p^3) (u*v^2*p^3) ab.2))
      ((u:R)*v*p*(ThetaAddition.theta p (u*p)*ThetaAddition.theta (p^3) (u*v^2*p^3))) := ((ThetaAddition.summable_theta p (u*p) hp).hasSum.mul_of_nonarchimedean'
    (ThetaAddition.summable_theta (p^3) (u*v^2*p^3) hp3).hasSum).mul_left ((u:R)*v*p)
  have hs : HasSum (Sum.elim
      (fun ab : ℤ × ℤ => ThetaAddition.term p u ab.1 * ThetaAddition.term (p^3) (u*v^2) ab.2)
      (fun ab : ℤ × ℤ => (u:R)*v*p * (ThetaAddition.term p (u*p) ab.1 *
        ThetaAddition.term (p^3) (u*v^2*p^3) ab.2)))
      (ThetaAddition.theta p u * ThetaAddition.theta (p^3) (u*v^2) +
        (u:R)*v*p*(ThetaAddition.theta p (u*p)*ThetaAddition.theta (p^3) (u*v^2*p^3))) :=
    HasSum.sum he ho
  have heq : (Sum.elim
      (fun ab : ℤ × ℤ => ThetaAddition.term p u ab.1 * ThetaAddition.term (p^3) (u*v^2) ab.2)
      (fun ab : ℤ × ℤ => (u:R)*v*p * (ThetaAddition.term p (u*p) ab.1 *
        ThetaAddition.term (p^3) (u*v^2*p^3) ab.2))) = (term p u v) ∘ parityEquiv := by
    funext ab
    rcases ab with ⟨a,b⟩ | ⟨a,b⟩
    · exact (term_even p u v a b).symm
    · exact (term_odd p u v a b).symm
  rw [heq] at hs
  exact parityEquiv.hasSum_iff.mp hs
theorem tsum_factorization (p u v : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    ∑' mn : ℤ × ℤ, term p u v mn =
      ThetaAddition.theta p u * ThetaAddition.theta (p^3) (u*v^2) +
        (u:R)*v*p*(ThetaAddition.theta p (u*p)*ThetaAddition.theta (p^3) (u*v^2*p^3)) :=
  (hasSum_factorization p u v hp).tsum_eq
end KanadeRussell.Infra.A2ThetaFactorization
