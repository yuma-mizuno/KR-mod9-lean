import KanadeRussell.Infra.ThetaAddition
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.ThetaAddition
variable {R : Type*} [CommRing R]

theorem term_pair_even (p u v : Rˣ) (a b : ℤ) :
    term p u (a+b)*term p v (a-b)=term (p^2) (u*v) a*term (p^2) (u/v) b := by
  simp only [term,← Units.val_mul]
  congr 1
  apply Additive.ofMul.injective
  simp only [ofMul_mul,ofMul_div,ofMul_zpow,ofMul_pow]
  module

theorem term_pair_odd (p u v : Rˣ) (a b : ℤ) :
    term p u (a+b+1)*term p v (a-b)=(p:R)*u*
      (term (p^2) (p^2*u*v) a*term (p^2) (p^2*u/v) b) := by
  simp only [term,← Units.val_mul]
  congr 1
  apply Additive.ofMul.injective
  simp only [ofMul_mul,ofMul_div,ofMul_zpow,ofMul_pow]
  module

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R]

/-- The binary theta product formula with arbitrary arguments, without square roots. -/
theorem theta_pair_general (p u v : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    theta p u*theta p v=theta (p^2) (u*v)*theta (p^2) (u/v)+
      (p:R)*u*(theta (p^2) (p^2*u*v)*theta (p^2) (p^2*u/v)) := by
  have hp2 : IsTopologicallyNilpotent ((p^2:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 2 ≠ 0)
  have ht : HasSum (fun mn : ℤ × ℤ => term p u mn.1*term p v mn.2)
      (theta p u*theta p v) :=
    (summable_theta p u hp).hasSum.mul_of_nonarchimedean' (summable_theta p v hp).hasSum
  have he : HasSum (fun ab : ℤ × ℤ => term (p^2) (u*v) ab.1*term (p^2) (u/v) ab.2)
      (theta (p^2) (u*v)*theta (p^2) (u/v)) :=
    (summable_theta (p^2) (u*v) hp2).hasSum.mul_of_nonarchimedean'
      (summable_theta (p^2) (u/v) hp2).hasSum
  have ho : HasSum (fun ab : ℤ × ℤ => (p:R)*u*
      (term (p^2) (p^2*u*v) ab.1*term (p^2) (p^2*u/v) ab.2))
      ((p:R)*u*(theta (p^2) (p^2*u*v)*theta (p^2) (p^2*u/v))) :=
    ((summable_theta (p^2) (p^2*u*v) hp2).hasSum.mul_of_nonarchimedean'
      (summable_theta (p^2) (p^2*u/v) hp2).hasSum).mul_left ((p:R)*u)
  have hs : HasSum (Sum.elim
      (fun ab : ℤ × ℤ => term (p^2) (u*v) ab.1*term (p^2) (u/v) ab.2)
      (fun ab : ℤ × ℤ => (p:R)*u*(term (p^2) (p^2*u*v) ab.1*term (p^2) (p^2*u/v) ab.2)))
      (theta (p^2) (u*v)*theta (p^2) (u/v)+
        (p:R)*u*(theta (p^2) (p^2*u*v)*theta (p^2) (p^2*u/v))) := HasSum.sum he ho
  have hr := parityEquiv.hasSum_iff.mpr ht
  apply hr.unique
  apply hs.congr_fun
  rintro (⟨a,b⟩ | ⟨a,b⟩)
  · exact term_pair_even p u v a b
  · exact term_pair_odd p u v a b
end KanadeRussell.Infra.ThetaAddition
