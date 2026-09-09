import KanadeRussell.Infra.JacobiProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! The three shifted Jacobi products whose constant term is the shifted A2
lattice theta series. This product identity follows solely by progression splitting. -/
open scoped QTheory
namespace KanadeRussell.Infra.ThetaAddition
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

theorem jacobi_trisection_product (p z : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    ((p : R)^2; (p : R)^2)_∞ * jacobi (p^3) z *
      jacobi (p^3) (z*p^2) * jacobi (p^3) (z*p^4) =
      (((p : R)^6; (p : R)^6)_∞)^3 * jacobi p z := by
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  have hp3 : IsTopologicallyNilpotent ((p^3 : Rˣ) : R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 3 ≠ 0)
  have ha := qPochhammerInf_eq_prod_range (a := (z : R)) (m := 3) (by decide) hp2
  have hb := qPochhammerInf_eq_prod_range (a := ((p^2/z : Rˣ) : R)) (m := 3) (by decide) hp2
  norm_num only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    pow_zero, mul_one, pow_one, ← pow_mul, Nat.reduceMul] at ha hb
  have h0 : (p^3)^2/z = p^6/z := by group
  have h2 : (p^3)^2/(z*p^2) = (p^2/z)*p^2 := by
    apply Additive.ofMul.injective
    simp only [← zpow_natCast, ofMul_mul, ofMul_div, ofMul_zpow]
    module
  have h4 : (p^3)^2/(z*p^4) = p^2/z := by
    apply Additive.ofMul.injective
    simp only [← zpow_natCast, ofMul_mul, ofMul_div, ofMul_zpow]
    module
  have h6 : p^6/z = (p^2/z)*p^4 := by
    apply Additive.ofMul.injective
    simp only [← zpow_natCast, ofMul_mul, ofMul_div, ofMul_zpow]
    module
  rw [jacobi_eq_product _ _ hp3, jacobi_eq_product _ _ hp3,
    jacobi_eq_product _ _ hp3, jacobi_eq_product _ _ hp, h0, h2, h4, h6]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← pow_mul, Nat.reduceMul]
  rw [ha, hb]
  ring

/-- Bilateral Jacobi summand written without a quotient in its quadratic power. -/
noncomputable def jacobiTerm (p z : Rˣ) (n : ℤ) : R :=
  ↑(((-1 : Rˣ)^n * z^n) * p^(n*(n-1)))

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
theorem term_eq_jacobiTerm (p z : Rˣ) (n : ℤ) :
    term p (-z/p) n = jacobiTerm p z n := by
  unfold term jacobiTerm
  congr 1
  rw [show -z/p = (-1 : Rˣ)*z*p⁻¹ by simp [div_eq_mul_inv]]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module

omit [T2Space R] in
theorem hasSum_jacobiTerm (p z : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    HasSum (jacobiTerm p z) (jacobi p z) := by
  exact (summable_theta p (-z/p) hp).hasSum.congr_fun
    (fun n => (term_eq_jacobiTerm p z n).symm)

end KanadeRussell.Infra.ThetaAddition
