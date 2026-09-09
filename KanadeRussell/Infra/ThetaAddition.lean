import KanadeRussell.Infra.Theta
import RogersRamanujan.NumberTheory.QTheory.JacobiTripleProduct.NilpotentUnit

/-! A rank-two theta addition identity from a convergent lattice bijection. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Filter Topology
namespace KanadeRussell.Infra.ThetaAddition

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def term (p z : Rˣ) (n : ℤ) : R := ↑(z ^ n * p ^ (n * n))
noncomputable def theta (p z : Rˣ) : R := ∑' n : ℤ, term p z n

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
theorem term_nat (p z : Rˣ) (n : ℕ) :
    term p z n = ((z : R) * p) ^ n * ((p : R) ^ 2) ^ n.choose 2 := by
  simp only [term, ← Nat.cast_mul, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val,
    mul_pow]
  rw [show n * n = n + 2 * n.choose 2 by have h := Nat.two_mul_choose_two_add_self n; omega, pow_add]
  ring

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
theorem term_neg_nat (p z : Rˣ) (n : ℕ) : term p z (-n) = term p z⁻¹ n := by
  simp only [term, neg_mul_neg, inv_zpow, zpow_neg]

omit [T2Space R] in
theorem summable_theta (p z : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    Summable (term p z) := by
  apply (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero _).mpr
  rw [Int.tendsto_cofinite_iff]
  have hp2 : IsTopologicallyNilpotent ((p : R) ^ 2) := hp.pow (by decide)
  constructor
  · simpa only [term_nat] using
      (tendsto_pow_mul_pow_choose_two (a := (z : R) * p) hp2)
  · simpa only [term_neg_nat, term_nat] using
      (tendsto_pow_mul_pow_choose_two (a := ((z⁻¹ : Rˣ) : R) * p) hp2)

/-- The even and odd sum/difference coordinates partition the integer lattice. -/
def parityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun
    | Sum.inl (a, b) => (a + b, a - b)
    | Sum.inr (a, b) => (a + b + 1, a - b)
  invFun mn := if (mn.1 + mn.2) % 2 = 0 then
    Sum.inl ((mn.1 + mn.2) / 2, (mn.1 - mn.2) / 2)
    else Sum.inr ((mn.1 + mn.2 - 1) / 2, (mn.1 - mn.2 - 1) / 2)
  left_inv := by
    rintro (⟨a,b⟩ | ⟨a,b⟩) <;> simp only
    · rw [if_pos (by omega)]
      congr 2 <;> omega
    · rw [if_neg (by omega)]
      congr 2 <;> omega
  right_inv := by
    rintro ⟨m,n⟩
    simp only
    split_ifs <;> simp only <;> apply Prod.ext <;> simp only <;> omega

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
private theorem pair_units (p x z : Rˣ) (m n : ℤ) :
    ((x*z)^m * p^(m*m)) * ((x/z)^n * p^(n*n)) =
      x^(m+n) * z^(m-n) * p^(m*m+n*n) := by
  simp only [mul_zpow, zpow_add, zpow_sub, div_eq_mul_inv, inv_zpow]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
private theorem term_even (p x z : Rˣ) (a b : ℤ) :
    term p (x * z) (a+b) * term p (x / z) (a-b) =
      term (p^2) (x^2) a * term (p^2) (z^2) b := by
  simp only [term, ← Units.val_mul]
  congr 1
  rw [pair_units]
  rw [show a+b+(a-b) = 2*a by ring,
    show a+b-(a-b) = 2*b by ring,
    show (a+b)*(a+b)+(a-b)*(a-b) = 2*(a*a)+2*(b*b) by ring]
  simp only [← zpow_natCast, ← zpow_mul, zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
private theorem term_odd (p x z : Rˣ) (a b : ℤ) :
    term p (x * z) (a+b+1) * term p (x / z) (a-b) =
      (p : R) * x * z * (term (p^2) (p^2*x^2) a * term (p^2) (p^2*z^2) b) := by
  simp only [term, ← Units.val_mul]
  congr 1
  rw [pair_units]
  rw [show a+b+1+(a-b) = 1+2*a by ring,
    show a+b+1-(a-b) = 1+2*b by ring,
    show (a+b+1)*(a+b+1)+(a-b)*(a-b) = 1+2*a+2*(a*a)+2*b+2*(b*b) by ring]
  simp only [mul_zpow, ← zpow_natCast, ← zpow_mul, zpow_add, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

/-- Theta pair products have two separated terms; no theta addition theorem is assumed. -/
theorem theta_pair (p x z : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    theta p (x*z) * theta p (x/z) =
      theta (p^2) (x^2) * theta (p^2) (z^2) +
      (p : R) * x * z * (theta (p^2) (p^2*x^2) * theta (p^2) (p^2*z^2)) := by
  have hp2 : IsTopologicallyNilpotent ((p^2 : Rˣ) : R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 2 ≠ 0)
  have ht : HasSum (fun mn : ℤ × ℤ => term p (x*z) mn.1 * term p (x/z) mn.2)
      (theta p (x*z) * theta p (x/z)) :=
    (summable_theta p (x*z) hp).hasSum.mul_of_nonarchimedean'
      (summable_theta p (x/z) hp).hasSum
  have he : HasSum (fun ab : ℤ × ℤ => term (p^2) (x^2) ab.1 * term (p^2) (z^2) ab.2)
      (theta (p^2) (x^2) * theta (p^2) (z^2)) :=
    (summable_theta (p^2) (x^2) hp2).hasSum.mul_of_nonarchimedean'
      (summable_theta (p^2) (z^2) hp2).hasSum
  have ho : HasSum (fun ab : ℤ × ℤ => (p : R)*x*z *
      (term (p^2) (p^2*x^2) ab.1 * term (p^2) (p^2*z^2) ab.2))
      ((p : R)*x*z * (theta (p^2) (p^2*x^2) * theta (p^2) (p^2*z^2))) :=
    ((summable_theta (p^2) (p^2*x^2) hp2).hasSum.mul_of_nonarchimedean'
    (summable_theta (p^2) (p^2*z^2) hp2).hasSum).mul_left ((p : R)*x*z)
  have hh : HasSum (Sum.elim
      (fun ab : ℤ × ℤ => term (p^2) (x^2) ab.1 * term (p^2) (z^2) ab.2)
      (fun ab : ℤ × ℤ => (p : R)*x*z *
        (term (p^2) (p^2*x^2) ab.1 * term (p^2) (p^2*z^2) ab.2)))
      (theta (p^2) (x^2) * theta (p^2) (z^2) +
        (p : R)*x*z * (theta (p^2) (p^2*x^2) * theta (p^2) (p^2*z^2))) :=
    HasSum.sum he ho
  have hr := parityEquiv.hasSum_iff.mpr ht
  apply hr.unique
  apply hh.congr_fun
  rintro (⟨a,b⟩ | ⟨a,b⟩)
  · exact term_even p x z a b
  · exact term_odd p x z a b

noncomputable def jacobi (p u : Rˣ) : R := theta p (-u/p)
noncomputable def kernel (p x z : Rˣ) : R := jacobi p (x*z) * jacobi p (x/z)

end KanadeRussell.Infra.ThetaAddition
