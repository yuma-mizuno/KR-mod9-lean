import KanadeRussell.Infra.JacobiProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Weierstrass addition from the rank-two theta kernel. -/
namespace KanadeRussell.Infra.ThetaAddition
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
theorem theta_inv (p z : Rˣ) : theta p z⁻¹ = theta p z := by
  unfold theta
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply, term, neg_mul_neg, inv_zpow, zpow_neg, inv_inv]

theorem theta_shift (p z : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    theta p (p^2*z) = ((p⁻¹ * z⁻¹ : Rˣ) : R) * theta p z := by
  have ht := (summable_theta p z hp).hasSum
  have he := (Equiv.addRight (1 : ℤ)).hasSum_iff.mpr ht
  have hs := he.mul_left (((p⁻¹ * z⁻¹ : Rˣ) : R))
  apply (summable_theta p (p^2*z) hp).hasSum.unique
  apply hs.congr_fun
  intro n
  simp only [Function.comp_apply, Equiv.coe_addRight, term, ← Units.val_mul]
  congr 1
  apply Additive.ofMul.injective
  simp only [mul_zpow, ← zpow_natCast, ← zpow_mul,
    ofMul_mul, ofMul_zpow, ofMul_inv]
  module


theorem jacobi_inv (p u : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    jacobi p u⁻¹ = -((u⁻¹ : Rˣ) : R) * jacobi p u := by
  have hi := theta_inv p (-u⁻¹/p)
  have hunit : (-u⁻¹/p)⁻¹ = p^2 * (-u/p) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_neg, inv_inv, neg_mul, mul_neg]
    congr 1
    apply Additive.ofMul.injective
    simp only [← zpow_natCast, ofMul_mul, ofMul_zpow, ofMul_inv]
    module
  rw [hunit, theta_shift p (-u/p) hp] at hi
  rw [jacobi, ← hi]
  congr 1
  simp [div_eq_mul_inv]

private theorem kernel_pair (p x z : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    kernel p x z = theta (p^2) ((-x/p)^2) * theta (p^2) (z^2) +
      ((p : R) * (((-x/p) : Rˣ) : R) * theta (p^2) (p^2*(-x/p)^2)) *
      ((z : R) * theta (p^2) (p^2*z^2)) := by
  have h1 : -(x*z)/p = (-x/p)*z := by
    simp only [div_eq_mul_inv, neg_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel
  have h2 : -(x/z)/p = (-x/p)/z := by
    simp only [div_eq_mul_inv, neg_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel
  unfold kernel jacobi
  rw [h1, h2, theta_pair p (-x/p) z hp]
  ring

/-- Every three by three minor of the separated theta kernel vanishes. -/
theorem kernel_minor (p x y u v : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    kernel p 1 1 * kernel p x u * kernel p y v +
      kernel p 1 u * kernel p x v * kernel p y 1 +
      kernel p 1 v * kernel p x 1 * kernel p y u -
      kernel p 1 v * kernel p x u * kernel p y 1 -
      kernel p 1 u * kernel p x 1 * kernel p y v -
      kernel p 1 1 * kernel p x v * kernel p y u = 0 := by
  simp only [kernel_pair p _ _ hp]
  ring

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R]
  [T2Space R] in
private theorem kernel_one_right (p x : Rˣ) : kernel p x 1 = (jacobi p x)^2 := by
  simp [kernel, pow_two]

private theorem kernel_self (p x : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    kernel p x x = 0 := by
  simp [kernel, jacobi_one_eq_zero p hp]

private theorem kernel_one_left (p z : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    kernel p 1 z = -((z⁻¹ : Rˣ) : R) * (jacobi p z)^2 := by
  simp only [kernel, one_mul, one_div, jacobi_inv p z hp]
  ring

private theorem kernel_swap (p x y : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    kernel p y x = -(y : R) * ((x⁻¹ : Rˣ) : R) * kernel p x y := by
  have hi := jacobi_inv p (x/y) hp
  rw [inv_div] at hi
  simp only [div_eq_mul_inv, Units.val_mul] at hi
  simp only [kernel, div_eq_mul_inv, mul_comm y x]
  rw [hi]
  ring

/-- The Weierstrass relation, proved from convergent theta sums and a rank-two
kernel. The unit hypothesis is supplied by the Jacobi product in applications. -/
theorem weierstrass_addition (p x y z : Rˣ) (hp : IsTopologicallyNilpotent (p : R))
    (hx : IsUnit (jacobi p x)) :
    kernel p x z * (jacobi p y)^2 - kernel p y z * (jacobi p x)^2 =
      (y : R) * ((z⁻¹ : Rˣ) : R) * kernel p x y * (jacobi p z)^2 := by
  have hd := kernel_minor p x y x z hp
  simp only [kernel_one_right, kernel_self p _ hp, kernel_one_left p _ hp,
    zero_mul, mul_zero, zero_add, sub_zero] at hd
  rw [kernel_swap p x y hp] at hd
  have he : (jacobi p x)^2 * ((x⁻¹ : Rˣ) : R) *
      (kernel p x z * (jacobi p y)^2 - kernel p y z * (jacobi p x)^2 -
       (y : R) * ((z⁻¹ : Rˣ) : R) * kernel p x y * (jacobi p z)^2) = 0 := by
    linear_combination -hd
  have hn : IsUnit ((jacobi p x)^2 * ((x⁻¹ : Rˣ) : R)) :=
    (hx.pow 2).mul (x⁻¹).isUnit
  exact sub_eq_zero.mp (hn.mul_left_cancel (by simpa only [mul_zero] using he))

end KanadeRussell.Infra.ThetaAddition
