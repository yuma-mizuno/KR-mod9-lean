import KanadeRussell.Infra.WeierstrassAddition
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KanadeRussell.Infra.ThetaAddition
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

theorem jacobi_plucker (p x y z w : Rˣ)
    (hp : IsTopologicallyNilpotent (p : R)) (hx : IsUnit (jacobi p x)) :
    kernel p x z * kernel p y w - kernel p x w * kernel p y z =
      (y : R) * ((z⁻¹ : Rˣ) : R) * kernel p x y * kernel p z w := by
  have h1 := weierstrass_addition p x y z hp hx
  have h2 := weierstrass_addition p x y w hp hx
  have h3 := weierstrass_addition p x z w hp hx
  have hz : (z : R) * ((z⁻¹ : Rˣ) : R) = 1 := by simp
  apply (hx.pow 2).mul_left_cancel
  linear_combination kernel p x w * h1 - kernel p x z * h2 +
    (y : R) * ((z⁻¹ : Rˣ) : R) * kernel p x y * h3 +
    (y : R) * ((w⁻¹ : Rˣ) : R) * kernel p x y * kernel p x z * (jacobi p w)^2 * hz

/-- Balanced triple addition; the first argument is written as a square of a unit. -/
theorem jacobi_triple_addition (p a v Z : Rˣ)
    (hp : IsTopologicallyNilpotent (p : R)) (hanchor : IsUnit (jacobi p (Z*a))) :
    jacobi p Z * ((Z : R) * jacobi p (a^2*v*Z) * jacobi p (a^2/Z) *
      jacobi p (v/Z) + jacobi p (a^2*Z) * jacobi p (v*Z) *
      jacobi p (a^2*v/Z)) =
    jacobi p (Z^2) * jacobi p (a^2) * jacobi p v * jacobi p (a^2*v) := by
  have h := jacobi_plucker p (Z*a) (Z/a) (v*a) a hp hanchor
  simp only [kernel] at h
  have e1 : Z*a*(v*a) = a^2*v*Z := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow]
    module
  have e2 : Z*a/(v*a) = (v/Z)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
    module
  have e3 : Z/a*a = Z := by
    apply Additive.ofMul.injective
    simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
    module
  have e4 : Z/a/a = (a^2/Z)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv, ofMul_pow]
    module
  have e5 : Z*a*a = a^2*Z := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow]
    module
  have e6 : Z*a/a = Z := by
    apply Additive.ofMul.injective
    simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
    module
  have e7 : Z/a*(v*a) = v*Z := by
    apply Additive.ofMul.injective
    simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
    module
  have e8 : Z/a/(v*a) = (a^2*v/Z)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv, ofMul_pow]
    module
  have e9 : Z*a*(Z/a) = Z^2 := by
    apply Additive.ofMul.injective
    simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv, ofMul_pow]
    module
  have e10 : Z*a/(Z/a) = a^2 := by
    apply Additive.ofMul.injective
    simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv, ofMul_pow]
    module
  have e11 : v*a*a = a^2*v := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow]
    module
  have e12 : v*a/a = v := by
    apply Additive.ofMul.injective
    simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
    module
  rw [e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12] at h
  rw [jacobi_inv p (v/Z) hp, jacobi_inv p (a^2/Z) hp,
    jacobi_inv p (a^2*v/Z) hp] at h
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv,
    Units.val_mul] at h
  have ep : (a^2)⁻¹ = a⁻¹*a⁻¹ := by
    simp [pow_two]
  rw [ep] at h
  simp only [Units.val_mul] at h
  apply ((Z.isUnit.mul ((a⁻¹).isUnit.pow 2)).mul (v⁻¹).isUnit).mul_left_cancel
  linear_combination h
end KanadeRussell.Infra.ThetaAddition
