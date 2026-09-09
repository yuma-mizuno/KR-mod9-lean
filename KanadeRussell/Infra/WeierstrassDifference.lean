import KanadeRussell.Infra.JacobiJets

/-! Weierstrass' difference formula as an identity of convergent formal series.
The proof takes the second coefficient of the already proved addition relation.
No analytic differentiation, modular transformation, or coefficient bound is used. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped QTheory
namespace KanadeRussell.Infra.ThetaAddition
open JacobiJets SecondCoefficient
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

/-- The denominator-cleared elliptic Lambert difference formula. -/
theorem weierstrass_difference (p x y : Rˣ) (hp : IsTopologicallyNilpotent (p : R))
    (hx : IsTopologicallyNilpotent (x : R))
    (hx' : IsTopologicallyNilpotent ((p^2/x : Rˣ) : R))
    (hy : IsTopologicallyNilpotent (y : R))
    (hy' : IsTopologicallyNilpotent ((p^2/y : Rˣ) : R)) :
    (jacobi p x)^2 * (jacobi p y)^2 * (ellipticLambert p x - ellipticLambert p y) =
      -(y : R) * (((p : R)^2; (p : R)^2)_∞)^6 * kernel p x y := by
  have hCp : IsTopologicallyNilpotent ((unitC p : (PowerSeries R)ˣ) : PowerSeries R) :=
    hp.map continuous_C
  have hu : IsUnit (jacobi (unitC p) (unitC x)) := by
    rw [jacobi_unitC p x hp]
    exact (isUnit_jacobi p x hp hx hx').map PowerSeries.C
  have h := weierstrass_addition (unitC p) (unitC x) (unitC y) oneAddX hCp hu
  rw [jacobi_unitC p y hp, jacobi_unitC p x hp, kernel_unitC p x y hp, unitC_val] at h
  have hr : PowerSeries.C (y : R) *
      (((oneAddX : (PowerSeries R)ˣ)⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) *
      PowerSeries.C (kernel p x y) * (jacobi (unitC p) oneAddX)^2 =
      PowerSeries.C ((y : R) * kernel p x y) *
        ((((oneAddX : (PowerSeries R)ˣ)⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) *
          (jacobi (unitC p) oneAddX)^2) := by
    rw [map_mul]
    ring
  rw [hr] at h
  have hc := congrArg (coeff 2) h
  obtain ⟨h0, h1, h2⟩ := jacobi_square_coefficients p hp
  have hkx := (kernel_coefficients p x hp hx hx').2
  have hky := (kernel_coefficients p y hp hy hy').2
  rw [kernel_constant p x hp] at hkx
  rw [kernel_constant p y hp] at hky
  simp only [map_sub, ← map_pow, coeff_mul_C, coeff_C_mul, coeff_two_mul,
    hkx, hky, h0, h1, h2, JacobiJets.constantCoeff_inv, mul_zero, zero_add, one_mul] at hc
  linear_combination -hc

end KanadeRussell.Infra.ThetaAddition
