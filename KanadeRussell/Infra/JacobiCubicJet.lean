import KanadeRussell.Infra.LambertUnitArgument

/-! The central cubic Jacobi jet needed in the Frobenius--Stickelberger
normalization. This is extracted from the convergent paired product and carries
no logarithmic-derivative or addition-formula assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped QTheory
namespace KanadeRussell.Infra.JacobiJets
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

/-- The first nontrivial correction to the central Jacobi zero is the Lambert tail. -/
theorem jacobi_oneAddX_third (p : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    coeff 3 (ThetaAddition.jacobi (unitC p) oneAddX) =
      (((p : R)^2; (p : R)^2)_∞)^3 * lambertTail ((p : R)^2) ((p : R)^2) := by
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  have h2 := (pochPair_coefficients ((p : R)^2) ((p : R)^2) hp2 hp2).2
  rw [pochPair_constant _ _ hp2] at h2
  rw [jacobi_oneAddX p hp]
  have he : -X * PowerSeries.C (((p : R)^2; (p : R)^2)_∞) *
      pochPair ((p : R)^2) ((p : R)^2) =
      - (X * (PowerSeries.C (((p : R)^2; (p : R)^2)_∞) *
        pochPair ((p : R)^2) ((p : R)^2))) := by ring
  rw [he, map_neg, ← pow_one (X : PowerSeries R)]
  simp only [coeff_X_pow_mul', show (1 : ℕ) ≤ 3 by decide, if_true, coeff_C_mul, h2]
  ring

/-- All central coefficients through degree three, with no division in the base ring. -/
theorem jacobi_oneAddX_cubic (p : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    constantCoeff (ThetaAddition.jacobi (unitC p) oneAddX) = 0 ∧
    coeff 1 (ThetaAddition.jacobi (unitC p) oneAddX) =
      -(((p : R)^2; (p : R)^2)_∞)^3 ∧
    coeff 2 (ThetaAddition.jacobi (unitC p) oneAddX) = 0 ∧
    coeff 3 (ThetaAddition.jacobi (unitC p) oneAddX) =
      (((p : R)^2; (p : R)^2)_∞)^3 * lambertTail ((p : R)^2) ((p : R)^2) := by
  have h := JacobiParameter.jacobi_parameter_coefficients p oneAddX hp (by simp)
  refine ⟨h.1, ?_, ?_, jacobi_oneAddX_third p hp⟩
  · simpa [coeff_X] using h.2.1
  · simpa [coeff_X] using h.2.2

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
private theorem coeff_three_mul (f g : PowerSeries R) :
    coeff 3 (f*g) = coeff 3 f * constantCoeff g + coeff 2 f * coeff 1 g +
      coeff 1 f * coeff 2 g + constantCoeff f * coeff 3 g := by
  simp only [coeff_mul, show Finset.antidiagonal 3 = {(0,3),(1,2),(2,1),(3,0)} by decide]
  simp
  ring

/-- The cubic central jet in an arbitrary multiplicative formal parameter. -/
theorem jacobi_parameter_third (p : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p : R))
    (hZ : constantCoeff (Z : PowerSeries R) = 1) :
    coeff 3 (ThetaAddition.jacobi (unitC p) Z) =
      (((p : R)^2; (p : R)^2)_∞)^3 *
        (lambertTail ((p : R)^2) ((p : R)^2) * (coeff 1 (Z : PowerSeries R))^3 -
          coeff 3 (Z : PowerSeries R)) := by
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  have hh := JacobiParameter.pochPair_coefficients ((p : R)^2) ((p : R)^2) Z hp2 hZ
    (summable_lambertTail _ _ hp2 hp2)
    (fun n => (hp2.mul_pow hp2 (n := n)).isUnit_one_sub)
  have hc := JacobiParameter.pochPair_constant ((p : R)^2) ((p : R)^2) Z hp2 hZ
  rw [JacobiParameter.jacobi_parameter p Z hp]
  simp only [coeff_three_mul, SecondCoefficient.coeff_two_mul, coeff_one_mul, map_mul,
    map_sub, map_one, hZ, sub_self, zero_mul, add_zero, mul_zero,
    constantCoeff_C, coeff_C, coeff_one, if_neg (by decide : (3 : ℕ) ≠ 0),
    if_neg (by decide : (2 : ℕ) ≠ 0), if_neg (by decide : (1 : ℕ) ≠ 0),
    hh.1, hh.2, hc]
  ring

end KanadeRussell.Infra.JacobiJets
