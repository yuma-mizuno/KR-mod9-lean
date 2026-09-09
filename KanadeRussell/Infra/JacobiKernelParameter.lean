import KanadeRussell.Infra.JacobiParameter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Jacobi kernels and their central zero with arbitrary auxiliary parameters. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped QTheory
namespace KanadeRussell.Infra.JacobiParameter
open SecondCoefficient JacobiJets
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
private theorem complement_mul (p u Z : (PowerSeries R)ˣ) :
    p^2/(u*Z) = (p^2/u)*Z⁻¹ := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
private theorem complement_div (p u Z : (PowerSeries R)ˣ) :
    p^2/(u/Z) = (p^2/u)*Z := by
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ac_rfl

theorem kernel_eq_pochPair (p u : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p:R)) :
    ThetaAddition.kernel (unitC p) (unitC u) Z =
      PowerSeries.C (((p:R)^2;(p:R)^2)_∞)^2 *
        pochPair (u:R) ((p:R)^2) Z * pochPair ((p^2/u:Rˣ):R) ((p:R)^2) Z := by
  have hCp : IsTopologicallyNilpotent ((unitC p:(PowerSeries R)ˣ):PowerSeries R) :=
    hp.map continuous_C
  have hp2 : IsTopologicallyNilpotent ((p:R)^2) := hp.pow (by decide)
  have hcomp : (unitC p)^2/unitC u = unitC (p^2/u) := by
    simp only [unitC, map_div, map_pow]
  rw [ThetaAddition.kernel, ThetaAddition.jacobi_eq_product _ _ hCp,
    ThetaAddition.jacobi_eq_product _ _ hCp, complement_mul, complement_div]
  simp only [hcomp, pochPair, div_eq_mul_inv, Units.val_mul]
  simp only [unitC_val, ← map_pow,
    map_qPochhammerInf PowerSeries.C continuous_C _ hp2, Units.val_mul]
  ring

theorem kernel_constant (p u : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (hZ : constantCoeff (Z:PowerSeries R) = 1) :
    constantCoeff (ThetaAddition.kernel (unitC p) (unitC u) Z) = (ThetaAddition.jacobi p u)^2 := by
  have hp2 : IsTopologicallyNilpotent ((p:R)^2) := hp.pow (by decide)
  rw [kernel_eq_pochPair p u Z hp, ThetaAddition.jacobi_eq_product p u hp]
  simp only [map_mul, map_pow, constantCoeff_C, pochPair_constant _ _ Z hp2 hZ]
  ring

/-- The second coefficient scales by the square of the parameter's first coefficient. -/
theorem kernel_coefficients (p u : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (hZ : constantCoeff (Z:PowerSeries R) = 1)
    (hsu : Summable (fun n : ℕ => (u:R)*((p:R)^2)^n*bInv (1-(u:R)*((p:R)^2)^n)^2))
    (hu : ∀ n : ℕ, IsUnit (1-(u:R)*((p:R)^2)^n))
    (hsv : Summable (fun n : ℕ => ((p^2/u:Rˣ):R)*((p:R)^2)^n*
      bInv (1-((p^2/u:Rˣ):R)*((p:R)^2)^n)^2))
    (hv : ∀ n : ℕ, IsUnit (1-((p^2/u:Rˣ):R)*((p:R)^2)^n)) :
    coeff 1 (ThetaAddition.kernel (unitC p) (unitC u) Z) = 0 ∧
    coeff 2 (ThetaAddition.kernel (unitC p) (unitC u) Z) =
      -(ThetaAddition.jacobi p u)^2 * ellipticLambert p u * (coeff 1 (Z:PowerSeries R))^2 := by
  have hp2 : IsTopologicallyNilpotent ((p:R)^2) := hp.pow (by decide)
  obtain ⟨h1,h2⟩ := pochPair_coefficients (u:R) ((p:R)^2) Z hp2 hZ hsu hu
  obtain ⟨k1,k2⟩ := pochPair_coefficients ((p^2/u:Rˣ):R) ((p:R)^2) Z hp2 hZ hsv hv
  rw [← kernel_constant p u Z hp hZ, kernel_eq_pochPair p u Z hp]
  rw [← map_pow]
  constructor
  · simp only [coeff_one_mul, coeff_C_mul, h1, k1, zero_mul, mul_zero, add_zero]
  · simp only [coeff_two_mul, coeff_C_mul, map_mul, constantCoeff_C, h1, k1, h2, k2,
      ellipticLambert]
    ring

theorem kernel_coefficients_nilpotent (p u : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (hZ : constantCoeff (Z:PowerSeries R) = 1)
    (hu : IsTopologicallyNilpotent (u:R))
    (hv : IsTopologicallyNilpotent ((p^2/u:Rˣ):R)) :
    coeff 1 (ThetaAddition.kernel (unitC p) (unitC u) Z) = 0 ∧
    coeff 2 (ThetaAddition.kernel (unitC p) (unitC u) Z) =
      -(ThetaAddition.jacobi p u)^2 * ellipticLambert p u * (coeff 1 (Z:PowerSeries R))^2 := by
  have hp2 : IsTopologicallyNilpotent ((p:R)^2) := hp.pow (by decide)
  exact kernel_coefficients p u Z hp hZ (summable_lambertTail _ _ hu hp2)
    (fun n => (hu.mul_pow hp2 (n:=n)).isUnit_one_sub)
    (summable_lambertTail _ _ hv hp2) (fun n => (hv.mul_pow hp2 (n:=n)).isUnit_one_sub)

theorem jacobi_parameter (p : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p:R)) :
    ThetaAddition.jacobi (unitC p) Z = (1-(Z:PowerSeries R))*
      PowerSeries.C (((p:R)^2;(p:R)^2)_∞) * pochPair ((p:R)^2) ((p:R)^2) Z := by
  have hCp : IsTopologicallyNilpotent ((unitC p:(PowerSeries R)ˣ):PowerSeries R) :=
    hp.map continuous_C
  have hp2 : IsTopologicallyNilpotent ((p:R)^2) := hp.pow (by decide)
  have hCQ : IsTopologicallyNilpotent (PowerSeries.C ((p:R)^2)) := hp2.map continuous_C
  rw [ThetaAddition.jacobi_eq_product _ _ hCp]
  simp only [div_eq_mul_inv, Units.val_mul, Units.val_pow_eq_pow_val, unitC_val, ← map_pow]
  rw [qPochhammerInf_eq_one_sub_mul_qPochhammerInf (a:=(Z:PowerSeries R)) hCQ]
  rw [map_qPochhammerInf PowerSeries.C continuous_C _ hp2]
  simp only [pochPair]
  rw [mul_comm (Z:PowerSeries R) (PowerSeries.C ((p:R)^2))]
  ring

/-- The central Jacobi zero keeps the first two coefficients of the parameter. -/
theorem jacobi_parameter_coefficients (p : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (hZ : constantCoeff (Z:PowerSeries R) = 1) :
    constantCoeff (ThetaAddition.jacobi (unitC p) Z) = 0 ∧
    coeff 1 (ThetaAddition.jacobi (unitC p) Z) =
      -(((p:R)^2;(p:R)^2)_∞)^3*coeff 1 (Z:PowerSeries R) ∧
    coeff 2 (ThetaAddition.jacobi (unitC p) Z) =
      -(((p:R)^2;(p:R)^2)_∞)^3*coeff 2 (Z:PowerSeries R) := by
  have hp2 : IsTopologicallyNilpotent ((p:R)^2) := hp.pow (by decide)
  have hh := pochPair_coefficients ((p:R)^2) ((p:R)^2) Z hp2 hZ
    (summable_lambertTail _ _ hp2 hp2) (fun n => (hp2.mul_pow hp2 (n:=n)).isUnit_one_sub)
  have hc := pochPair_constant ((p:R)^2) ((p:R)^2) Z hp2 hZ
  rw [jacobi_parameter p Z hp]
  constructor
  · simp [hZ]
  constructor
  · simp [coeff_one_mul, hZ, hc, hh.1]
    ring
  · simp [coeff_two_mul, hZ, hc, hh.1]
    ring

end KanadeRussell.Infra.JacobiParameter
