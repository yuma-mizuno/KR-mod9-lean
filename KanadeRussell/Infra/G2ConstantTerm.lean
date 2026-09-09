import KanadeRussell.Infra.A2ConvolutionConstant
import KanadeRussell.Infra.G2JacobiCoefficients

/-! The genuine equal-base G2 constant coefficient, evaluated from the A2
convolution. The normalized value is Cooper's `E^(-2)`, with no constant-term
or denominator identity supplied as a premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped QTheory
namespace KanadeRussell.Infra.G2ConstantTerm
open A2JacobiCoefficients A2CoefficientResidues A2ConvolutionConstant
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

/-- The actual raw six-Jacobi coefficient at `(0,0)` equals the fourth Euler power. -/
theorem coefficient_zero (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    G2JacobiCoefficients.coefficient p 0 0=euler p^4 := by
  simpa only [G2JacobiCoefficients.coefficient,sub_self,zero_sub,neg_mul] using
    constant_convolution p hp

private theorem inverse_normalization (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    bInv (euler p)^6*euler p^4=bInv (euler p)^2 := by
  have hu : IsUnit (euler p) := isUnit_qPochhammerInf
    (hp.pow (by decide : 2 ≠ 0)) (hp.pow (by decide : 2 ≠ 0))
  calc
    _ = bInv (euler p)^2*(bInv (euler p)*euler p)^4 := by ring
    _ = _ := by rw [hu.bInv_mul_cancel]; ring

/-- The normalization of the actual six-Jacobi constant coefficient. -/
theorem normalized_coefficient_zero (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    bInv (euler p)^6*G2JacobiCoefficients.coefficient p 0 0=bInv (euler p)^2 := by
  rw [coefficient_zero p hp]
  exact inverse_normalization p hp

/-- The normalized coefficient convolution converges to the evaluated constant. -/
theorem hasSum_normalized_constant (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    HasSum (fun mn : ℤ × ℤ => normalizedCoefficient p (-2*mn.1+mn.2) (-mn.1-mn.2)*
      normalizedCoefficient p mn.1 mn.2) (bInv (euler p)^2) := by
  have hh := (hasSum_constant_convolution p hp).mul_left (bInv (euler p)^6)
  rw [inverse_normalization p hp] at hh
  apply hh.congr_fun
  intro mn
  simp only [normalizedCoefficient,euler]
  ring

theorem normalized_constant (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    (∑' mn : ℤ × ℤ, normalizedCoefficient p (-2*mn.1+mn.2) (-mn.1-mn.2)*
      normalizedCoefficient p mn.1 mn.2)=bInv (euler p)^2 :=
  (hasSum_normalized_constant p hp).tsum_eq

end KanadeRussell.Infra.G2ConstantTerm
