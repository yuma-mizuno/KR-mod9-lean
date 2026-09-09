import KanadeRussell.Infra.A2JacobiCoefficients
import KanadeRussell.Infra.JacobiIntegerShift
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped QTheory
namespace KanadeRussell.Infra.A2CoefficientResidues
open ThetaAddition A2JacobiCoefficients
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

/-- The complete integer quasi-periodicity of the actual bilateral Jacobi series. -/
theorem jacobi_integer_shift (p z : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (k : ℤ) :
    jacobi p (z*p^(2*k))=
      (↑(((-1:Rˣ)^k*z^(-k))*p^(-k*(k-1))):R)*jacobi p z := by
  simpa only [JacobiIntegerShift.shiftFactor,mul_comm,mul_left_comm,mul_assoc] using
    JacobiIntegerShift.jacobi_shift p z k hp

noncomputable def euler (p : Rˣ) : R := ((p:R)^2;(p:R)^2)_∞

def residueExponent (m n k r : ℤ) : ℤ :=
  m*(m-1)+n*(n-1)-3*k^2+(1-2*r)*k

/-- Separate the sum of the two coefficient indices modulo three. -/
theorem coefficient_class (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (m n k r : ℤ) (h : m+n=3*k+r) :
    coefficient p m n =
      (↑(((-1:Rˣ)^r)*p^(residueExponent m n k r)):R)*jacobi (p^3) (p^(4-2*r)) := by
  have hp3 : IsTopologicallyNilpotent ((p^3:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 3 ≠ 0)
  have ha : p^(4-2*r)*(p^3)^(2*(-k))=p^(4-2*m-2*n) := by
    simp only [← zpow_natCast,← zpow_mul,← zpow_add]
    congr 1
    norm_num only [Nat.cast_ofNat]
    omega
  have hj := jacobi_integer_shift (p^3) (p^(4-2*r)) hp3 (-k)
  rw [ha] at hj
  have hs : (-1:Rˣ)^(m+n)*(-1:Rˣ)^(-k)=(-1:Rˣ)^r := by
    rw [← zpow_add,show m+n+-k=r+2*k by omega,zpow_add,zpow_mul]
    norm_num [zpow_ofNat]
  unfold coefficient
  rw [hj,← mul_assoc]
  congr 1
  rw [← Units.val_mul]
  congr 1
  calc
    _ = ((-1:Rˣ)^(m+n)*(-1:Rˣ)^(-k))*
      (p^(m*(m-1)+n*(n-1))*(p^(4-2*r))^(-(-k))*(p^3)^(-(-k)*(-k-1))) := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul]
        abel
    _ = _ := by
      rw [hs]
      apply Additive.ofMul.injective
      simp only [ofMul_mul,ofMul_zpow,ofMul_pow,residueExponent]
      module

theorem coefficient_residue (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (m n k : ℤ) (r : Fin 3) (h : m+n=3*k+r) :
    coefficient p m n = if r=2 then 0 else
      (↑(((-1:Rˣ)^(r:ℤ))*p^(residueExponent m n k r)):R)*euler p := by
  rw [coefficient_class p hp m n k r h]
  have hp3 : IsTopologicallyNilpotent ((p^3:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 3 ≠ 0)
  have h0 : jacobi (p^3) (p^(4:ℤ))=euler p := by
    simpa [coefficient,euler] using coefficient_zero p hp
  have h1 : jacobi (p^3) (p^(2:ℤ))=euler p := by
    simpa only [zpow_ofNat,euler] using Product.jacobi_cubic_argument p hp
  fin_cases r <;> norm_num [h0,h1,jacobi_one_eq_zero (p^3) hp3] <;> simp_all [Fin.ext_iff]

/-- The occupied residue classes have one common quadratic exponent equation. -/
theorem residueExponent_identity (m n k : ℤ) (r : Fin 3)
    (h : m+n=3*k+r) (hr : r≠2) :
    3*residueExponent m n k r=2*(m^2+n^2-m*n-m-n) := by
  have hr01 : (r:ℤ)=0 ∨ (r:ℤ)=1 := by fin_cases r <;> simp_all
  rcases hr01 with hr0|hr1
  · have hh := congrArg (fun t : ℤ => t^2) h
    simp only [residueExponent,hr0] at *
    nlinarith [hh]
  · have hh := congrArg (fun t : ℤ => t^2) h
    simp only [residueExponent,hr1] at *
    nlinarith [hh]

end KanadeRussell.Infra.A2CoefficientResidues
