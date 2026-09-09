import KanadeRussell.Infra.JacobiTrisection

/-! Exact trisection of the bilateral Jacobi series. The proof partitions every
integer index into its residue modulo three and retains all monomial factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.JacobiSeriesDissection
open ThetaAddition

/-- Quotient and residue modulo three give an exact bilateral index bijection. -/
def residueEquiv : Fin 3 × ℤ ≃ ℤ where
  toFun rn := 3*rn.2+rn.1
  invFun n := (⟨(n%3).toNat, by omega⟩, n/3)
  left_inv := by
    rintro ⟨r,n⟩
    apply Prod.ext
    · apply Fin.ext
      simp only
      omega
    · simp only
      omega
  right_inv := by
    intro n
    simp only
    omega

variable {R : Type*} [CommRing R]

theorem jacobiTerm_residue (p z : Rˣ) (r n : ℤ) :
    jacobiTerm p z (3*n+r) =
      (↑(((-1 : Rˣ)^r*z^r)*p^(r*(r-1))) : R)*
        jacobiTerm (p^9) (z^3*p^(6*r+6)) n := by
  have hsign : (-1 : Rˣ)^(3*n+r) = (-1 : Rˣ)^r*(-1 : Rˣ)^n := by
    rw [zpow_add, zpow_mul]
    norm_num [zpow_ofNat, mul_comm]
  simp only [jacobiTerm, ← Units.val_mul]
  congr 1
  rw [hsign]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow]
  module

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R]

/-- The three residue series, with their exact prefactors, sum to the original Jacobi function. -/
theorem jacobi_residue_sum (p z : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    jacobi p z = ∑ r : Fin 3,
      (↑(((-1 : Rˣ)^(r : ℤ)*z^(r : ℤ))*p^((r : ℤ)*(r-1))) : R)*
        jacobi (p^9) (z^3*p^(6*(r : ℤ)+6)) := by
  have hp9 : IsTopologicallyNilpotent ((p^9 : Rˣ) : R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 9 ≠ 0)
  have hwhole := residueEquiv.hasSum_iff.mpr (hasSum_jacobiTerm p z hp)
  have hfiber (r : Fin 3) : HasSum (fun n : ℤ => jacobiTerm p z (3*n+r))
      ((↑(((-1 : Rˣ)^(r : ℤ)*z^(r : ℤ))*p^((r : ℤ)*(r-1))) : R)*
        jacobi (p^9) (z^3*p^(6*(r : ℤ)+6))) := by
    apply ((hasSum_jacobiTerm (p^9) (z^3*p^(6*(r : ℤ)+6)) hp9).mul_left
      (↑(((-1 : Rˣ)^(r : ℤ)*z^(r : ℤ))*p^((r : ℤ)*(r-1))) : R)).congr_fun
    intro n
    exact jacobiTerm_residue p z r n
  exact (hwhole.prod_fiberwise hfiber).unique (hasSum_fintype _)

/-- Explicit three-term Jacobi series dissection; no theta evaluation is an input. -/
theorem jacobi_trisection (p z : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    jacobi p z = jacobi (p^9) (z^3*p^6) -
      (z : R)*jacobi (p^9) (z^3*p^12) +
        (z : R)^2*(p : R)^2*jacobi (p^9) (z^3*p^18) := by
  rw [jacobi_residue_sum p z hp, Fin.sum_univ_three]
  norm_num [Units.val_mul, Units.val_pow_eq_pow_val, sub_eq_add_neg, zpow_ofNat]

end KanadeRussell.Infra.JacobiSeriesDissection
