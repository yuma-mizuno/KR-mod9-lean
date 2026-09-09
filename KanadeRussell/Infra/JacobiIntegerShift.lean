import KanadeRussell.Infra.JacobiTrisection

/-! Integer shifts of an actual bilateral Jacobi function, with the exact unit
prefactor. This includes negative shifts and requires no Jacobi-unit premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.JacobiIntegerShift
open ThetaAddition
variable {R : Type*} [CommRing R]

def shiftFactor (p z : Rˣ) (n : ℤ) : Rˣ :=
  (-1)^n*p^(-n*(n-1))*z^(-n)

theorem shifted_term (p z : Rˣ) (n k : ℤ) :
    jacobiTerm p (p^(2*n)*z) k =
      (shiftFactor p z n : R)*jacobiTerm p z (k+n) := by
  have hs : (-1 : Rˣ)^n*(-1 : Rˣ)^(k+n)=(-1 : Rˣ)^k := by
    rw [← zpow_add, show n+(k+n)=2*n+k by ring, zpow_add, zpow_mul]
    norm_num [zpow_ofNat]
  simp only [jacobiTerm, shiftFactor, ← Units.val_mul, mul_zpow]
  congr 1
  calc
    _ = (-1 : Rˣ)^k*(p^((2*n)*k)*z^k*p^(k*(k-1))) := by group
    _ = _ := by
      rw [← hs]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R]

/-- Shifting an argument by any integral power of the Jacobi base. -/
theorem jacobi_shift (p z : Rˣ) (n : ℤ) (hp : IsTopologicallyNilpotent (p : R)) :
    jacobi p (p^(2*n)*z) = (shiftFactor p z n : R)*jacobi p z := by
  have hs := ((Equiv.addRight n).hasSum_iff.mpr (hasSum_jacobiTerm p z hp)).mul_left
    (shiftFactor p z n : R)
  apply (hasSum_jacobiTerm p (p^(2*n)*z) hp).unique
  apply hs.congr_fun
  intro k
  exact shifted_term p z n k

end KanadeRussell.Infra.JacobiIntegerShift
