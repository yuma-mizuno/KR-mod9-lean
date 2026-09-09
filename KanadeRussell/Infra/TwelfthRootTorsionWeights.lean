import Mathlib
import KanadeRussell.Infra.CyclotomicLambert

/-! Exact constants and Fourier weights at a primitive twelfth root. The odd
Fourier coefficient is u^(-m)-u^m, without a factor of two absorbed into its
definition. These are cyclotomic identities, not assertions about actual
Jacobi logarithmic jets or a Frobenius--Stickelberger identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.TwelfthRootTorsionWeights
variable {K : Type*} [Field K]

theorem pow_six (w : K) (hw : w^4-w^2+1=0) : w^6 = -1 := by
  linear_combination (w^2+1)*hw

theorem pow_twelve (w : K) (hw : w^4-w^2+1=0) : w^12 = 1 := by
  rw [show 12=6*2 by decide, pow_mul, pow_six w hw]
  norm_num

theorem root_ne_zero (w : K) (hw : w^4-w^2+1=0) : w ≠ 0 := by
  intro h
  simp [h] at hw

theorem pow_mod_twelve (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    w^n = w^(n%12) :=
  pow_eq_pow_of_modEq (by show n%12=(n%12)%12; omega) (pow_twelve w hw)

section Constants
variable [CharZero K]

/-- Explicit inverse of 1-w^(j+1), for j=0,...,5. -/
def denominatorInverse (w : K) : Fin 6 → K :=
  ![w^3+w^2, w^2, (w^3+1)/2, (w^2+1)/3, w^3-w^2+1, 1/2]

theorem denominatorInverse_spec (w : K) (hw : w^4-w^2+1=0) (j : Fin 6) :
    (1-w^(j.val+1))*denominatorInverse w j = 1 := by
  fin_cases j <;> norm_num [denominatorInverse]
  · linear_combination (-1)*hw
  · linear_combination (-1)*hw
  · linear_combination (-w^2/2 - 1/2)*hw
  · linear_combination (-w^2/3 - 2/3)*hw
  · linear_combination (-w^4 + w^3 - w^2)*hw
  · linear_combination (-w^2/2 - 1/2)*hw

theorem denominator_isUnit (w : K) (hw : w^4-w^2+1=0) (j : Fin 6) :
    IsUnit (1-w^(j.val+1)) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  have hs := denominatorInverse_spec w hw j
  rw [h, zero_mul] at hs
  exact zero_ne_one hs

theorem denominator_bInv (w : K) (hw : w^4-w^2+1=0) (j : Fin 6) :
    bInv (1-w^(j.val+1)) = denominatorInverse w j := by
  apply (denominator_isUnit w hw j).mul_left_cancel
  rw [(denominator_isUnit w hw j).mul_bInv_cancel, denominatorInverse_spec w hw j]

/-- The constant of the centered first logarithmic jet a(u)-1/2. -/
noncomputable def firstConstant (w : K) (j : Fin 6) : K :=
  -w^(j.val+1)*bInv (1-w^(j.val+1))-1/2

/-- The constant of the elliptic Lambert series at u=w^(j+1). -/
noncomputable def evenConstant (w : K) (j : Fin 6) : K :=
  w^(j.val+1)*bInv (1-w^(j.val+1))^2

theorem firstConstant_table (w : K) (hw : w^4-w^2+1=0) (j : Fin 6) :
    firstConstant w j =
      ![-w^3-w^2+1/2, 1/2-w^2, -w^3/2, 1/6-w^2/3, -w^3+w^2-1/2, 0] j := by
  rw [firstConstant, denominator_bInv w hw j]
  fin_cases j <;> norm_num [denominatorInverse]
  · linear_combination (-1)*hw
  · linear_combination (-1)*hw
  · linear_combination (-w^2/2 - 1/2)*hw
  · linear_combination (-w^2/3 - 2/3)*hw
  · linear_combination (-w^4 + w^3 - w^2)*hw
  · linear_combination (-w^2/2 - 1/2)*hw

theorem evenConstant_table (w : K) (hw : w^4-w^2+1=0) (j : Fin 6) :
    evenConstant w j = ![w^3-2*w-2, -1, -1/2, -1/3, -w^3+2*w-2, -1/4] j := by
  rw [evenConstant, denominator_bInv w hw j]
  fin_cases j <;> norm_num [denominatorInverse]
  · linear_combination (w^3 + 2*w^2 + 2*w + 2)*hw
  · linear_combination (w^2 + 1)*hw
  · linear_combination (w^5/4 + w^3/4 + w^2/2 + 1/2)*hw
  · linear_combination (w^4/9 + w^2/3 + 1/3)*hw
  · linear_combination (w^7 - 2*w^6 + 2*w^5 - w^3 + 2*w^2 - 2*w + 2)*hw
  · linear_combination (w^2/4 + 1/4)*hw

theorem firstConstant_T (w : K) (hw : w^4-w^2+1=0) :
    firstConstant w 0+firstConstant w 4 = -2*w^3 := by
  rw [firstConstant_table w hw, firstConstant_table w hw]
  change (-w^3-w^2+1/2)+(-w^3+w^2-1/2) = -2*w^3
  ring

theorem firstConstant_U (w : K) (hw : w^4-w^2+1=0) :
    -firstConstant w 0+2*firstConstant w 1+firstConstant w 4 = 0 := by
  rw [firstConstant_table w hw, firstConstant_table w hw, firstConstant_table w hw]
  change -(-w^3-w^2+1/2)+2*(1/2-w^2)+(-w^3+w^2-1/2) = 0
  ring

theorem evenConstant_combination (w : K) (hw : w^4-w^2+1=0) :
    evenConstant w 0+9*evenConstant w 1-2*evenConstant w 2+
      evenConstant w 3+evenConstant w 4+3*evenConstant w 5 = -157/12 := by
  simp only [evenConstant_table w hw]
  change (w^3-2*w-2)+9*(-1)-2*(-1/2)+(-1/3)+(-w^3+2*w-2)+3*(-1/4) = -157/12
  ring

end Constants

/-- Raw odd Fourier weight. For j≤12 this equals (w^j)^(-m)-(w^j)^m. -/
def oddFourier (w : K) (j m : ℕ) : K := w^((12-j)*m)-w^(j*m)

def evenFourier (w : K) (j m : ℕ) : K := w^((12-j)*m)+w^(j*m)

theorem oddFourier_eq_zpow (w : K) (hw : w^4-w^2+1=0) (j m : ℕ) (hj : j ≤ 12) :
    oddFourier w j m = (w^j)^(-(m : ℤ))-(w^j)^m := by
  have hinv : w^(12-j) = (w^j)⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ (root_ne_zero w hw))).mp
    rw [← pow_add, Nat.sub_add_cancel hj, pow_twelve w hw]
  simp only [oddFourier, pow_mul, hinv, zpow_neg, zpow_natCast, inv_pow]

theorem evenFourier_eq_zpow (w : K) (hw : w^4-w^2+1=0) (j m : ℕ) (hj : j ≤ 12) :
    evenFourier w j m = (w^j)^(-(m : ℤ))+(w^j)^m := by
  have hinv : w^(12-j) = (w^j)⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ (root_ne_zero w hw))).mp
    rw [← pow_add, Nat.sub_add_cancel hj, pow_twelve w hw]
  simp only [evenFourier, pow_mul, hinv, zpow_neg, zpow_natCast, inv_pow]

private theorem exponent_product_mod (w : K) (hw : w^4-w^2+1=0) (j m : ℕ) :
    w^(j*m) = w^(j*(m%12)) :=
  pow_eq_pow_of_modEq (by show (j*m)%12=(j*(m%12))%12; simp [Nat.mul_mod]) (pow_twelve w hw)

theorem oddFourier_mod (w : K) (hw : w^4-w^2+1=0) (j m : ℕ) :
    oddFourier w j m = oddFourier w j (m%12) := by
  exact congrArg₂ (fun a b : K => a-b) (exponent_product_mod w hw (12-j) m)
    (exponent_product_mod w hw j m)

theorem evenFourier_mod (w : K) (hw : w^4-w^2+1=0) (j m : ℕ) :
    evenFourier w j m = evenFourier w j (m%12) := by
  exact congrArg₂ (fun a b : K => a+b) (exponent_product_mod w hw (12-j) m)
    (exponent_product_mod w hw j m)

def tWeight : Fin 12 → ℤ := ![0,1,0,2,0,1,0,-1,0,-2,0,-1]
def uWeight : Fin 12 → ℤ := ![0,1,0,0,-2,-1,0,1,2,0,0,-1]
def eWeight : Fin 12 → ℤ := ![26,2,2,-22,-10,2,26,2,-10,-22,2,2]

theorem Fourier_T_finite (w : K) (hw : w^4-w^2+1=0) (m : Fin 12) :
    oddFourier w 1 m.val+oddFourier w 5 m.val = -2*w^3*(tWeight m : K) := by
  fin_cases m
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (w^7 + w^5 + w^3 - w)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (2*w^5 + 2*w^3)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (w^7 + w^5 + w^3 - w)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (-w^7 - w^5 - w^3 + w)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (-2*w^5 - 2*w^3)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (-w^7 - w^5 - w^3 + w)*hw

theorem Fourier_U_finite (w : K) (hw : w^4-w^2+1=0) (m : Fin 12) :
    -oddFourier w 1 m.val+2*oddFourier w 2 m.val+oddFourier w 5 m.val =
      -2*(2*w^2-1)*(uWeight m : K) := by
  fin_cases m
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (-w^7 + 2*w^6 - w^5 + 2*w^4 + w^3 + w - 2)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (-2*w^6 + 2*w^2)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (-4*w^4 - 4*w^2 + 4)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (w^7 - 2*w^6 + w^5 - 2*w^4 - w^3 - w + 2)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (-w^7 + 2*w^6 - w^5 + 2*w^4 + w^3 + w - 2)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (4*w^4 + 4*w^2 - 4)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (2*w^6 - 2*w^2)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (w^7 - 2*w^6 + w^5 - 2*w^4 - w^3 - w + 2)*hw

theorem Fourier_E_finite (w : K) (hw : w^4-w^2+1=0) (m : Fin 12) :
    evenFourier w 1 m.val+9*evenFourier w 2 m.val-2*evenFourier w 3 m.val+
      evenFourier w 4 m.val+evenFourier w 5 m.val+3*evenFourier w 6 m.val = (eWeight m : K) := by
  fin_cases m
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (w^7 + 9*w^6 - w^5 + 10*w^4 - w^3 + 7*w^2 + w - 2)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (2*w^6 + 12*w^4 + 6*w^2 + 4)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (24*w^2 + 24)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (12*w^4 + 12*w^2 + 12)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (w^7 + 9*w^6 - w^5 + 10*w^4 - w^3 + 7*w^2 + w - 2)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    ring
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (w^7 + 9*w^6 - w^5 + 10*w^4 - w^3 + 7*w^2 + w - 2)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (12*w^4 + 12*w^2 + 12)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (24*w^2 + 24)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (2*w^6 + 12*w^4 + 6*w^2 + 4)*hw
  · norm_num [oddFourier, evenFourier, tWeight, uWeight, eWeight, pow_mod_twelve w hw]
    linear_combination (w^7 + 9*w^6 - w^5 + 10*w^4 - w^3 + 7*w^2 + w - 2)*hw

theorem Fourier_T (w : K) (hw : w^4-w^2+1=0) (m : ℕ) :
    oddFourier w 1 m+oddFourier w 5 m = -2*w^3*(tWeight ⟨m%12, Nat.mod_lt _ (by decide)⟩ : K) := by
  rw [oddFourier_mod w hw 1 m, oddFourier_mod w hw 5 m]
  exact Fourier_T_finite w hw ⟨m%12, Nat.mod_lt _ (by decide)⟩

theorem Fourier_U (w : K) (hw : w^4-w^2+1=0) (m : ℕ) :
    -oddFourier w 1 m+2*oddFourier w 2 m+oddFourier w 5 m =
      -2*(2*w^2-1)*(uWeight ⟨m%12, Nat.mod_lt _ (by decide)⟩ : K) := by
  rw [oddFourier_mod w hw 1 m, oddFourier_mod w hw 2 m, oddFourier_mod w hw 5 m]
  exact Fourier_U_finite w hw ⟨m%12, Nat.mod_lt _ (by decide)⟩

theorem Fourier_E (w : K) (hw : w^4-w^2+1=0) (m : ℕ) :
    evenFourier w 1 m+9*evenFourier w 2 m-2*evenFourier w 3 m+
      evenFourier w 4 m+evenFourier w 5 m+3*evenFourier w 6 m =
      (eWeight ⟨m%12, Nat.mod_lt _ (by decide)⟩ : K) := by
  rw [evenFourier_mod w hw 1 m, evenFourier_mod w hw 2 m, evenFourier_mod w hw 3 m,
    evenFourier_mod w hw 4 m, evenFourier_mod w hw 5 m, evenFourier_mod w hw 6 m]
  exact Fourier_E_finite w hw ⟨m%12, Nat.mod_lt _ (by decide)⟩

/-- The even Fourier trace as a divisor-indicator function, including m=0. -/
theorem eWeight_dvd (m : ℕ) :
    eWeight ⟨m%12, Nat.mod_lt _ (by decide)⟩ =
      2-24*(if 3 ∣ m then 1 else 0)-12*(if 4 ∣ m then 1 else 0)+
        48*(if 6 ∣ m then 1 else 0)+12*(if 12 ∣ m then 1 else 0) := by
  have h3 : (3 ∣ m) ↔ 3 ∣ m%12 := by omega
  have h4 : (4 ∣ m) ↔ 4 ∣ m%12 := by omega
  have h6 : (6 ∣ m) ↔ 6 ∣ m%12 := by omega
  have h12 : (12 ∣ m) ↔ 12 ∣ m%12 := by omega
  simp only [h3, h4, h6, h12]
  exact (by decide : ∀ s : Fin 12, eWeight s =
    2-24*(if 3 ∣ s.val then 1 else 0)-12*(if 4 ∣ s.val then 1 else 0)+
      48*(if 6 ∣ s.val then 1 else 0)+12*(if 12 ∣ s.val then 1 else 0))
        ⟨m%12, Nat.mod_lt _ (by decide)⟩

theorem square_imaginary (w : K) (hw : w^4-w^2+1=0) : (w^3)^2 = -1 := by
  rw [← pow_mul]
  exact pow_six w hw

theorem square_sqrt_neg_three (w : K) (hw : w^4-w^2+1=0) : (2*w^2-1)^2 = -3 := by
  linear_combination 4*hw

end KanadeRussell.Infra.TwelfthRootTorsionWeights
