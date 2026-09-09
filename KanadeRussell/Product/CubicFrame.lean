import KanadeRussell.Product.CubicProducts
import KanadeRussell.Infra.JacobiFunctorial
import KanadeRussell.Infra.CubicRelations
import KanadeRussell.Infra.LambertUnitArgument
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! The normalized Jacobi series in the cubic comparison. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped QTheory
namespace KanadeRussell.Product.CubicFrame
open Infra.ThetaAddition Infra.JacobiJets Infra.JacobiParameter
open Infra.CubicSeriesAlgebra
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def e (p : Rˣ) : R := (((p:R)^6;(p:R)^6)_∞)^3
noncomputable def j (p : Rˣ) : R := jacobi (p^3) (p^2)
noncomputable def H (p : Rˣ) (Z : (PowerSeries R)ˣ) : PowerSeries R :=
  PowerSeries.C (bInv (e p))*jacobi (unitC (p^3)) (Z^3)
noncomputable def B (p : Rˣ) (Z : (PowerSeries R)ˣ) : PowerSeries R :=
  PowerSeries.C (bInv (j p))*jacobi (unitC (p^3)) (unitC (p^2)*Z^3)
noncomputable def D (p : Rˣ) (Z : (PowerSeries R)ˣ) : PowerSeries R :=
  PowerSeries.C (bInv (j p))*jacobi (unitC (p^3)) (unitC (p^4)*Z^3)

theorem e_unit (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) : IsUnit (e p) := by
  exact (isUnit_qPochhammerInf (hp.pow (by decide : 6 ≠ 0)) (hp.pow (by decide : 6 ≠ 0))).pow 3

theorem j_unit (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) : IsUnit (j p) := by
  rw [j, jacobi_cubic_argument p hp]
  exact isUnit_qPochhammerInf (hp.pow (by decide : 2 ≠ 0)) (hp.pow (by decide : 2 ≠ 0))

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
theorem jacobi_complement (p u : Rˣ) : jacobi p (p^2/u) = jacobi p u := by
  have hh := theta_inv p (-u/p)
  have he : -(p^2/u)/p = (-u/p)⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_neg, inv_inv, neg_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [← zpow_natCast, ofMul_mul, ofMul_zpow, ofMul_inv]
    module
  rw [jacobi, he, hh]
  rfl

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
theorem level_complement (p : Rˣ) : (p^3)^2/p^2 = p^4 := by
  apply Additive.ofMul.injective
  simp only [← zpow_natCast, ofMul_div, ofMul_zpow]
  module

theorem normalized_cube (p v : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (hv : v^3 = 1) :
    (jacobi (unitC p) (unitC v*Z))^3 = PowerSeries.C (e p)*
      (PowerSeries.C (intEval ((p:R)^2) a)*H p Z -
        PowerSeries.C (3*(v:R))*(Z:PowerSeries R)*B p Z +
        PowerSeries.C (3*(v:R)^2)*(Z:PowerSeries R)^2*D p Z) := by
  have hE := e_unit p hp
  have hJ := j_unit p hp
  have hc : intEval ((p:R)^2) coreTheta = e p*bInv (j p) := by
    have hh := congrArg (fun x : R => x*bInv (j p)) (core_cubic_product p hp)
    change (intEval ((p:R)^2) coreTheta*j p)*bInv (j p) = e p*bInv (j p) at hh
    simpa only [mul_assoc, hJ.mul_bInv_cancel, mul_one] using hh
  have hpow : (unitC v*Z)^3 = Z^3 := by
    simp only [mul_pow, unitC, ← map_pow, hv, map_one, one_mul]
  have h2 : (unitC p)^2 = unitC (p^2) := by simp only [unitC, map_pow]
  have h3 : (unitC p)^3 = unitC (p^3) := by simp only [unitC, map_pow]
  have h4 : (unitC p)^4 = unitC (p^4) := by simp only [unitC, map_pow]
  have hh := jacobi_cube_a2 (unitC p) (unitC v*Z) (hp.map continuous_C)
  simp only [hpow, h2, h3, h4, Units.val_mul, unitC_val, ← map_pow,
    intEval_C _ (hp.pow (by decide : 2 ≠ 0)), hc] at hh
  rw [mul_comm (Z^3) (unitC (p^2)), mul_comm (Z^3) (unitC (p^4))] at hh
  rw [hh]
  unfold H B D
  have heC : PowerSeries.C (e p)*PowerSeries.C (bInv (e p)) = (1:PowerSeries R) := by
    rw [← map_mul, hE.mul_bInv_cancel, map_one]
  simp only [map_mul, map_pow, map_ofNat]
  linear_combination -(PowerSeries.C (intEval ((p:R)^2) a)*
    jacobi (unitC (p^3)) (Z^3))*heC


theorem constants (p : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (hZ : constantCoeff (Z:PowerSeries R) = 1) :
    constantCoeff (H p Z) = 0 ∧ constantCoeff (B p Z) = 1 ∧ constantCoeff (D p Z) = 1 := by
  have hp3 : IsTopologicallyNilpotent ((p^3:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 3 ≠ 0)
  have hZ3 : constantCoeff ((Z^3:(PowerSeries R)ˣ):PowerSeries R) = 1 := by
    simp only [Units.val_pow_eq_pow_val, map_pow, hZ, one_pow]
  have hH := jacobi_parameter_coefficients (p^3) (Z^3) hp3 hZ3
  have hB := jacobi_argument_constant (p^3) (p^2) (Z^3) hp3 hZ3
  have hD := jacobi_argument_constant (p^3) (p^4) (Z^3) hp3 hZ3
  have hj : jacobi (p^3) (p^4) = j p := by
    rw [← level_complement p, jacobi_complement]
    rfl
  rw [hj] at hD
  simp only [H, B, D, map_mul, constantCoeff_C, hH.1, hB, hD, mul_zero]
  exact ⟨trivial, (j_unit p hp).bInv_mul_cancel, (j_unit p hp).bInv_mul_cancel⟩

theorem H_first (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    coeff 1 (H p oneAddX) = -3 := by
  have hp3 : IsTopologicallyNilpotent ((p^3:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 3 ≠ 0)
  have hz : constantCoeff (((oneAddX:(PowerSeries R)ˣ)^3:(PowerSeries R)ˣ):PowerSeries R) = 1 := by simp
  have hh := (jacobi_parameter_coefficients (p^3) (oneAddX^3) hp3 hz).2.1
  simp only [Units.val_pow_eq_pow_val, ← pow_mul, Nat.reduceMul, oneAddX_val,
    coeff_one_cube, map_add, map_one, constantCoeff_X, coeff_one, coeff_X] at hh
  norm_num at hh
  rw [H, coeff_C_mul, hh]
  change bInv (e p)*(-(e p*3)) = -3
  have he := (e_unit p hp).bInv_mul_cancel
  linear_combination -3*he

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
theorem BD_kernel (p : Rˣ) (Z : (PowerSeries R)ˣ) :
    B p Z*D p Z = PowerSeries.C (bInv (j p)^2)*kernel (unitC (p^3)) (unitC (p^2)) (Z^3) := by
  have he : (unitC (p^3))^2/(unitC (p^2)/Z^3) = unitC (p^4)*Z^3 := by
    have hl : (unitC (p^3))^2/unitC (p^2) = unitC (p^4) := by
      simp only [unitC, ← map_pow, ← map_div, level_complement]
    rw [div_div_eq_mul_div, mul_div_right_comm, hl]
  have hh := jacobi_complement (unitC (p^3)) (unitC (p^2)/Z^3)
  rw [he] at hh
  rw [B, D, kernel, ← hh, map_pow]
  ring

theorem BD_coefficients (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    coeff 1 (B p oneAddX*D p oneAddX) = 0 ∧
    coeff 2 (B p oneAddX*D p oneAddX) = -9*ellipticLambert (p^3) (p^2) := by
  have hp3 : IsTopologicallyNilpotent ((p^3:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 3 ≠ 0)
  have hp2 : IsTopologicallyNilpotent ((p^2:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 2 ≠ 0)
  have hp4 : IsTopologicallyNilpotent (((p^3)^2/p^2:Rˣ):R) := by
    rw [level_complement]
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 4 ≠ 0)
  have hz : constantCoeff (((oneAddX:(PowerSeries R)ˣ)^3:(PowerSeries R)ˣ):PowerSeries R) = 1 := by simp
  have hh := kernel_coefficients_nilpotent (p^3) (p^2) (oneAddX^3) hp3 hz hp2 hp4
  rw [BD_kernel]
  constructor
  · simp only [coeff_C_mul, hh.1, mul_zero]
  · rw [coeff_C_mul, hh.2]
    simp only [Units.val_pow_eq_pow_val, oneAddX_val, coeff_one_cube,
      map_add, map_one, constantCoeff_X, coeff_one, coeff_X]
    norm_num
    change bInv (j p)^2*((j p)^2*ellipticLambert (p^3) (p^2)*9) = _
    have hj : bInv (j p)^2*(j p)^2 = 1 := by
      rw [← mul_pow, (j_unit p hp).bInv_mul_cancel, one_pow]
    linear_combination (9*ellipticLambert (p^3) (p^2))*hj


theorem cube_expression (p v : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (hv : v^3 = 1) :
    (jacobi (unitC p) (unitC v*oneAddX))^3 = PowerSeries.C (e p)*
      expression (intEval ((p:R)^2) a) (v:R) (H p oneAddX) (B p oneAddX) (D p oneAddX) := by
  have hh := normalized_cube p v oneAddX hp hv
  simpa only [oneAddX_val, expression, pow_two, mul_assoc] using hh

theorem root_product (p v : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (hv : v^3 = 1) :
    jacobi (unitC p) (unitC v*Z)*jacobi (unitC p) (unitC (v^2)*Z) =
      -PowerSeries.C ((v:R)^2)*(Z:PowerSeries R)*kernel (unitC p) (unitC v) Z := by
  have hi : v⁻¹ = v^2 := by
    apply mul_left_cancel (a:=v)
    rw [mul_inv_cancel, ← pow_succ', hv]
  have he : (unitC v/Z)⁻¹ = unitC (v^2)*Z := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, unitC, ← map_inv, hi]
    ac_rfl
  have hh := jacobi_inv (unitC p) (unitC v/Z) (hp.map continuous_C)
  rw [he] at hh
  rw [hh, kernel]
  simp only [Units.val_mul, unitC_val, Units.val_pow_eq_pow_val]
  ring

/-- The convergent cube and kernel identities imply the unnormalized Lambert square. -/
theorem square_elliptic (p v : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (hw : (v:R)^2+(v:R)+1 = 0) (h6 : IsUnit (6:R)) (hv0 : IsUnit (1-(v:R))) :
    (intEval ((p:R)^2) a)^2 =
      9*ellipticLambert (p^3) (p^2)-3*ellipticLambert p v := by
  have hw3 : (v:R)^3 = 1 := by linear_combination ((v:R)-1)*hw
  have hv : v^3 = 1 := Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hw3)
  have hv2 : (v^2)^3 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hv, one_pow]
  have hp2 : IsTopologicallyNilpotent ((p:R)^2) := hp.pow (by decide)
  have hroot : IsTopologicallyNilpotent ((v:R)*(p:R)^2) :=
    root_mul_nilpotent (v:R) ((p:R)^2) (by decide : 3 ≠ 0) hw3 hp2
  have hcomp : IsTopologicallyNilpotent (((p^2/v:Rˣ):R)) := by
    have hi : v⁻¹ = v^2 := by
      apply mul_left_cancel (a:=v)
      rw [mul_inv_cancel, ← pow_succ', hv]
    have hr := root_mul_nilpotent ((v:R)^2) ((p:R)^2) (by decide : 3 ≠ 0)
      (by rw [← pow_mul, Nat.mul_comm, pow_mul, hw3, one_pow]) hp2
    simpa only [div_eq_mul_inv, hi, Units.val_mul, Units.val_pow_eq_pow_val, mul_comm] using hr
  have hz : constantCoeff ((oneAddX:(PowerSeries R)ˣ):PowerSeries R) = 1 := by simp
  have hk := kernel_coefficients_of_shift p v oneAddX hp hz hroot hv0
    (hcomp.mul_pow hp2 (n:=1) |>.congr (by simp)) hcomp.isUnit_one_sub
  have hk0 := kernel_constant p v oneAddX hp hz
  have hh := constants p oneAddX hp hz
  have hc := cube_expression p (1:Rˣ) hp (by simp)
  have hf := (jacobi_parameter_coefficients p oneAddX hp hz).1
  have hpr := root_product p v oneAddX hp hv
  simp only [oneAddX_val] at hpr
  have hk2 : coeff 2 (kernel (unitC p) (unitC v) oneAddX) =
      -constantCoeff (kernel (unitC p) (unitC v) oneAddX)*ellipticLambert p v := by
    rw [hk.2, hk0]
    simp only [oneAddX_val, map_add, coeff_one, coeff_X]
    norm_num
  have hc0 : (jacobi (unitC p) oneAddX)^3 = PowerSeries.C (e p)*
      expression (intEval ((p:R)^2) a) 1 (H p oneAddX) (B p oneAddX) (D p oneAddX) := by
    simpa only [unitC, map_one, one_mul, Units.val_one] using hc
  exact square_of_cube_relations (intEval ((p:R)^2) a) (v:R)
    (ellipticLambert (p^3) (p^2)) (ellipticLambert p v) (e p)
    (H p oneAddX) (B p oneAddX) (D p oneAddX)
    (jacobi (unitC p) oneAddX) (jacobi (unitC p) (unitC v*oneAddX))
    (jacobi (unitC p) (unitC (v^2)*oneAddX)) (kernel (unitC p) (unitC v) oneAddX)
    h6 (e_unit p hp) hw hh.1 (H_first p hp) hh.2.1 hh.2.2
    (BD_coefficients p hp).1 (BD_coefficients p hp).2 hf hc0
    (cube_expression p v hp hv) (by simpa only [Units.val_pow_eq_pow_val] using cube_expression p (v^2) hp hv2)
    hpr hk.1 hk2

end KanadeRussell.Product.CubicFrame
