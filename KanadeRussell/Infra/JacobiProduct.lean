import KanadeRussell.Infra.ThetaAddition
import RogersRamanujan.NumberTheory.QTheory.JacobiTripleProduct.Basic
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! The series used for Weierstrass addition is exactly the Jacobi product. -/
open scoped QTheory
namespace KanadeRussell.Infra.ThetaAddition
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

theorem jacobi_eq_product (p u : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    jacobi p u = ((p : R)^2; (p : R)^2)_∞ * ((u : R); (p : R)^2)_∞ *
      (((p^2/u : Rˣ) : R); (p : R)^2)_∞ := by
  have hpos : (-u/p)*p = -u := by simp
  have hneg : (-u/p)⁻¹*p = -(p^2/u) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_neg, inv_inv, neg_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [← zpow_natCast, ofMul_mul, ofMul_zpow, ofMul_inv]
    module
  have hm : u * (p^2/u) = p^2 := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  have ht := jacobi_triple_product_hasSum' hp2
    (show (u : R) * ((p^2/u : Rˣ) : R) = (p : R)^2 by
      simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using congrArg Units.val hm)
  apply (summable_theta p (-u/p) hp).hasSum.unique
  apply ht.congr_fun
  intro n
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [term_nat, abPow_nat]
    simp only [Int.natAbs_natCast]
    rw [← Units.val_mul, hpos]
    rfl
  · rw [term_neg_nat, term_nat, abPow_neg_nat]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    rw [← Units.val_mul, hneg]
    rfl

/-- The factor cancelled in the Weierstrass relation is a unit whenever both
Jacobi-product arguments are topologically nilpotent. -/
theorem isUnit_jacobi (p u : Rˣ) (hp : IsTopologicallyNilpotent (p : R))
    (hu : IsTopologicallyNilpotent (u : R))
    (hv : IsTopologicallyNilpotent ((p^2/u : Rˣ) : R)) : IsUnit (jacobi p u) := by
  rw [jacobi_eq_product p u hp]
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  exact ((isUnit_qPochhammerInf hp2 hp2).mul (isUnit_qPochhammerInf hu hp2)).mul
    (isUnit_qPochhammerInf hv hp2)

theorem jacobi_one_eq_zero (p : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    jacobi p 1 = 0 := by
  rw [jacobi_eq_product p 1 hp]
  simp

end KanadeRussell.Infra.ThetaAddition
