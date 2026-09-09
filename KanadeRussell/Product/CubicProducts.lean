import KanadeRussell.Product.JacobiCube
set_option backward.isDefEq.respectTransparency false

/-! The products and unit normalizations used in the cubic Jacobi comparison. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Product
open Infra.ThetaAddition
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

theorem intEval_E_of_nilpotent (x : R) (hx : IsTopologicallyNilpotent x)
    (d : ℕ) (hd : 0 < d) : intEval x (E d) = (x^d;x^d)_∞ := by
  have hq : IsTopologicallyNilpotent (q^d) := by simp [q, hd.ne']
  rw [E, map_qPochhammerInf (intEval x) (by fun_prop) _ hq, map_pow,
    show intEval x q = x from intEval_X hx]

theorem jacobi_cubic_argument (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    jacobi (p^3) (p^2) = ((p:R)^2;(p:R)^2)_∞ := by
  have hp2 : IsTopologicallyNilpotent ((p:R)^2) := hp.pow (by decide)
  have hp3 : IsTopologicallyNilpotent ((p^3:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 3 ≠ 0)
  have he : (p^3)^2/p^2 = p^4 := by
    apply Additive.ofMul.injective
    simp only [← zpow_natCast, ofMul_div, ofMul_zpow]
    module
  have hh := qPochhammerInf_eq_prod_range (a:=(p:R)^2) (m:=3) (by decide) hp2
  norm_num only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, one_mul,
    mul_one, pow_one, ← pow_mul, ← pow_add, Nat.reduceMul, Nat.reduceAdd] at hh
  rw [jacobi_eq_product _ _ hp3, he]
  simp only [Units.val_pow_eq_pow_val, ← pow_mul, Nat.reduceMul]
  rw [hh]
  ring

/-- The core coefficient and the level-three Jacobi value have product E₃³. -/
theorem core_cubic_product (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    intEval ((p:R)^2) coreTheta * jacobi (p^3) (p^2) = (((p:R)^6;(p:R)^6)_∞)^3 := by
  have hp2 : IsTopologicallyNilpotent ((p:R)^2) := hp.pow (by decide)
  have hh := congrArg (intEval ((p:R)^2)) coreTheta_product
  simp only [map_mul, map_pow, intEval_E_of_nilpotent _ hp2 1 (by decide),
    intEval_E_of_nilpotent _ hp2 3 (by decide), pow_one, ← pow_mul, Nat.reduceMul] at hh
  rw [jacobi_cubic_argument p hp]
  rw [mul_comm]
  exact hh

end KanadeRussell.Product
