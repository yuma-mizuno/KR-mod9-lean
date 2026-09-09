import KanadeRussell.Infra.JacobiCube
import KanadeRussell.Product.A2Core
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Identification of the cubic Jacobi coefficients with the original A₂ series. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Product
open Infra.ThetaAddition
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

private theorem eval_int_pow (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (n : ℤ) (hn : 0 ≤ n) :
    intEval ((p:R)^2) (q^n.toNat) = ((p^(2*n):Rˣ):R) := by
  have hp2 := hp.pow (by decide : 2 ≠ 0)
  rw [map_pow, show intEval ((p:R)^2) q = (p:R)^2 from intEval_X hp2, ← pow_mul]
  simp only [← Units.val_pow_eq_pow_val, ← zpow_natCast, Nat.cast_mul,
    Nat.cast_ofNat, Int.toNat_of_nonneg hn]

theorem cubeCoeff_zero (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    cubeCoeff p 0 = intEval ((p:R)^2) a := by
  have hh := Infra.summable_a2.hasSum.map (intEval ((p:R)^2)) (by fun_prop)
  apply (summable_cubeCoeffTerm p 0 hp).hasSum.unique
  apply hh.congr_fun
  rintro ⟨r,s⟩
  dsimp only [Function.comp_def]
  rw [eval_int_pow p hp _ (Infra.a2_nonneg r s), cubeCoeffTerm_formula]
  simp only [zpow_zero, one_mul]
  congr 2
  ring

theorem cubeCoeff_one (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    cubeCoeff p 1 = -3*intEval ((p:R)^2) coreTheta := by
  have hc := summable_coreTheta.hasSum.map (intEval ((p:R)^2)) (by fun_prop)
  have ht := (hasSum_fintype (fun _ : Fin 3 => (-1:R))).mul_of_nonarchimedean' hc
  have hs : ∑ k : Fin 3, (-1:R) = -3 := by norm_num
  rw [hs] at ht
  have hh := Infra.CubeLattice.shiftedEquiv.hasSum_iff.mpr
    (summable_cubeCoeffTerm p 1 hp).hasSum
  apply hh.unique
  apply ht.congr_fun
  rintro ⟨k,r,s⟩
  change cubeCoeffTerm p 1 (Infra.CubeLattice.shifted k (r,s)) =
    -1 * intEval ((p:R)^2) (q^(coreExponent r s).toNat)
  rw [cubeCoeffTerm_formula, eval_int_pow p hp _ (coreExponent_nonneg r s)]
  have hn := Infra.CubeLattice.shifted_norm k r s
  have he : (1-(Infra.CubeLattice.shifted k (r,s)).1-(Infra.CubeLattice.shifted k (r,s)).2)*
        (1-(Infra.CubeLattice.shifted k (r,s)).1-(Infra.CubeLattice.shifted k (r,s)).2-1)+
      (Infra.CubeLattice.shifted k (r,s)).1*((Infra.CubeLattice.shifted k (r,s)).1-1)+
      (Infra.CubeLattice.shifted k (r,s)).2*((Infra.CubeLattice.shifted k (r,s)).2-1) =
      2*coreExponent r s := by
    dsimp only [coreExponent]
    nlinarith
  rw [he]
  simp

private def reflectPair : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun rs := (1-rs.1,1-rs.2)
  invFun rs := (1-rs.1,1-rs.2)
  left_inv := by rintro ⟨r,s⟩; simp
  right_inv := by rintro ⟨r,s⟩; simp

theorem cubeCoeff_two (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    cubeCoeff p 2 = 3*intEval ((p:R)^2) coreTheta := by
  have h1 := (summable_cubeCoeffTerm p 1 hp).hasSum.neg
  have he : cubeCoeff p 2 = -cubeCoeff p 1 := by
    apply (summable_cubeCoeffTerm p 2 hp).hasSum.unique
    apply reflectPair.hasSum_iff.mp
    apply h1.congr_fun
    rintro ⟨r,s⟩
    dsimp only [reflectPair, Equiv.coe_fn_mk, Function.comp_def]
    rw [cubeCoeffTerm_formula, cubeCoeffTerm_formula]
    norm_num only [zpow_ofNat, zpow_one, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one, neg_one_sq, one_mul, neg_mul, neg_neg]
    congr 2
    ring
  rw [he, cubeCoeff_one p hp]
  ring

/-- Jacobi cube dissection with the original A₂ theta and shifted-core coefficients. -/
theorem jacobi_cube_a2 (p z : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    (jacobi p z)^3 = intEval ((p:R)^2) a * jacobi (p^3) (z^3) -
      3*intEval ((p:R)^2) coreTheta*(z:R)*jacobi (p^3) (z^3*p^2) +
      3*intEval ((p:R)^2) coreTheta*(z:R)^2*jacobi (p^3) (z^3*p^4) := by
  have hh := jacobi_cube_dissection p z hp
  norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.sum_empty, add_zero, Nat.reduceAdd, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Nat.reduceMul, pow_zero, pow_one, mul_one] at hh
  rw [cubeCoeff_zero p hp, cubeCoeff_one p hp, cubeCoeff_two p hp] at hh
  convert hh using 1
  ring

end KanadeRussell.Product
