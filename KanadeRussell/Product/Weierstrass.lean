import KanadeRussell.Infra.WeierstrassDifference
import RogersRamanujan.RingTheory.MvLaurentSeries.Basic
import KanadeRussell.Product.Defs
set_option backward.isDefEq.respectTransparency false

/-! The exact level-nine Weierstrass relation, with q=t² and a free unit z.
The coefficient ring is arbitrary, so formal auxiliary parameters are allowed. -/
namespace KanadeRussell.Product.LevelNine
open Infra.ThetaAddition MvLaurentSeries PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

variable {R : Type*} [CommRing R] [Nontrivial R]

abbrev Laurent (R : Type*) [Zero R] := MvLaurentSeries Unit R
noncomputable def tPow (n : ℤ) : (Laurent R)ˣ := xPowUnits () n

omit [Nontrivial R] in
theorem tPow_val (n : ℤ) : ((tPow (R := R) n : (Laurent R)ˣ) : Laurent R) = xPow () n := rfl

omit [Nontrivial R] in
theorem tPow_mul (m n : ℤ) : tPow (R := R) m * tPow n = tPow (m+n) := by
  apply Units.ext
  change xPow () m * xPow () n = xPow () (m+n)
  exact (xPow_add () m n).symm

omit [Nontrivial R] in
theorem tPow_inv (n : ℤ) : (tPow (R := R) n)⁻¹ = tPow (-n) := by
  apply Units.ext
  rfl

omit [Nontrivial R] in
theorem tPow_div (m n : ℤ) : tPow (R := R) m / tPow n = tPow (m-n) := by
  rw [div_eq_mul_inv, tPow_inv, tPow_mul, sub_eq_add_neg]

omit [Nontrivial R] in
theorem tPow_two (n : ℤ) : tPow (R := R) n ^ 2 = tPow (2*n) := by
  rw [pow_two, tPow_mul]
  congr 1
  ring

theorem nilpotent_tPow (n : ℤ) (hn : 0 < n) :
    IsTopologicallyNilpotent ((tPow (R := R) n : (Laurent R)ˣ) : Laurent R) := by
  change IsTopologicallyNilpotent (xPow () n : Laurent R)
  exact (isTopologicallyNilpotent_xPow_iff () n).mpr hn

noncomputable def J (n : ℤ) : Laurent R := jacobi (tPow 9) (tPow n)
noncomputable def shiftedJ (n : ℤ) (z : (Laurent R)ˣ) : Laurent R :=
  jacobi (tPow 9) (tPow n * z)

theorem isUnit_J (n : ℤ) (hn : 0 < n) (hn18 : n < 18) : IsUnit (J (R := R) n) := by
  apply isUnit_jacobi (tPow 9) (tPow n) (nilpotent_tPow 9 (by decide))
    (nilpotent_tPow n hn)
  rw [tPow_two, tPow_div]
  apply nilpotent_tPow
  omega

/-- A concrete Laurent-series identity for every r in the indicated range;
in particular r=1,2,4 gives the three required Weierstrass specializations. -/
theorem weierstrass (r : ℤ) (hr : 0 < r) (hr9 : r < 9) (z : (Laurent R)ˣ) :
    shiftedJ (2*r) z * shiftedJ (2*r) z⁻¹ * (J 6)^2 -
      shiftedJ 6 z * shiftedJ 6 z⁻¹ * (J (2*r))^2 =
      ((tPow 6 : (Laurent R)ˣ) : Laurent R) * ((z⁻¹ : (Laurent R)ˣ) : Laurent R) *
      J (2*r+6) * J (2*r-6) * (jacobi (tPow 9) z)^2 := by
  have hp := nilpotent_tPow (R := R) 9 (by decide)
  have hx := isUnit_J (R := R) (2*r) (by omega) (by omega)
  have h := weierstrass_addition (tPow 9) (tPow (2*r)) (tPow 6) z hp hx
  simpa only [kernel, shiftedJ, J, div_eq_mul_inv, tPow_inv, tPow_mul,
    ← sub_eq_add_neg, mul_assoc] using h

/-- Substitute q=t² in the original integer-coefficient power series. -/
noncomputable def baseChange2 : PowerSeries ℤ →+* Laurent R := intEval (xPow () 2)

/-- The specialized Jacobi product is exactly the existing level-nine product. -/
theorem J_even (r : ℕ) (hr9 : r < 9) :
    J (R := R) (2*(r : ℤ)) = baseChange2 (KanadeRussell.Product.J r) := by
  have hp := nilpotent_tPow (R := R) 9 (by decide)
  have ht : IsTopologicallyNilpotent (xPow () 2 : Laurent R) :=
    (isTopologicallyNilpotent_xPow_iff () 2).mpr (by decide)
  rw [J, jacobi_eq_product _ _ hp]
  simp only [← Units.val_pow_eq_pow_val, tPow_two, tPow_div]
  change (xPow () 18; xPow () 18)_∞ * (xPow () (2*(r:ℤ)); xPow () 18)_∞ *
      (xPow () (18-2*(r:ℤ)); xPow () 18)_∞ = _
  have hq : IsTopologicallyNilpotent (q ^ 9) := by simp [q]
  simp only [baseChange2, KanadeRussell.Product.J, E, P9, map_mul,
    map_qPochhammerInf (intEval (xPow () 2 : Laurent R)) (by fun_prop) _ hq,
    map_pow, q, intEval_X ht, xPow_pow]
  congr 2
  push_cast [Nat.cast_sub (by omega : r ≤ 9)]
  ring_nf

/-- The two progressions r and 9-r in the Laurent variable t, with q=t². -/
noncomputable def S (r : ℤ) : Laurent R :=
  Infra.JacobiJets.ellipticLambert (tPow 9) (tPow (2*r))

/-- The level-nine elliptic difference formula. The convergence and the
second-coefficient extraction are discharged, including for r=1,2,4. -/
theorem difference (r : ℤ) (hr : 0 < r) (hr9 : r < 9) :
    (J (R := R) (2*r))^2 * (J 6)^2 * (S r - S 3) =
      -((tPow 6 : (Laurent R)ˣ) : Laurent R) *
        (xPow () 18; xPow () 18)_∞^6 * J (2*r+6) * J (2*r-6) := by
  have hp := nilpotent_tPow (R := R) 9 (by decide)
  have hx := nilpotent_tPow (R := R) (2*r) (by omega)
  have hx' : IsTopologicallyNilpotent
      (((tPow 9)^2 / tPow (2*r) : (Laurent R)ˣ) : Laurent R) := by
    rw [tPow_two, tPow_div]
    apply nilpotent_tPow
    omega
  have hy := nilpotent_tPow (R := R) 6 (by decide)
  have hy' : IsTopologicallyNilpotent
      (((tPow 9)^2 / tPow 6 : (Laurent R)ˣ) : Laurent R) := by
    rw [tPow_two, tPow_div]
    exact nilpotent_tPow 12 (by decide)
  have hpow : ((tPow 9 : (Laurent R)ˣ) : Laurent R)^2 = xPow () 18 := by
    rw [tPow_val, xPow_pow]
    rfl
  have h := weierstrass_difference (tPow 9) (tPow (2*r)) (tPow 6) hp hx hx' hy hy'
  simpa only [J, S, kernel, tPow_mul, tPow_div, hpow, Int.reduceMul, mul_assoc] using h

end KanadeRussell.Product.LevelNine
