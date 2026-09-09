import KanadeRussell.Product.LambertProgressions
import KanadeRussell.Product.LaurentSubstitution
set_option backward.isDefEq.respectTransparency false

/-! Identification of the elliptic Lambert tails with the original residue
series, under the injective substitution q=t². -/
open PowerSeries PowerSeries.WithPiTopology MvLaurentSeries
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Product.LevelNine
open Infra.JacobiJets
variable {R : Type*} [CommRing R] [Nontrivial R]

omit [Nontrivial R] in
theorem baseChange2_continuous : Continuous (baseChange2 (R := R)) := by
  unfold baseChange2
  fun_prop

@[simp] theorem baseChange2_q : baseChange2 (R := R) q = xPow () 2 := by
  apply intEval_X
  exact (isTopologicallyNilpotent_xPow_iff () 2).mpr (by decide)

theorem baseChange2_q_pow (k : ℕ) : baseChange2 (R := R) (q^k) = xPow () (2*(k:ℤ)) := by
  rw [map_pow, baseChange2_q, xPow_pow]

theorem baseChange2_lambertTerm (k : ℕ) (hk : 0 < k) :
    baseChange2 (R := R) (lambertTerm k) =
      xPow () (2*(k:ℤ)) * bInv (1-xPow () (2*(k:ℤ)))^2 := by
  have hu : IsUnit (1-q^k) :=
    (show IsTopologicallyNilpotent (q^k) by simp [q, hk.ne']).isUnit_one_sub
  simp only [lambertTerm, if_neg hk.ne', map_mul, map_pow,
    hu.map_bInv baseChange2, map_sub, map_one, baseChange2_q, xPow_pow]

theorem baseChange2_progression (r : ℕ) (hr : 0 < r) :
    baseChange2 (R := R) (lambertProgression r) =
      lambertTail (xPow () (2*(r:ℤ))) (xPow () 18) := by
  have h := (summable_lambertProgression r).hasSum.map (baseChange2 (R := R)) baseChange2_continuous
  have hu : IsTopologicallyNilpotent (xPow () (2*(r:ℤ)) : Laurent R) :=
    (isTopologicallyNilpotent_xPow_iff () _).mpr (by omega)
  have hQ : IsTopologicallyNilpotent (xPow () 18 : Laurent R) :=
    (isTopologicallyNilpotent_xPow_iff () 18).mpr (by decide)
  apply h.unique
  apply (summable_lambertTail _ _ hu hQ).hasSum.congr_fun
  intro n
  dsimp only [Function.comp_def]
  rw [baseChange2_lambertTerm _ (by omega), xPow_pow, ← xPow_add]
  have he : 2*((r+9*n : ℕ):ℤ) = 2*(r:ℤ)+18*(n:ℤ) := by push_cast; ring
  rw [he]

/-- The Lambert function in the formal difference formula is precisely the
image of the original residue-class series. -/
theorem S_eq_lambertResidue (r : ℕ) (hr : 0 < r) (hr9 : r < 9) :
    S (R := R) (r : ℤ) = baseChange2 (lambertResidue r) := by
  have he : 18-2*(r:ℤ) = 2*((9-r : ℕ):ℤ) := by
    rw [Nat.cast_sub (by omega : r ≤ 9)]
    push_cast
    ring
  rw [lambertResidue_eq_progressions r hr hr9, map_add,
    baseChange2_progression r hr, baseChange2_progression (9-r) (by omega)]
  simp only [S, ellipticLambert, tPow_two, tPow_div, tPow_val, xPow_pow, Nat.cast_ofNat, Int.reduceMul, he]

theorem baseChange2_E (d : ℕ) (hd : 0 < d) :
    baseChange2 (R := R) (E d) = (xPow () (2*(d:ℤ)); xPow () (2*(d:ℤ)))_∞ := by
  have hq : IsTopologicallyNilpotent (q^d) := by simp [q, hd.ne']
  rw [E, map_qPochhammerInf baseChange2 baseChange2_continuous _ hq, baseChange2_q_pow]

end KanadeRussell.Product.LevelNine
