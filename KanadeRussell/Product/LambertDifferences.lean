import KanadeRussell.Product.LambertComparison
set_option backward.isDefEq.respectTransparency false

/-! The three exact Lambert differences used in the product-norm trace.
These are identities in the original integer-coefficient power-series ring. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Product

theorem J_reflect (r : ℕ) (hr : r ≤ 9) : J (9-r) = J r := by
  simp only [J, Nat.sub_sub_self hr]
  ring

theorem J_three : J 3 = E 3 := by
  rw [J, E_three_split]
  norm_num only [Nat.reduceSub]
  ring

namespace LevelNine
open Infra.ThetaAddition MvLaurentSeries
variable {R : Type*} [CommRing R] [Nontrivial R]

theorem J_neg (n : ℤ) : J (R := R) (-n) =
    -((tPow (-n) : (Laurent R)ˣ) : Laurent R) * J n := by
  rw [J, ← tPow_inv, jacobi_inv _ _ (nilpotent_tPow 9 (by decide)), tPow_inv]
  rfl

private theorem J_six : J (R := R) 6 = baseChange2 (E 3) := by
  simpa only [Nat.cast_ofNat, Int.reduceMul, Product.J_three] using J_even (R := R) 3 (by decide)

end LevelNine

/-- First of the three Weierstrass differences, with all denominators cleared. -/
theorem lambert_difference_one :
    (J 1)^2 * (E 3)^2 * (lambertResidue 1 - lambertResidue 3) =
      q * (E 9)^6 * J 2 * J 4 := by
  let F := LevelNine.baseChange2 (R := ℤ)
  have h := LevelNine.difference (R := ℤ) 1 (by decide) (by decide)
  norm_num only [Int.reduceMul, Int.reduceAdd, Int.reduceSub] at h
  have j1 := LevelNine.J_even (R := ℤ) 1 (by decide)
  have j2 := LevelNine.J_even (R := ℤ) 2 (by decide)
  have j4 := LevelNine.J_even (R := ℤ) 4 (by decide)
  have s1 := LevelNine.S_eq_lambertResidue (R := ℤ) 1 (by decide) (by decide)
  have s3 := LevelNine.S_eq_lambertResidue (R := ℤ) 3 (by decide) (by decide)
  have e9 := LevelNine.baseChange2_E (R := ℤ) 9 (by decide)
  norm_num only [Nat.cast_ofNat, Int.reduceMul] at j1 j2 j4 s1 s3 e9
  rw [LevelNine.J_neg 4, j1, j2, j4, LevelNine.J_six,
    s1, s3, ← e9] at h
  have hm : ((LevelNine.tPow 6 : (LevelNine.Laurent ℤ)ˣ) : LevelNine.Laurent ℤ) *
      ((LevelNine.tPow (-4) : (LevelNine.Laurent ℤ)ˣ) : LevelNine.Laurent ℤ) = F q := by
    dsimp only [F]
    rw [← Units.val_mul, LevelNine.tPow_mul, LevelNine.baseChange2_q]
    rfl
  apply LevelNine.baseChange2_injective
  simp only [map_mul, map_pow, map_sub]
  linear_combination h + F (E 9)^6 * F (J 2) * F (J 4) * hm

/-- Second Weierstrass difference in the original power-series ring. -/
theorem lambert_difference_two :
    (J 2)^2 * (E 3)^2 * (lambertResidue 2 - lambertResidue 3) =
      q^2 * (E 9)^6 * J 1 * J 4 := by
  let F := LevelNine.baseChange2 (R := ℤ)
  have h := LevelNine.difference (R := ℤ) 2 (by decide) (by decide)
  norm_num only [Int.reduceMul, Int.reduceAdd, Int.reduceSub] at h
  have j1 := LevelNine.J_even (R := ℤ) 1 (by decide)
  have j2 := LevelNine.J_even (R := ℤ) 2 (by decide)
  have j5 := LevelNine.J_even (R := ℤ) 5 (by decide)
  have jsym : J 5 = J 4 := J_reflect 4 (by decide)
  rw [jsym] at j5
  have s2 := LevelNine.S_eq_lambertResidue (R := ℤ) 2 (by decide) (by decide)
  have s3 := LevelNine.S_eq_lambertResidue (R := ℤ) 3 (by decide) (by decide)
  have e9 := LevelNine.baseChange2_E (R := ℤ) 9 (by decide)
  norm_num only [Nat.cast_ofNat, Int.reduceMul] at j1 j2 j5 s2 s3 e9
  rw [LevelNine.J_neg 2, j1, j2, j5, LevelNine.J_six, s2, s3, ← e9] at h
  have hm : ((LevelNine.tPow 6 : (LevelNine.Laurent ℤ)ˣ) : LevelNine.Laurent ℤ) *
      ((LevelNine.tPow (-2) : (LevelNine.Laurent ℤ)ˣ) : LevelNine.Laurent ℤ) = F (q^2) := by
    dsimp only [F]
    rw [← Units.val_mul, LevelNine.tPow_mul, LevelNine.baseChange2_q_pow]
    rfl
  apply LevelNine.baseChange2_injective
  simp only [map_mul, map_pow, map_sub] at hm ⊢
  linear_combination h + F (E 9)^6 * F (J 1) * F (J 4) * hm

/-- Third Weierstrass difference, including its negative sign. -/
theorem lambert_difference_four :
    (J 4)^2 * (E 3)^2 * (lambertResidue 4 - lambertResidue 3) =
      -q^3 * (E 9)^6 * J 1 * J 2 := by
  have h := LevelNine.difference (R := ℤ) 4 (by decide) (by decide)
  norm_num only [Int.reduceMul, Int.reduceAdd, Int.reduceSub] at h
  have j1 := LevelNine.J_even (R := ℤ) 1 (by decide)
  have j4 := LevelNine.J_even (R := ℤ) 4 (by decide)
  have j7 := LevelNine.J_even (R := ℤ) 7 (by decide)
  have jsym : J 7 = J 2 := J_reflect 2 (by decide)
  rw [jsym] at j7
  have s4 := LevelNine.S_eq_lambertResidue (R := ℤ) 4 (by decide) (by decide)
  have s3 := LevelNine.S_eq_lambertResidue (R := ℤ) 3 (by decide) (by decide)
  have e9 := LevelNine.baseChange2_E (R := ℤ) 9 (by decide)
  norm_num only [Nat.cast_ofNat, Int.reduceMul] at j1 j4 j7 s4 s3 e9
  rw [j1, j4, j7, LevelNine.J_six, s4, s3, ← e9] at h
  have hm : ((LevelNine.tPow 6 : (LevelNine.Laurent ℤ)ˣ) : LevelNine.Laurent ℤ) =
      LevelNine.baseChange2 (q^3) := by
    rw [LevelNine.baseChange2_q_pow]
    rfl
  rw [hm] at h
  apply LevelNine.baseChange2_injective
  simp only [map_mul, map_pow, map_sub, map_neg] at h ⊢
  linear_combination h

end KanadeRussell.Product
