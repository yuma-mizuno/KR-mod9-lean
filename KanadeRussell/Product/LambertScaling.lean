import KanadeRussell.Product.LambertNorm
set_option backward.isDefEq.respectTransparency false

/-! Dilation of Lambert series and the resulting two-identity route to ProductNorm. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Product

theorem intEval_lambertTerm (d k : ℕ) (hd : 0 < d) :
    intEval (q^d) (lambertTerm k) = lambertTerm (d*k) := by
  by_cases hk : k = 0
  · simp [hk, lambertTerm]
  have hdk : d*k ≠ 0 := mul_ne_zero hd.ne' hk
  have hu : IsUnit (1-q^k) :=
    (show IsTopologicallyNilpotent (q^k) by simp [q, hk]).isUnit_one_sub
  have hq : IsTopologicallyNilpotent (q^d) := by simp [q, hd.ne']
  simp only [lambertTerm, if_neg hk, if_neg hdk, map_mul, map_pow,
    hu.map_bInv (intEval (q^d)), map_sub, map_one, q, intEval_X hq, ← pow_mul]

theorem intEval_lambert (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    intEval (q^d) (lambert e) = lambert (d*e) := by
  have h := (summable_lambert e he).hasSum.map (intEval (q^d)) (by fun_prop)
  apply h.unique
  apply (summable_lambert (d*e) (Nat.mul_pos hd he)).hasSum.congr_fun
  intro n
  simp only [Function.comp_def, intEval_lambertTerm d _ hd, mul_assoc]

/-- Only the square expansion and the trisection identity remain in this route.
The square expansion at q³ follows here by continuous substitution. -/
theorem productNorm_of_square_and_trisection
    (hsq : a^2 = 1 + 12*lambert 1 - 36*lambert 3)
    (htri : (a-intEval (q^3) a)*E 3 = 6*q*(E 9)^3) : ProductNorm := by
  have hsq₃ := congrArg (intEval (q^3)) hsq
  simp only [map_pow, map_sub, map_add, map_mul, map_one, map_ofNat,
    intEval_lambert 3 1 (by decide) (by decide),
    intEval_lambert 3 3 (by decide) (by decide), Nat.reduceMul] at hsq₃
  exact productNorm_of_theta_relations (intEval (q^3) a) hsq hsq₃ htri

end KanadeRussell.Product
