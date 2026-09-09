import KanadeRussell

/-! Historical exact-type checks for the earlier sixteen-target checkpoint.
The active four-target submission is the root Solution.lean. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell.Submitted

theorem kanade_russell_hasSum₁ : HasSum (sourceTerm 0 0) K₁ := by
  exact KanadeRussell.kanade_russell_hasSum₁

theorem kanade_russell_hasSum₂ : HasSum (sourceTerm 1 3) K₂ := by
  exact KanadeRussell.kanade_russell_hasSum₂

theorem kanade_russell_hasSum₃ : HasSum (sourceTerm 2 3) K₃ := by
  exact KanadeRussell.kanade_russell_hasSum₃

theorem kanade_russell₁ : A = K₁ := by
  exact KanadeRussell.kanade_russell₁

theorem kanade_russell₂ : B = K₂ := by
  exact KanadeRussell.kanade_russell₂

theorem kanade_russell₃ : C = K₃ := by
  exact KanadeRussell.kanade_russell₃

theorem kanade_russell_of_lowerBounds (h : LowerBounds) : A = K₁ ∧ B = K₂ ∧ C = K₃ := by
  exact KanadeRussell.kanade_russell_of_lowerBounds h

theorem kanade_russell_of_lowerBounds_of_productNorm (h : LowerBounds) (h' : ProductNorm) :
    A = K₁ ∧ B = K₂ ∧ C = K₃ := by
  exact KanadeRussell.kanade_russell_of_lowerBounds_of_productNorm h h'

theorem sourceNorm : E 1 * E 3 * cubicNorm A B C = a := by
  exact KanadeRussell.sourceNorm

theorem isUnit_qPochhammer_q (d m : ℕ) : IsUnit (q ^ (d + 1); q ^ (d + 1))_m := by
  exact KanadeRussell.isUnit_qPochhammer_q d m

theorem summable_sourceTerm (a b : ℕ) : Summable (sourceTerm a b) := by
  exact KanadeRussell.summable_sourceTerm a b

theorem hasProd_P9 (r : ℕ) :
    HasProd (fun i : ℕ ↦ 1 - q ^ (r + 1) * (q ^ 9) ^ i) (P9 (r + 1)) := by
  exact KanadeRussell.hasProd_P9 r

theorem K₁_mul : K₁ * (P9 1 * P9 3 * P9 6 * P9 8) = 1 := by
  exact KanadeRussell.K₁_mul

theorem K₂_mul : K₂ * (P9 2 * P9 3 * P9 6 * P9 7) = 1 := by
  exact KanadeRussell.K₂_mul

theorem K₃_mul : K₃ * (P9 3 * P9 4 * P9 5 * P9 6) = 1 := by
  exact KanadeRussell.K₃_mul

theorem constantCoeff_eq_one :
    constantCoeff A = 1 ∧ constantCoeff B = 1 ∧ constantCoeff C = 1 ∧
    constantCoeff K₁ = 1 ∧ constantCoeff K₂ = 1 ∧ constantCoeff K₃ = 1 := by
  exact KanadeRussell.constantCoeff_eq_one

end KanadeRussell.Submitted
