import KanadeRussell.Source.Defs

/-! Coefficient lower-bound statement, proved by `KanadeRussell.lowerBounds` in
Theorems.lean. -/
open PowerSeries
namespace KanadeRussell

def LowerBounds : Prop :=
  (∀ n, coeff n K₁ ≤ coeff n A) ∧ (∀ n, coeff n K₂ ≤ coeff n B) ∧ (∀ n, coeff n K₃ ≤ coeff n C)

end KanadeRussell
