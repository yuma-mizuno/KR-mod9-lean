import KanadeRussell.Source.Defs

/-! External lower-bound input P1. This proposition is a hypothesis, not an axiom. -/
open PowerSeries
namespace KanadeRussell

def LowerBounds : Prop :=
  (∀ n, coeff n K₁ ≤ coeff n A) ∧ (∀ n, coeff n K₂ ≤ coeff n B) ∧ (∀ n, coeff n K₃ ≤ coeff n C)

end KanadeRussell
