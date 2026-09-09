import KanadeRussell.Main
import KanadeRussell.Product.A2Square

/-! The three Kanade–Russell identities with only the coefficient lower bounds as input. -/
namespace KanadeRussell

theorem kanade_russell_of_lowerBounds (h : LowerBounds) : A = K₁ ∧ B = K₂ ∧ C = K₃ :=
  kanade_russell_of_lowerBounds_of_productNorm h productNorm

end KanadeRussell
