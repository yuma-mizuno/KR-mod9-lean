import KanadeRussell.Source.Norm
import KanadeRussell.Rigidity
import KanadeRussell.Pending.LowerBounds
import KanadeRussell.Pending.ProductNorm
set_option backward.isDefEq.respectTransparency false

/-! Level A′: the three formal-series identities from the two recorded external inputs. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell

theorem kanade_russell_of_lowerBounds_of_productNorm (h : LowerBounds) (h' : ProductNorm) :
    A = K₁ ∧ B = K₂ ∧ C = K₃ := by
  have hE (d : ℕ) : IsUnit (E (d + 1)) :=
    isUnit_qPochhammerInf (by simp [q])
  have hn : cubicNorm A B C = cubicNorm K₁ K₂ K₃ := by
    apply mul_left_cancel₀ (mul_ne_zero (hE 0).ne_zero (hE 2).ne_zero)
    exact sourceNorm.trans h'.symm
  obtain ⟨hA, hB, hC, hK1, hK2, hK3⟩ := constantCoeff_eq_one
  exact Rigidity.rigidity A B C K₁ K₂ K₃ hA hB hC hK1 hK2 hK3 h.1 h.2.1 h.2.2 hn

end KanadeRussell
