import KanadeRussell.Source.Defs

/-! Product-norm statement, proved by `KanadeRussell.productNorm` in
Product/A2Square.lean. -/
namespace KanadeRussell

def ProductNorm : Prop := E 1 * E 3 * cubicNorm K₁ K₂ K₃ = a

end KanadeRussell
