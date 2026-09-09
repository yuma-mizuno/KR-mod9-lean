import KanadeRussell.Source.Defs

/-! The frozen product-norm proposition P2. Discharged by `KanadeRussell.productNorm`
in Product/A2Square.lean; retained here for exact compatibility with the comparator. -/
namespace KanadeRussell

def ProductNorm : Prop := E 1 * E 3 * cubicNorm K₁ K₂ K₃ = a

end KanadeRussell
