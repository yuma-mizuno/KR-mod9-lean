import Mathlib
import RogersRamanujan
set_option backward.isDefEq.respectTransparency false

/-! Definitions copied verbatim from the frozen comparator; no specification proofs are imported. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell

noncomputable abbrev q : PowerSeries ℤ := PowerSeries.X

noncomputable def sourceTerm (a b : ℕ) : ℕ × ℕ → PowerSeries ℤ
  | (m, n) => q ^ (m ^ 2 + 3 * m * n + 3 * n ^ 2 + a * m + b * n)
      * bInv (q; q)_m * bInv (q ^ 3; q ^ 3)_n

noncomputable def A : PowerSeries ℤ := ∑' mn, sourceTerm 0 0 mn

noncomputable def B : PowerSeries ℤ := ∑' mn, sourceTerm 1 3 mn

noncomputable def C : PowerSeries ℤ := ∑' mn, sourceTerm 2 3 mn

noncomputable def P9 (r : ℕ) : PowerSeries ℤ := (q ^ r; q ^ 9)_∞

noncomputable def K₁ : PowerSeries ℤ := bInv (P9 1 * P9 3 * P9 6 * P9 8)

noncomputable def K₂ : PowerSeries ℤ := bInv (P9 2 * P9 3 * P9 6 * P9 7)

noncomputable def K₃ : PowerSeries ℤ := bInv (P9 3 * P9 4 * P9 5 * P9 6)

noncomputable def E (d : ℕ) : PowerSeries ℤ := (q ^ d; q ^ d)_∞

noncomputable def a : PowerSeries ℤ := ∑' rs : ℤ × ℤ, q ^ (rs.1 ^ 2 + rs.1 * rs.2 + rs.2 ^ 2).toNat

noncomputable def cubicNorm (X Y Z : PowerSeries ℤ) : PowerSeries ℤ :=
  X ^ 3 + q * Y ^ 3 - q ^ 2 * Z ^ 3 + 3 * q * X * Y * Z

end KanadeRussell
