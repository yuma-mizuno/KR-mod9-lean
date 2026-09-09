import Mathlib
import RogersRamanujan
set_option backward.isDefEq.respectTransparency false

/-! Finite inverse factorial cancellation, shared by source contiguities. -/

open scoped QTheory

namespace KanadeRussell.Infra

variable {R : Type*} [CommRing R]

/-- The denominator-cleared index shift; only finite factorial units are needed. -/
theorem bInv_qFactorial_step (q : R) (n : ℕ)
    (hu : IsUnit (q; q)_n) (hv : IsUnit (q; q)_(n + 1)) :
    (1 - q ^ (n + 1)) * bInv (q; q)_(n + 1) = bInv (q; q)_n := by
  have hp : (q; q)_n * ((1 - q ^ (n + 1)) * bInv (q; q)_(n + 1)) = 1 := by
    simpa only [qPochhammer_succ', pow_succ', mul_assoc] using hv.mul_bInv_cancel
  have hc := congrArg (fun z : R => bInv (q; q)_n * z) hp
  simpa only [← mul_assoc, hu.bInv_mul_cancel, one_mul, mul_one] using hc

end KanadeRussell.Infra
