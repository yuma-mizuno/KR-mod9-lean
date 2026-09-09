import KanadeRussell.Tsuchioka.EulerPolynomial

/-! Cancellation of the three creation contributions to the central Euler residue. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem sum_creationLog :
    ∑ j : Fin 3, creationLog (K := K) j = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [map_sum, creationLog, PowerSeries.coeff_mk, map_zero]
  by_cases hn : IsMode n
  · simp only [dif_pos hn]
    rw [Finset.sum_comm]
    have hs (i : Fin 3) : ∑ j : Fin 3, -4 * tensorExponent (K := K) i j / (n : K) = 0 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum, sum_tensorExponent,
        mul_zero, zero_mul]
    simp only [← Finset.sum_mul, ← map_sum, hs, map_zero, zero_mul, Finset.sum_const_zero]
  · simp [hn]

theorem laurentEuler_creation (j : Fin 3) :
    laurentEuler (creation (K := K) j : LaurentSeries (Space K)) =
      (creation (K := K) j : LaurentSeries (Space K)) *
        laurentEuler (creationLog (K := K) j : LaurentSeries (Space K)) := by
  rw [laurentEuler_powerSeries, laurentEuler_powerSeries]
  change ((PowerSeries.X * PowerSeries.derivative (Space K)
      (exponential (creationLog (K := K) j)) : PowerSeries (Space K)) : LaurentSeries (Space K)) = _
  rw [derivative_exponential (constantCoeff_creationLog (K := K) j)]
  rw [← PowerSeries.coe_mul]
  congr 1
  change PowerSeries.X * (exponential (creationLog (K := K) j) *
      PowerSeries.derivative (Space K) (creationLog (K := K) j)) =
    exponential (creationLog (K := K) j) * (PowerSeries.X * PowerSeries.derivative (Space K) (creationLog (K := K) j))
  ring

theorem creation_central_fusion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (j : Fin 3) :
    laurentRescale (phaseUnit w hw 6) (creation (K := K) j : LaurentSeries (Space K)) *
      (creation (K := K) j : LaurentSeries (Space K)) = 1 := by
  have h := poleNormalProduct_six w hw (simpleRoot 0) j (1 : Space K)
  simpa only [poleNormalProduct, rootCreation_first, map_one, mul_one] using h

theorem creation_central_euler (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (j : Fin 3) :
    laurentRescale (phaseUnit w hw 6)
        (laurentEuler (creation (K := K) j : LaurentSeries (Space K))) *
      (creation (K := K) j : LaurentSeries (Space K)) =
      laurentRescale (phaseUnit w hw 6)
        (laurentEuler (creationLog (K := K) j : LaurentSeries (Space K))) := by
  rw [laurentEuler_creation, map_mul]
  calc
    _ = laurentRescale (phaseUnit w hw 6)
        (laurentEuler (creationLog (K := K) j : LaurentSeries (Space K))) *
        (laurentRescale (phaseUnit w hw 6) (creation (K := K) j : LaurentSeries (Space K)) * creation (K := K) j) := by
      ring
    _ = _ := by rw [creation_central_fusion w hw, mul_one]

/-- Each creation derivative can be nonzero; their tensor sum vanishes. -/
theorem sum_creation_central_euler (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    ∑ j : Fin 3, laurentRescale (phaseUnit w hw 6)
        (laurentEuler (creation (K := K) j : LaurentSeries (Space K))) *
      (creation (K := K) j : LaurentSeries (Space K)) = 0 := by
  simp_rw [creation_central_euler w hw]
  have hs : ∑ j : Fin 3, (creationLog (K := K) j : LaurentSeries (Space K)) = 0 := by
    rw [← map_sum, sum_creationLog, map_zero]
  rw [← map_sum, ← map_sum, hs, map_zero, map_zero]

end KanadeRussell.Tsuchioka.Fock
