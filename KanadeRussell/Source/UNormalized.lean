import KanadeRussell.Source.UAiry
import KanadeRussell.Source.Addition
set_option backward.isDefEq.respectTransparency false

/-! The normalized Casoratian for the two concrete t-variable solutions. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Source
open Infra

private theorem rescale_constant_aux (r c : QSeries) :
    rescale r (PowerSeries.C c) = PowerSeries.C c := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_rescale, coeff_C]
  split_ifs with h
  · subst n; simp
  · simp

/-- The shifted p recurrence is exactly the exterior equation. -/
theorem exteriorEquation_rescale_p : exteriorEquation q (rescale q p) = 0 := by
  have h := congrArg (rescale q) p_recurrence
  simp only [map_add, map_sub, map_mul, map_pow, map_one, rescale_X,
    rescale_constant_aux, rescale_rescale] at h
  simp only [exteriorEquation, rescale_rescale, map_add, map_pow, map_one]
  simp only [← pow_succ, ← pow_succ', ← pow_two] at h ⊢
  linear_combination h

noncomputable def uCasoratian : PowerSeries QSeries := casoratian (q ^ 4) uTwisted uSeries
noncomputable def uCasoratianTail : PowerSeries QSeries := mk fun n => coeff (n + 1) uCasoratian

theorem uCasoratian_eq_X_mul : uCasoratian = X * uCasoratianTail := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp only [coeff_zero_X_mul, coeff_zero_eq_constantCoeff, uCasoratian,
      casoratian, map_sub, map_mul, constantCoeff_rescale]
    ring
  | succ n => simp only [coeff_succ_X_mul, uCasoratianTail, coeff_mk]

theorem exteriorEquation_uCasoratianTail : exteriorEquation (q ^ 4) uCasoratianTail = 0 :=
  casoratian_exterior (q ^ 4) (pow_ne_zero _ X_ne_zero) uTwisted uSeries uCasoratianTail
    scalarEquation_uTwisted scalarEquation_uSeries uCasoratian_eq_X_mul

private theorem exteriorEquation_mapped_p :
    exteriorEquation (q ^ 4) (rescale (q ^ 4) (PowerSeries.map baseChange p)) = 0 := by
  have h := congrArg (PowerSeries.map baseChange) exteriorEquation_rescale_p
  simpa only [map_exteriorEquation, ← rescale_map, q, baseChange_X, map_zero] using h

private theorem exteriorEquation_candidate :
    exteriorEquation (q ^ 4) (PowerSeries.C (2 * q) *
      rescale (q ^ 4) (PowerSeries.map baseChange p)) = 0 := by
  have h := exteriorEquation_mapped_p
  simp only [exteriorEquation, map_mul, rescale_constant_aux] at *
  linear_combination (PowerSeries.C 2 * PowerSeries.C q) * h

/-- Plan E.3: W(t;x) = 2t x p(t^4;t^4 x), with the coefficient substitution explicit. -/
theorem uCasoratian_normalized : uCasoratian = PowerSeries.C (2 * q) * X *
    rescale (q ^ 4) (PowerSeries.map baseChange p) := by
  let candidate := PowerSeries.C (2 * q) * rescale (q ^ 4) (PowerSeries.map baseChange p)
  have hc : exteriorEquation (q ^ 4) (uCasoratianTail - candidate) = 0 := by
    have h1 := exteriorEquation_uCasoratianTail
    have h2 := exteriorEquation_candidate
    dsimp [candidate]
    simp only [exteriorEquation, map_sub] at *
    linear_combination h1 - h2
  have h0 : coeff 0 (uCasoratianTail - candidate) = 0 := by
    simp only [map_sub, uCasoratianTail, coeff_mk, Nat.zero_add, uCasoratian,
      uCasoratian_coeff_one, candidate, coeff_C_mul, coeff_rescale, pow_zero, one_mul,
      coeff_map]
    rw [coeff_zero_eq_constantCoeff]
    simp [p]
  have hp : ∀ n : ℕ, 0 < n → (q ^ 4) ^ n ≠ 1 := by
    intro n hn h
    have hcc := congrArg (constantCoeff (R := ℤ)) h
    simp [q, hn.ne'] at hcc
  have he := exteriorEquation_eq_zero_of_initial (q ^ 4) hp
    (uCasoratianTail - candidate) hc h0
  rw [uCasoratian_eq_X_mul, sub_eq_zero.mp he]
  dsimp [candidate]
  ring

/-- The specialization of the normalized Casoratian at x = 1. -/
theorem uCasoratian_specialized :
    twist uOne * uFive - uOne * twist uFive = 2 * q * baseChange C := by
  have h := congrArg sumCoeff uCasoratian_normalized
  have hu := uSeries_summableCoeff
  have ht := uTwisted_summableCoeff
  have hp : SummableCoeff (rescale (q ^ 4) (PowerSeries.map baseChange p)) :=
    ((diagonalSeries_summableCoeff 1 0).map baseChange baseChange_continuous).rescale (q ^ 4)
  rw [uCasoratian, casoratian,
    sumCoeff_sub (ht.mul (hu.rescale _)) (hu.mul (ht.rescale _)),
    sumCoeff_mul ht (hu.rescale _), sumCoeff_mul hu (ht.rescale _),
    sumCoeff_uTwisted, sumCoeff_rescale_uSeries, sumCoeff_uSeries, sumCoeff_rescale_uTwisted,
    sumCoeff_mul ((SummableCoeff.C (2 * q)).mul SummableCoeff.X) hp,
    sumCoeff_mul (SummableCoeff.C (2 * q)) SummableCoeff.X, sumCoeff_C, sumCoeff_X, mul_one] at h
  have hsp : sumCoeff (rescale (q ^ 4) (PowerSeries.map baseChange p)) = baseChange C := by
    rw [← baseChange_X, rescale_map, sumCoeff_map
      (show SummableCoeff (rescale q p) from (diagonalSeries_summableCoeff 1 0).rescale q)
      baseChange baseChange_continuous,
      sumCoeff_rescale_p]
  rw [hsp] at h
  exact h

end KanadeRussell.Source
