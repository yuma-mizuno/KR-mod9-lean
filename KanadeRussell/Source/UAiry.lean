import KanadeRussell.Source.U
import KanadeRussell.Source.Airy
import KanadeRussell.Source.Casoratian
set_option backward.isDefEq.respectTransparency false

/-! Airy evaluation of the concrete initial data and its determinant. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Source
open Infra

private theorem eval_rescale (f : PowerSeries QSeries) (r s : QSeries)
    (hs : IsTopologicallyNilpotent s) (hrs : IsTopologicallyNilpotent (r * s)) :
    sEval (RingHom.id _) s (rescale r f) = sEval (RingHom.id _) (r * s) f := by
  have hb : (⇑(RingHom.id QSeries)).BoundedRange := PowerSeries.bounded _
  have hl := hasSum_sEval_of_commute (RingHom.id _) hb hs (rescale r f)
  have hr := hasSum_sEval_of_commute (RingHom.id _) hb hrs f
  apply hl.unique
  apply hr.congr_fun
  intro n
  simp only [RingHom.id_apply, coeff_rescale, mul_pow]
  ring

private theorem twist_eval (f : PowerSeries QSeries) (s : QSeries)
    (hs : IsTopologicallyNilpotent s) :
    twist (sEval (RingHom.id _) s f) =
      sEval (RingHom.id _) (twist s) (PowerSeries.map twist f) := by
  have hb : (⇑(RingHom.id QSeries)).BoundedRange := PowerSeries.bounded _
  have ht : IsTopologicallyNilpotent (twist s) := hs.map twist_continuous
  have hl := (hasSum_sEval_of_commute (RingHom.id _) hb hs f).map twist twist_continuous
  have hr := hasSum_sEval_of_commute (RingHom.id _) hb ht (PowerSeries.map twist f)
  apply hl.unique
  apply hr.congr_fun
  intro n
  simp only [Function.comp_def, RingHom.id_apply, coeff_map, map_mul, map_pow]

private theorem airy_t_units (n : ℕ) : IsUnit ((q ^ 6) ^ 2; (q ^ 6) ^ 2)_n := by
  simpa only [← pow_mul, Nat.reduceMul] using isUnit_qPochhammer_q 11 n

private theorem twist_airy_t : PowerSeries.map twist (airy (q ^ 6)) = airy (q ^ 6) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_map, airy, coeff_mk, map_mul, map_pow]
  rw [(airy_t_units n).map_bInv, map_qPochhammer]
  have ht : twist q ^ 6 = q ^ 6 := by
    rw [show twist q = -q by simp [twist, q]]
    ring
  simp only [map_pow, show twist (q ^ 6) = q ^ 6 from twist_even_q_pow 3, ht]

theorem uCore_eq_airy (m : ℕ) :
    uCore m = sEval (RingHom.id _) (q ^ (6 * m + 9)) (airy (q ^ 6)) := by
  have hb : (⇑(RingHom.id QSeries)).BoundedRange := PowerSeries.bounded _
  have hn : IsTopologicallyNilpotent (q ^ (6 * m + 9)) := by simp [q]
  have he (n : ℕ) : 6 * n.choose 2 + (6 * m + 9) * n =
      3 * n ^ 2 + 6 * n + 6 * m * n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith
  apply (summable_uCore m).hasSum.unique
  apply (hasSum_sEval_of_commute (RingHom.id _) hb hn (airy (q ^ 6))).congr_fun
  intro n
  simp only [RingHom.id_apply, airy, coeff_mk, uCoreTerm, ← pow_mul, Nat.reduceMul]
  rw [mul_right_comm (q ^ (6 * n.choose 2)), ← pow_add, he]

theorem twist_uCore_eq_airy (m : ℕ) :
    twist (uCore m) = sEval (RingHom.id _) (-q ^ (6 * m + 9)) (airy (q ^ 6)) := by
  rw [uCore_eq_airy, twist_eval _ _ (by simp [q]), twist_airy_t]
  have he : 6 * m + 9 = 2 * (3 * m + 4) + 1 := by omega
  have ht : twist (q ^ (6 * m + 9)) = -q ^ (6 * m + 9) := by
    rw [he, pow_succ, map_mul, twist_even_q_pow]
    simp [twist, q]
  rw [ht]

/-- The Airy Wronskian evaluated at the actual source arguments t^9 and t^15. -/
theorem uCore_wronskian :
    uCore 0 * twist (uCore 1) + twist (uCore 0) * uCore 1 = 2 := by
  have hp : ∀ n : ℕ, 0 < n → (q ^ 6) ^ n ≠ 1 := by
    intro n hn h
    have hc := congrArg (constantCoeff (R := ℤ)) h
    simp [q, hn.ne'] at hc
  have hw := congrArg (sEval (RingHom.id QSeries) (q ^ 9))
    (airy_wronskian (q ^ 6) airy_t_units hp)
  simp only [map_add, map_mul, map_ofNat] at hw
  rw [eval_rescale _ _ _ (by simp [q]) (by simp [q]),
    eval_rescale _ _ _ (by simp [q]) (by simp [q]),
    eval_rescale _ _ _ (by simp [q]) (by simp [q])] at hw
  norm_num only [neg_mul, neg_one_mul, one_mul, ← pow_add] at hw
  have h0 := uCore_eq_airy 0
  have h1 := uCore_eq_airy 1
  have h0t := twist_uCore_eq_airy 0
  have h1t := twist_uCore_eq_airy 1
  norm_num only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.reduceAdd] at h0 h1 h0t h1t
  rw [← h0, ← h1t, ← h0t, ← h1] at hw
  exact hw

@[simp] theorem uSeries_coeff_zero : coeff 0 uSeries = uCore 0 := by simp [coeff_uSeries]
@[simp] theorem uSeries_coeff_one : coeff 1 uSeries = -q * bInv (q ^ 4; q ^ 4)_1 * uCore 1 := by
  simp [coeff_uSeries]

@[simp] theorem twist_inverse_four : twist (bInv (q ^ 4; q ^ 4)_1) = bInv (q ^ 4; q ^ 4)_1 := by
  have hu : IsUnit (q ^ 4; q ^ 4)_1 := by simpa using isUnit_qPochhammer_q 3 1
  rw [hu.map_bInv, map_qPochhammer, twist_q_four]

/-- Initial coefficient of the concrete Casoratian; no formal division by t is used. -/
theorem uCasoratian_coeff_one : coeff 1 (casoratian (q ^ 4) uTwisted uSeries) = 2 * q := by
  have hcc (f : PowerSeries QSeries) : constantCoeff f = coeff 0 f :=
    by rw [coeff_zero_eq_constantCoeff]
  have hq : twist q = -q := by simp [twist, q]
  have hW := uCore_wronskian
  have hu : IsUnit (q ^ 4; q ^ 4)_1 := by simpa using isUnit_qPochhammer_q 3 1
  have hi : (1 - q ^ 4) * bInv (q ^ 4; q ^ 4)_1 = 1 := by
    simpa only [qPochhammer_one] using hu.mul_bInv_cancel
  simp only [casoratian, map_sub, coeff_one_mul, hcc, coeff_rescale,
    pow_one, pow_zero, one_mul, uTwisted, coeff_map, uSeries_coeff_zero, uSeries_coeff_one,
    map_mul, map_neg, hq, neg_neg, twist_inverse_four]
  linear_combination q * hW + q * (uCore 0 * twist (uCore 1) + twist (uCore 0) * uCore 1) * hi

end KanadeRussell.Source
