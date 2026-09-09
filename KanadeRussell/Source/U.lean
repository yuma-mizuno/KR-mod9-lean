import KanadeRussell.Source.Anchors
import KanadeRussell.Infra.Nonarch
import KanadeRussell.Infra.Weighted
import KanadeRussell.Infra.ScalarCoefficients
import KanadeRussell.Infra.Theta
import KanadeRussell.Infra.MapSeries
set_option backward.isDefEq.respectTransparency false

/-! The concrete t-variable source, with q = t^4, from plan §2.3. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell.Source
open Infra

noncomputable def uCoreTerm (m n : ℕ) : QSeries :=
  q ^ (3 * n ^ 2 + 6 * n + 6 * m * n) * bInv (q ^ 12; q ^ 12)_n

noncomputable def uCore (m : ℕ) : QSeries := ∑' n, uCoreTerm m n

noncomputable def uTerm (mn : ℕ × ℕ) : QSeries :=
  q ^ (mn.1 ^ 2 + 3 * mn.2 ^ 2 + 6 * mn.2 + 6 * mn.1 * mn.2) *
    ((-1) ^ mn.1 * bInv (q ^ 4; q ^ 4)_mn.1 * bInv (q ^ 12; q ^ 12)_mn.2)

noncomputable def uSeries : PowerSeries QSeries := weightedSeries Prod.fst uTerm
noncomputable def uTwisted : PowerSeries QSeries := PowerSeries.map twist uSeries
noncomputable def uOne : QSeries := ∑' mn, uTerm mn
noncomputable def uFive : QSeries := ∑' mn, (q ^ 4) ^ mn.1 * uTerm mn

theorem summable_uTerm : Summable uTerm := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (k + 1) ×ˢ Finset.range (k + 1))).subset
  intro mn hmn
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
  by_contra h
  have he : k < mn.1 ^ 2 + 3 * mn.2 ^ 2 + 6 * mn.2 + 6 * mn.1 * mn.2 := by
    have hm := Nat.le_self_pow (by decide : 2 ≠ 0) mn.1
    have hn := Nat.le_self_pow (by decide : 2 ≠ 0) mn.2
    omega
  apply hmn
  change coeff k (uTerm mn) = 0
  rw [uTerm, coeff_X_pow_mul', if_neg (by omega)]

theorem summable_uCore (m : ℕ) : Summable (uCoreTerm m) := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (k + 1))).subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have he : k < 3 * n ^ 2 + 6 * n + 6 * m * n := by omega
  apply hn
  change coeff k (uCoreTerm m n) = 0
  rw [uCoreTerm, coeff_X_pow_mul', if_neg (by omega)]

theorem coeff_uSeries (m : ℕ) :
    coeff m uSeries = (-1) ^ m * q ^ (m ^ 2) * bInv (q ^ 4; q ^ 4)_m * uCore m := by
  have h := hasSum_weightedSeries Prod.fst summable_uTerm
  have hc := (hasSum_iff_hasSum_coeff _).mp h m
  have hrow := (summable_uTerm.prod_factor m).hasSum
  have hf : HasSum (fun mn : ℕ × ℕ => if m = mn.1 then uTerm mn else 0)
      (∑' n, uTerm (m, n)) := by
    have hi : Function.Injective (fun n : ℕ => (m, n)) := fun n k h => congrArg Prod.snd h
    apply (hi.hasSum_iff ?_).mp
    · simpa only [Function.comp_def, ↓reduceIte] using hrow
    · rintro ⟨r, n⟩ hn
      have hr : m ≠ r := by
        intro he
        apply hn
        exact ⟨n, Prod.ext he rfl⟩
      simp only [if_neg hr]
  have heq : coeff m uSeries = ∑' n, uTerm (m, n) :=
    (hc.congr_fun (fun mn => by simp only [coeff_monomial])).unique hf
  rw [heq, uCore, ← (summable_uCore m).tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [uTerm, uCoreTerm, pow_add]
  ring

theorem uSeries_summableCoeff : SummableCoeff uSeries :=
  weightedSeries_summableCoeff Prod.fst summable_uTerm

@[simp] theorem sumCoeff_uSeries : sumCoeff uSeries = uOne :=
  sumCoeff_weightedSeries Prod.fst summable_uTerm

@[simp] theorem sumCoeff_rescale_uSeries : sumCoeff (rescale (q ^ 4) uSeries) = uFive := by
  rw [uSeries, weightedSeries_rescale _ _ summable_uTerm]
  exact sumCoeff_weightedSeries Prod.fst
    (summable_series_mul summable_uTerm (fun mn => (q ^ 4) ^ mn.1))

theorem uCoreTerm_contiguity (m n : ℕ) :
    uCoreTerm m (n + 1) - uCoreTerm (m + 2) (n + 1) =
      q ^ (6 * m + 9) * uCoreTerm (m + 1) n := by
  have hu (k : ℕ) : IsUnit (q ^ 12; q ^ 12)_k := by
    simpa using isUnit_qPochhammer_q 11 k
  have hc := bInv_qFactorial_step (q ^ 12) n (hu n) (hu (n + 1))
  have he : 3 * (n + 1) ^ 2 + 6 * (n + 1) + 6 * m * (n + 1) =
      6 * m + 9 + (3 * n ^ 2 + 6 * n + 6 * (m + 1) * n) := by ring
  have he' : 3 * (n + 1) ^ 2 + 6 * (n + 1) + 6 * (m + 2) * (n + 1) =
      (6 * m + 9 + (3 * n ^ 2 + 6 * n + 6 * (m + 1) * n)) + 12 * (n + 1) := by ring
  simp only [uCoreTerm, he, he', pow_add]
  rw [← pow_mul] at hc
  linear_combination q ^ (6 * m + 9) * q ^ (3 * n ^ 2 + 6 * n + 6 * (m + 1) * n) * hc

theorem uCore_contiguity (m : ℕ) :
    uCore m - uCore (m + 2) = q ^ (6 * m + 9) * uCore (m + 1) := by
  have hl := (summable_uCore m).hasSum.sub (summable_uCore (m + 2)).hasSum
  have hr := ((summable_uCore (m + 1)).hasSum.mul_left (q ^ (6 * m + 9))).congr_fun
    (fun n => uCoreTerm_contiguity m n)
  have hh := (hasSum_nat_add_iff (f := fun n => uCoreTerm m n - uCoreTerm (m + 2) n) 1).mp hr
  have hz : uCoreTerm m 0 - uCoreTerm (m + 2) 0 = 0 := by simp [uCoreTerm]
  simp only [Finset.sum_range_one, hz, add_zero] at hh
  exact hl.unique hh

private theorem uNumerator_recurrence (m : ℕ) :
    (-1 : QSeries) ^ (m + 2) * q ^ ((m + 2) ^ 2) * uCore (m + 2) =
      (q ^ 4) ^ (2 * m + 3) * ((-1) ^ (m + 1) * q ^ ((m + 1) ^ 2) * uCore (m + 1)) +
      (q ^ 4) ^ (m + 1) * ((-1) ^ m * q ^ (m ^ 2) * uCore m) := by
  have hR := uCore_contiguity m
  rw [show (m + 2) ^ 2 = m ^ 2 + 4 * m + 4 by ring,
    show (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 by ring]
  simp only [pow_add, pow_mul] at hR ⊢
  linear_combination -(-1 : QSeries) ^ m * q ^ (m ^ 2) * (q ^ m) ^ 4 * q ^ 4 * hR

theorem scalarEquation_uSeries : scalarEquation (q ^ 4) uSeries = 0 := by
  apply scalarEquation_of_recurrence
  intro m
  rw [coeff_uSeries, coeff_uSeries, coeff_uSeries]
  have hu (k : ℕ) : IsUnit (q ^ 4; q ^ 4)_k := by
    simpa using isUnit_qPochhammer_q 3 k
  have h1 := bInv_qFactorial_step (q ^ 4) m (hu m) (hu (m + 1))
  have h2 := bInv_qFactorial_step (q ^ 4) (m + 1) (hu (m + 1)) (hu (m + 2))
  have hR := uNumerator_recurrence m
  simp only [Nat.add_assoc, Nat.reduceAdd] at h2
  linear_combination bInv (q ^ 4; q ^ 4)_m * hR +
    (1 - (q ^ 4) ^ (m + 1)) * ((-1) ^ (m + 2) * q ^ ((m + 2) ^ 2) * uCore (m + 2)) * h2 +
    (((-1) ^ (m + 2) * q ^ ((m + 2) ^ 2) * uCore (m + 2)) -
      (q ^ 4) ^ (2 * m + 3) * ((-1) ^ (m + 1) * q ^ ((m + 1) ^ 2) * uCore (m + 1))) * h1

@[simp] theorem twist_even_q_pow (k : ℕ) : twist (q ^ (2 * k)) = q ^ (2 * k) := by
  simp only [twist, map_pow, q, rescale_neg_one_X, pow_mul, neg_sq]

@[simp] theorem twist_q_four : twist (q ^ 4) = q ^ 4 := twist_even_q_pow 2

theorem scalarEquation_uTwisted : scalarEquation (q ^ 4) uTwisted = 0 := by
  have h := congrArg (PowerSeries.map twist) scalarEquation_uSeries
  simpa only [map_scalarEquation, twist_q_four, map_zero, uTwisted] using h

theorem uTwisted_summableCoeff : SummableCoeff uTwisted :=
  uSeries_summableCoeff.map twist twist_continuous

@[simp] theorem sumCoeff_uTwisted : sumCoeff uTwisted = twist uOne := by
  rw [uTwisted, sumCoeff_map uSeries_summableCoeff twist twist_continuous, sumCoeff_uSeries]

@[simp] theorem sumCoeff_rescale_uTwisted :
    sumCoeff (rescale (q ^ 4) uTwisted) = twist uFive := by
  rw [uTwisted, ← twist_q_four, rescale_map,
    sumCoeff_map (uSeries_summableCoeff.rescale _) twist twist_continuous,
    sumCoeff_rescale_uSeries]

end KanadeRussell.Source
