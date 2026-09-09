import KanadeRussell.Source.Reflected
set_option backward.isDefEq.respectTransparency false

/-! The reflected G(q⁻¹x,q³) source, with all exponents proved nonnegative. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell.Source
open Infra

def minusExponent (m n : ℕ) : ℕ :=
  ((m : ℤ) ^ 2 - 3 * m * n + 3 * (n : ℤ) ^ 2 - m + 3 * n).toNat

theorem minus_nonneg (m n : ℕ) :
    0 ≤ (m : ℤ) ^ 2 - 3 * m * n + 3 * (n : ℤ) ^ 2 - m + 3 * n := by
  by_cases hn : n = 0
  · subst n
    have hm : m ≤ m ^ 2 := Nat.le_self_pow (by decide) _
    have hm' : (m : ℤ) ≤ (m : ℤ) ^ 2 := by exact_mod_cast hm
    simpa only [Nat.cast_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero] using sub_nonneg.mpr hm'
  · have hn' : (1 : ℤ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    nlinarith [sq_nonneg ((2 : ℤ) * m - 3 * n - 1), sq_nonneg (n : ℤ)]

theorem minusExponent_cast (m n : ℕ) :
    (minusExponent m n : ℤ) = (m : ℤ) ^ 2 - 3 * m * n + 3 * (n : ℤ) ^ 2 - m + 3 * n :=
  Int.toNat_of_nonneg (minus_nonneg m n)

theorem minusExponent_large (m n k : ℕ) (h : 16 * k + 16 < m ∨ 16 * k + 16 < n) :
    k < minusExponent m n := by
  have he := minusExponent_cast m n
  have hR := reflectedExponent_cast m n
  have hm : (m : ℤ) ^ 2 ≤ 4 * reflectedExponent m n := by
    nlinarith [sq_nonneg ((m : ℤ) - 2 * n)]
  have hn : (n : ℤ) ^ 2 ≤ 4 * reflectedExponent m n := by
    nlinarith [sq_nonneg ((2 : ℤ) * m - 3 * n), sq_nonneg (n : ℤ)]
  have hbound : (reflectedExponent m n : ℤ) ≤ 2 * minusExponent m n + 4 := by
    nlinarith [sq_nonneg ((m : ℤ) - 4)]
  rcases h with h | h
  · have h' : 16 * (k : ℤ) + 16 < m := by exact_mod_cast h
    have : (k : ℤ) < minusExponent m n := by nlinarith [sq_nonneg (k : ℤ)]
    exact_mod_cast this
  · have h' : 16 * (k : ℤ) + 16 < n := by exact_mod_cast h
    have : (k : ℤ) < minusExponent m n := by nlinarith [sq_nonneg (k : ℤ)]
    exact_mod_cast this

noncomputable def minusCoreTerm (m n : ℕ) : QSeries := q ^ minusExponent m n * bInv (q ^ 3; q ^ 3)_n
noncomputable def minusCore (m : ℕ) : QSeries := ∑' n, minusCoreTerm m n
noncomputable def minusTerm (mn : ℕ × ℕ) : QSeries :=
  q ^ minusExponent mn.1 mn.2 * bInv (q; q)_mn.1 * bInv (q ^ 3; q ^ 3)_mn.2
noncomputable def minusSeries : PowerSeries QSeries := weightedSeries Prod.fst minusTerm
noncomputable def Vval : QSeries := ∑' mn, minusTerm mn

theorem summable_minusTerm : Summable minusTerm := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (16 * k + 17) ×ˢ Finset.range (16 * k + 17))).subset
  intro mn hmn
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
  by_contra h
  have he := minusExponent_large mn.1 mn.2 k (by omega)
  apply hmn
  change coeff k (minusTerm mn) = 0
  rw [minusTerm, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]

theorem summable_minusCore (m : ℕ) : Summable (minusCoreTerm m) := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (16 * k + 17))).subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have he := minusExponent_large m n k (Or.inr (by omega))
  apply hn
  change coeff k (minusCoreTerm m n) = 0
  rw [minusCoreTerm, coeff_X_pow_mul', if_neg (by omega)]

theorem coeff_minusSeries (m : ℕ) : coeff m minusSeries = bInv (q; q)_m * minusCore m := by
  have h := hasSum_weightedSeries Prod.fst summable_minusTerm
  have hc := (hasSum_iff_hasSum_coeff _).mp h m
  have hrow := (summable_minusTerm.prod_factor m).hasSum
  have hf : HasSum (fun mn : ℕ × ℕ => if m = mn.1 then minusTerm mn else 0)
      (∑' n, minusTerm (m, n)) := by
    have hi : Function.Injective (fun n : ℕ => (m, n)) := fun n k h => congrArg Prod.snd h
    apply (hi.hasSum_iff ?_).mp
    · simpa only [Function.comp_def, ↓reduceIte] using hrow
    · rintro ⟨r, n⟩ hn
      have hr : m ≠ r := by
        intro he
        apply hn
        exact ⟨n, Prod.ext he rfl⟩
      simp only [if_neg hr]
  have heq : coeff m minusSeries = ∑' n, minusTerm (m, n) :=
    (hc.congr_fun (fun mn => by simp only [coeff_monomial])).unique hf
  rw [heq, minusCore, ← (summable_minusCore m).tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [minusTerm, minusCoreTerm]
  ring

theorem minusSeries_summableCoeff : SummableCoeff minusSeries :=
  weightedSeries_summableCoeff Prod.fst summable_minusTerm

@[simp] theorem sumCoeff_minusSeries : sumCoeff minusSeries = Vval :=
  sumCoeff_weightedSeries Prod.fst summable_minusTerm

private theorem minusCoreTerm_contiguity (m n : ℕ) :
    reflectedCoreTerm (m + 1) (n + 1) - q ^ (2 * m + 1) * reflectedCoreTerm m (n + 1) =
      q * minusCoreTerm m n := by
  have h1 : reflectedExponent (m + 1) (n + 1) = 1 + minusExponent m n := by
    have ha := reflectedExponent_cast (m + 1) (n + 1)
    have hb := minusExponent_cast m n
    push_cast at ha
    nlinarith
  have h2 : 2 * m + 1 + reflectedExponent m (n + 1) =
      reflectedExponent (m + 1) (n + 1) + 3 * (n + 1) := by
    have ha := reflectedExponent_cast m (n + 1)
    have hb := reflectedExponent_cast (m + 1) (n + 1)
    push_cast at ha hb
    nlinarith
  have hu (k : ℕ) : IsUnit (q ^ 3; q ^ 3)_k := by simpa using isUnit_qPochhammer_q 2 k
  have hc := bInv_qFactorial_step (q ^ 3) n (hu n) (hu (n + 1))
  simp only [reflectedCoreTerm, minusCoreTerm]
  rw [← mul_assoc (q ^ (2 * m + 1)), ← pow_add, h2, h1, pow_add, pow_add, pow_one]
  linear_combination q * q ^ minusExponent m n * hc

private theorem minusCore_contiguity (m : ℕ) :
    reflectedCore (m + 1) - q ^ (2 * m + 1) * reflectedCore m = q * minusCore m := by
  have hl := (summable_reflectedCore (m + 1)).hasSum.sub
    ((summable_reflectedCore m).hasSum.mul_left (q ^ (2 * m + 1)))
  have hr := ((summable_minusCore m).hasSum.mul_left q).congr_fun
    (fun n => minusCoreTerm_contiguity m n)
  have hz : reflectedCoreTerm (m + 1) 0 - q ^ (2 * m + 1) * reflectedCoreTerm m 0 = 0 := by
    have he : reflectedExponent (m + 1) 0 = 2 * m + 1 + reflectedExponent m 0 := by
      have h1 := reflectedExponent_cast (m + 1) 0
      have h2 := reflectedExponent_cast m 0
      push_cast at h1 h2
      nlinarith
    simp only [reflectedCoreTerm, qPochhammer_zero, bInv_one, mul_one, he, pow_add, sub_self]
  have hh := (hasSum_nat_add_iff (f := fun n => reflectedCoreTerm (m + 1) n -
    q ^ (2 * m + 1) * reflectedCoreTerm m n) 1).mp hr
  simp only [Finset.sum_range_one, hz, add_zero] at hh
  exact hl.unique hh

/-- The reflected contiguity used to obtain the third addition formula. -/
theorem reflected_minus_contiguity :
    PowerSeries.C q * X * minusSeries = reflectedSeries - rescale q reflectedSeries -
      PowerSeries.C q * X * rescale (q ^ 2) reflectedSeries := by
  apply PowerSeries.ext
  intro m
  rcases m with _ | m
  · simp only [mul_assoc, coeff_C_mul, coeff_zero_X_mul, mul_zero, map_sub,
      coeff_rescale, pow_zero, one_mul, sub_self]
  · simp only [mul_assoc, coeff_C_mul, coeff_succ_X_mul, map_sub, coeff_rescale,
      coeff_reflectedSeries, coeff_minusSeries]
    have hu (k : ℕ) : IsUnit (q; q)_k := by simpa using isUnit_qPochhammer_q 0 k
    have hc := bInv_qFactorial_step q m (hu m) (hu (m + 1))
    have hr := minusCore_contiguity m
    linear_combination -(bInv (q; q)_m * hr + reflectedCore (m + 1) * hc)

end KanadeRussell.Source
