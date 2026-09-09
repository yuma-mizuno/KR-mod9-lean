import KanadeRussell.Source.Diagonal
import KanadeRussell.Infra.QDifference
import KanadeRussell.Infra.ScalarCoefficients
set_option backward.isDefEq.respectTransparency false

/-! The reflected source G(x,1), with nonnegative integral exponents. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell.Source
open Infra

/-- The positive definite quadratic form in the reflected source. -/
def reflectedExponent (m n : ℕ) : ℕ :=
  ((m : ℤ) ^ 2 - 3 * m * n + 3 * (n : ℤ) ^ 2).toNat

theorem reflected_nonneg (m n : ℕ) :
    0 ≤ (m : ℤ) ^ 2 - 3 * m * n + 3 * (n : ℤ) ^ 2 := by
  nlinarith [sq_nonneg ((2 : ℤ) * m - 3 * n), sq_nonneg (n : ℤ)]

theorem reflectedExponent_cast (m n : ℕ) :
    (reflectedExponent m n : ℤ) = (m : ℤ) ^ 2 - 3 * m * n + 3 * (n : ℤ) ^ 2 :=
  Int.toNat_of_nonneg (reflected_nonneg m n)

theorem reflectedExponent_large (m n k : ℕ) (h : 4 * k + 4 < m ∨ 4 * k + 4 < n) :
    k < reflectedExponent m n := by
  have he := reflectedExponent_cast m n
  have hm : (m : ℤ) ^ 2 ≤ 4 * reflectedExponent m n := by
    nlinarith [sq_nonneg ((m : ℤ) - 2 * n)]
  have hn : (n : ℤ) ^ 2 ≤ 4 * reflectedExponent m n := by
    nlinarith [sq_nonneg ((2 : ℤ) * m - 3 * n), sq_nonneg (n : ℤ)]
  rcases h with h | h
  · have h' : 4 * (k : ℤ) + 4 < m := by exact_mod_cast h
    have : (k : ℤ) < reflectedExponent m n := by nlinarith [sq_nonneg (k : ℤ)]
    exact_mod_cast this
  · have h' : 4 * (k : ℤ) + 4 < n := by exact_mod_cast h
    have : (k : ℤ) < reflectedExponent m n := by nlinarith [sq_nonneg (k : ℤ)]
    exact_mod_cast this

noncomputable def reflectedCoreTerm (m n : ℕ) : QSeries :=
  q ^ reflectedExponent m n * bInv (q ^ 3; q ^ 3)_n

noncomputable def reflectedTerm (mn : ℕ × ℕ) : QSeries :=
  q ^ reflectedExponent mn.1 mn.2 * bInv (q; q)_mn.1 * bInv (q ^ 3; q ^ 3)_mn.2

noncomputable def reflectedCore (m : ℕ) : QSeries := ∑' n, reflectedCoreTerm m n

noncomputable def reflectedSeries : PowerSeries QSeries :=
  weightedSeries Prod.fst reflectedTerm

noncomputable def Uval : QSeries := ∑' mn, reflectedTerm mn
noncomputable def Wval : QSeries := ∑' mn, q ^ mn.1 * reflectedTerm mn

theorem summable_reflectedTerm : Summable reflectedTerm := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (4 * k + 5) ×ˢ Finset.range (4 * k + 5))).subset
  intro mn hmn
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
  by_contra h
  have he := reflectedExponent_large mn.1 mn.2 k (by omega)
  apply hmn
  change coeff k (reflectedTerm mn) = 0
  rw [reflectedTerm, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]

theorem summable_reflectedCore (m : ℕ) : Summable (reflectedCoreTerm m) := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (4 * k + 5))).subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have he := reflectedExponent_large m n k (Or.inr (by omega))
  apply hn
  change coeff k (reflectedCoreTerm m n) = 0
  rw [reflectedCoreTerm, coeff_X_pow_mul', if_neg (by omega)]

theorem coeff_reflectedSeries (m : ℕ) :
    coeff m reflectedSeries = bInv (q; q)_m * reflectedCore m := by
  have h := (hasSum_weightedSeries Prod.fst summable_reflectedTerm)
  have hc := (hasSum_iff_hasSum_coeff _).mp h m
  have hrow := (summable_reflectedTerm.prod_factor m).hasSum
  have hf : HasSum (fun mn : ℕ × ℕ => if m = mn.1 then reflectedTerm mn else 0)
      (∑' n, reflectedTerm (m, n)) := by
    have hi : Function.Injective (fun n : ℕ => (m, n)) := fun n k h => congrArg Prod.snd h
    apply (hi.hasSum_iff ?_).mp
    · simpa only [Function.comp_def, ↓reduceIte] using hrow
    · rintro ⟨r, n⟩ hn
      have hr : m ≠ r := by
        intro he
        apply hn
        exact ⟨n, Prod.ext he rfl⟩
      simp only [if_neg hr]
  have heq : coeff m reflectedSeries = ∑' n, reflectedTerm (m, n) :=
    (hc.congr_fun (fun mn => by simp only [coeff_monomial])).unique hf
  rw [heq, reflectedCore, ← (summable_reflectedCore m).tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [reflectedTerm, reflectedCoreTerm]
  ring

theorem reflectedSeries_summableCoeff : SummableCoeff reflectedSeries :=
  weightedSeries_summableCoeff Prod.fst summable_reflectedTerm

@[simp] theorem sumCoeff_reflectedSeries : sumCoeff reflectedSeries = Uval :=
  sumCoeff_weightedSeries Prod.fst summable_reflectedTerm

private theorem reflectedExponent_shift (m n : ℕ) :
    reflectedExponent (m + 2) (n + 1) = m + 1 + reflectedExponent m n := by
  have h1 := reflectedExponent_cast (m + 2) (n + 1)
  have h2 := reflectedExponent_cast m n
  push_cast at h1
  nlinarith

private theorem reflectedExponent_step (m n : ℕ) :
    2 * m + 3 + reflectedExponent (m + 1) (n + 1) =
      reflectedExponent (m + 2) (n + 1) + 3 * (n + 1) := by
  have h1 := reflectedExponent_cast (m + 1) (n + 1)
  have h2 := reflectedExponent_cast (m + 2) (n + 1)
  push_cast at h1 h2
  nlinarith

/-- R-contiguity in a cleared form that never requires a negative q-power. -/
theorem reflectedCoreTerm_contiguity (m n : ℕ) :
    reflectedCoreTerm (m + 2) (n + 1) - q ^ (2 * m + 3) * reflectedCoreTerm (m + 1) (n + 1) =
      q ^ (m + 1) * reflectedCoreTerm m n := by
  have hu (k : ℕ) : IsUnit (q ^ 3; q ^ 3)_k := by simpa using isUnit_qPochhammer_q 2 k
  have hc := bInv_qFactorial_step (q ^ 3) n (hu n) (hu (n + 1))
  simp only [reflectedCoreTerm]
  rw [← mul_assoc (q ^ (2 * m + 3)), ← pow_add, reflectedExponent_step,
    reflectedExponent_shift, pow_add, pow_add]
  linear_combination q ^ (m + 1) * q ^ reflectedExponent m n * hc

theorem reflectedCore_contiguity (m : ℕ) :
    reflectedCore (m + 2) - q ^ (2 * m + 3) * reflectedCore (m + 1) =
      q ^ (m + 1) * reflectedCore m := by
  have hl := (summable_reflectedCore (m + 2)).hasSum.sub
    ((summable_reflectedCore (m + 1)).hasSum.mul_left (q ^ (2 * m + 3)))
  have hr := ((summable_reflectedCore m).hasSum.mul_left (q ^ (m + 1))).congr_fun
    (fun n => reflectedCoreTerm_contiguity m n)
  have hz : reflectedCoreTerm (m + 2) 0 - q ^ (2 * m + 3) * reflectedCoreTerm (m + 1) 0 = 0 := by
    have he : reflectedExponent (m + 2) 0 = 2 * m + 3 + reflectedExponent (m + 1) 0 := by
      have h1 := reflectedExponent_cast (m + 2) 0
      have h2 := reflectedExponent_cast (m + 1) 0
      push_cast at h1 h2
      nlinarith
    simp only [reflectedCoreTerm, qPochhammer_zero, bInv_one, mul_one, he, pow_add, sub_self]
  have hh := (hasSum_nat_add_iff (f := fun n => reflectedCoreTerm (m + 2) n -
    q ^ (2 * m + 3) * reflectedCoreTerm (m + 1) n) 1).mp hr
  simp only [Finset.sum_range_one, hz, add_zero] at hh
  exact hl.unique hh

/-- The reflected source satisfies the scalar equation used in the addition theorem. -/
theorem scalarEquation_reflected : scalarEquation q reflectedSeries = 0 := by
  apply scalarEquation_of_recurrence
  intro m
  rw [coeff_reflectedSeries, coeff_reflectedSeries, coeff_reflectedSeries]
  have hu (k : ℕ) : IsUnit (q; q)_k := by simpa using isUnit_qPochhammer_q 0 k
  have h1 := bInv_qFactorial_step q m (hu m) (hu (m + 1))
  have h2 := bInv_qFactorial_step q (m + 1) (hu (m + 1)) (hu (m + 2))
  have hR := reflectedCore_contiguity m
  simp only [Nat.add_assoc, Nat.reduceAdd] at h2
  linear_combination bInv (q; q)_m * hR +
    (1 - q ^ (m + 1)) * reflectedCore (m + 2) * h2 +
    (reflectedCore (m + 2) - q ^ (2 * m + 3) * reflectedCore (m + 1)) * h1

/-- The constant x-coefficient is shared with the positive source. -/
theorem reflected_coeff_zero : coeff 0 reflectedSeries = coeff 0 (sourceSeries 0 0) := by
  rw [coeff_reflectedSeries]
  simp only [qPochhammer_zero, bInv_one, one_mul, reflectedCore, sourceSeries, coeff_mk, sourceRow]
  apply tsum_congr
  intro n
  have he : reflectedExponent 0 n = 3 * n ^ 2 := by
    have h := reflectedExponent_cast 0 n
    simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, sub_zero, zero_add] at h
    exact_mod_cast h
  simp [reflectedCoreTerm, sourceTerm, he]

private theorem reflectedCore_initial_term (n : ℕ) :
    reflectedCoreTerm 1 (n + 1) - q * reflectedCoreTerm 0 (n + 1) =
      (1 - q) * sourceTerm 0 0 (1, n) := by
  have h1 : reflectedExponent 1 (n + 1) = 1 + 3 * n + 3 * n ^ 2 := by
    have h := reflectedExponent_cast 1 (n + 1)
    push_cast at h
    nlinarith
  have h0 : reflectedExponent 0 (n + 1) = 3 * (n + 1) ^ 2 := by
    have h := reflectedExponent_cast 0 (n + 1)
    push_cast at h
    nlinarith
  have huQ (k : ℕ) : IsUnit (q ^ 3; q ^ 3)_k := by simpa using isUnit_qPochhammer_q 2 k
  have hQ := bInv_qFactorial_step (q ^ 3) n (huQ n) (huQ (n + 1))
  have huq : IsUnit (q; q)_1 := by simpa using isUnit_qPochhammer_q 0 1
  have hq : (1 - q) * bInv (q; q)_1 = 1 := by simpa only [qPochhammer_one] using huq.mul_bInv_cancel
  simp only [reflectedCoreTerm, sourceTerm, h1, h0, one_pow, mul_one, zero_mul, add_zero]
  linear_combination q ^ (1 + 3 * n + 3 * n ^ 2) * hQ -
    q ^ (1 + 3 * n + 3 * n ^ 2) * bInv (q ^ 3; q ^ 3)_n * hq

private theorem reflectedCore_initial :
    reflectedCore 1 - q * reflectedCore 0 = (1 - q) * sourceRow 0 0 1 := by
  have hl := (summable_reflectedCore 1).hasSum.sub ((summable_reflectedCore 0).hasSum.mul_left q)
  have hr := ((summable_sourceRow_terms 0 0 1).hasSum.mul_left (1 - q)).congr_fun
    (fun n => reflectedCore_initial_term n)
  have hz : reflectedCoreTerm 1 0 - q * reflectedCoreTerm 0 0 = 0 := by
    norm_num [reflectedCoreTerm, reflectedExponent]
  have hh := (hasSum_nat_add_iff (f := fun n => reflectedCoreTerm 1 n - q * reflectedCoreTerm 0 n) 1).mp hr
  simp only [Finset.sum_range_one, hz, add_zero] at hh
  exact hl.unique hh

/-- Paper `eq:app-g-initial`, written with the positive source coefficients. -/
theorem reflected_coeff_one : coeff 1 reflectedSeries =
    coeff 1 (sourceSeries 0 0) + q * bInv (q; q)_1 * coeff 0 (sourceSeries 0 0) := by
  have h0 := reflected_coeff_zero
  rw [coeff_reflectedSeries] at h0
  simp only [qPochhammer_zero, bInv_one, one_mul] at h0
  rw [coeff_reflectedSeries]
  have hi := reflectedCore_initial
  have hu : IsUnit (q; q)_1 := by simpa using isUnit_qPochhammer_q 0 1
  have hc : bInv (q; q)_1 * (1 - q) = 1 := by simpa only [qPochhammer_one] using hu.bInv_mul_cancel
  rw [show coeff 1 (sourceSeries 0 0) = sourceRow 0 0 1 by simp [sourceSeries]]
  change bInv (q; q)_1 * reflectedCore 1 = sourceRow 0 0 1 +
    q * bInv (q; q)_1 * coeff 0 (sourceSeries 0 0)
  linear_combination bInv (q; q)_1 * hi + sourceRow 0 0 1 * hc + q * bInv (q; q)_1 * h0

end KanadeRussell.Source
