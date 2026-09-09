import Mathlib

/-! Coefficientwise formal exponentials with an explicit finite cutoff. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

open scoped BigOperators
open PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The formal exponential of a series. All uses below require zero constant term. -/
noncomputable def exponential (f : PowerSeries A) : PowerSeries A :=
  (PowerSeries.exp A).subst f

omit [Algebra ℚ A] in
theorem coeff_pow_eq_zero_of_lt {f : PowerSeries A}
    (hf : constantCoeff f = 0) {n d : ℕ} (h : n < d) :
    coeff n (f ^ d) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h)
    (le_order_pow_of_constantCoeff_eq_zero d hf)

/-- The coefficient of degree n requires only powers zero through n. -/
theorem coeff_exponential {f : PowerSeries A} (hf : constantCoeff f = 0) (n : ℕ) :
    coeff n (exponential f) =
      ∑ d ∈ Finset.range (n + 1),
        algebraMap ℚ A (1 / (d.factorial : ℚ)) * coeff n (f ^ d) := by
  rw [exponential, coeff_subst' (HasSubst.of_constantCoeff_zero' hf)]
  simp only [coeff_exp, smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  by_contra hn
  have hnd : n < d := by simpa using hn
  exact hd (by simp [coeff_pow_eq_zero_of_lt hf hnd])

@[simp] theorem constantCoeff_exponential {f : PowerSeries A}
    (hf : constantCoeff f = 0) :
    constantCoeff (exponential f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_exponential hf]
  simp

@[simp] theorem coeff_one_exponential {f : PowerSeries A}
    (hf : constantCoeff f = 0) :
    coeff 1 (exponential f) = coeff 1 f := by
  rw [coeff_exponential hf]
  simp [Finset.sum_range_succ]

theorem coeff_two_exponential {f : PowerSeries A}
    (hf : constantCoeff f = 0) :
    coeff 2 (exponential f) = coeff 2 f + algebraMap ℚ A (1 / 2) * coeff 1 f ^ 2 := by
  have hp : coeff 2 (f ^ 2) = coeff 1 f ^ 2 := by
    rw [pow_two, coeff_mul]
    have ha : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := rfl
    simp [ha, coeff_zero_eq_constantCoeff, hf, pow_two]
  rw [coeff_exponential hf]
  norm_num [Finset.sum_range_succ, hp]

theorem derivative_exponential {f : PowerSeries A} (hf : constantCoeff f = 0) :
    derivative A (exponential f) = exponential f * derivative A f := by
  rw [exponential, derivative_subst A (HasSubst.of_constantCoeff_zero' hf),
    PowerSeries.derivative_exp]

omit [Algebra ℚ A] in
/-- A formal first-order differential equation is determined by its constant term. -/
theorem differential_unique [IsAddTorsionFree A] (b : PowerSeries A)
    {f g : PowerSeries A} (hf : derivative A f = b * f)
    (hg : derivative A g = b * g) (hc : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff] using hc
    | succ n =>
      have he : coeff n (derivative A f) = coeff n (derivative A g) := by
        rw [hf, hg, coeff_mul, coeff_mul]
        apply Finset.sum_congr rfl
        intro ij hij
        have hs : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        rw [ih ij.2 (by omega)]
      rw [coeff_derivative, coeff_derivative, ← Nat.cast_succ,
        mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul] at he
      exact (smul_right_inj (Nat.succ_ne_zero n)).mp he

theorem exponential_add {f g : PowerSeries A}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    exponential (f + g) = exponential f * exponential g := by
  letI : IsAddTorsionFree A := .of_module_rat A
  have hfg : constantCoeff (f + g) = 0 := by simp [hf, hg]
  apply differential_unique (derivative A f + derivative A g)
  · rw [derivative_exponential hfg, map_add]
    ring
  · rw [Derivation.leibniz, derivative_exponential hf, derivative_exponential hg]
    simp only [smul_eq_mul]
    ring
  · simp [hf, hg, hfg]

theorem map_exponential {B : Type*} [CommRing B] [Algebra ℚ B]
    (h : A →+* B) {f : PowerSeries A} (hf : constantCoeff f = 0) :
    PowerSeries.map h (exponential f) = exponential (PowerSeries.map h f) := by
  change MvPowerSeries.map h ((PowerSeries.exp A).subst f) =
    exponential (PowerSeries.map h f)
  rw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' hf)]
  change (PowerSeries.map h (PowerSeries.exp A)).subst (PowerSeries.map h f) = _
  rw [PowerSeries.map_exp]
  rfl

@[simp] theorem exponential_zero : exponential (0 : PowerSeries A) = 1 := by
  ext n
  rw [coeff_exponential (by simp)]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    simp [zero_pow hk0]
  · intro h
    simp at h

theorem exponential_sum {ι : Type*} (s : Finset ι)
    (f : ι → PowerSeries A) (hf : ∀ i ∈ s, constantCoeff (f i) = 0) :
    exponential (∑ i ∈ s, f i) = ∏ i ∈ s, exponential (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have hfs : ∀ j ∈ s, constantCoeff (f j) = 0 :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hs : constantCoeff (∑ j ∈ s, f j) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero hfs
    rw [Finset.sum_insert his, Finset.prod_insert his,
      exponential_add (hf i (by simp)) hs, ih hfs]

theorem exponential_mul_neg {f : PowerSeries A}
    (hf : constantCoeff f = 0) : exponential f * exponential (-f) = 1 := by
  rw [← exponential_add hf (by simp [hf])]
  simp

end KanadeRussell.Tsuchioka.FormalSeries
