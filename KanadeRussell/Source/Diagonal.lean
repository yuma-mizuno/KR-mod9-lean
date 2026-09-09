import KanadeRussell.Source.Contiguity
import KanadeRussell.Infra.Weighted
set_option backward.isDefEq.respectTransparency false

/-! The antidiagonal source series F(q^a x,q^b x³) and its polynomial contiguities. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell.Source
open Infra

private def diagonalWeight (mn : ℕ × ℕ) : ℕ := mn.1 + 3 * mn.2

noncomputable def diagonalSeries (a b : ℕ) : PowerSeries QSeries :=
  weightedSeries diagonalWeight (sourceTerm a b)

private noncomputable def diagonalTerm (a b : ℕ) (mn : ℕ × ℕ) : PowerSeries QSeries :=
  monomial (diagonalWeight mn) (sourceTerm a b mn)

private theorem hasSum_diagonal (a b : ℕ) : HasSum (diagonalTerm a b) (diagonalSeries a b) :=
  hasSum_weightedSeries diagonalWeight (summable_sourceTerm a b)

theorem diagonalSeries_summableCoeff (a b : ℕ) : SummableCoeff (diagonalSeries a b) :=
  weightedSeries_summableCoeff diagonalWeight (summable_sourceTerm a b)

theorem sumCoeff_diagonalSeries (a b : ℕ) :
    sumCoeff (diagonalSeries a b) = ∑' mn, sourceTerm a b mn :=
  sumCoeff_weightedSeries diagonalWeight (summable_sourceTerm a b)

theorem sourceTerm_m_contiguity (a b m n : ℕ) :
    sourceTerm a b (m + 1, n) - sourceTerm (a + 1) b (m + 1, n) =
      q ^ (a + 1) * sourceTerm (a + 2) (b + 3) (m, n) := by
  rw [← sourceTerm_rescale a b (m + 1) n, ← one_sub_mul]
  have hu (k : ℕ) : IsUnit (q; q)_k := by simpa using isUnit_qPochhammer_q 0 k
  have hc := bInv_qFactorial_step q m (hu m) (hu (m + 1))
  have he : (m + 1) ^ 2 + 3 * (m + 1) * n + 3 * n ^ 2 + a * (m + 1) + b * n =
      (a + 1) + (m ^ 2 + 3 * m * n + 3 * n ^ 2 + (a + 2) * m + (b + 3) * n) := by ring
  simp only [sourceTerm]
  rw [he, pow_add]
  linear_combination q ^ (a + 1) * q ^ (m ^ 2 + 3 * m * n + 3 * n ^ 2 + (a + 2) * m + (b + 3) * n) *
    bInv (q ^ 3; q ^ 3)_n * hc

theorem sourceTerm_bshift (a b m n : ℕ) :
    (q ^ 3) ^ n * sourceTerm a b (m, n) = sourceTerm a (b + 3) (m, n) := by
  simp only [sourceTerm]
  rw [← mul_assoc, ← mul_assoc, ← pow_mul, ← pow_add]
  congr 2
  congr 1
  ring

theorem sourceTerm_n_contiguity (a b m n : ℕ) :
    sourceTerm a b (m, n + 1) - sourceTerm a (b + 3) (m, n + 1) =
      q ^ (b + 3) * sourceTerm (a + 3) (b + 6) (m, n) := by
  rw [← sourceTerm_bshift a b m (n + 1), ← one_sub_mul]
  have hu (k : ℕ) : IsUnit (q ^ 3; q ^ 3)_k := by simpa using isUnit_qPochhammer_q 2 k
  have hc := bInv_qFactorial_step (q ^ 3) n (hu n) (hu (n + 1))
  have he : m ^ 2 + 3 * m * (n + 1) + 3 * (n + 1) ^ 2 + a * m + b * (n + 1) =
      (b + 3) + (m ^ 2 + 3 * m * n + 3 * n ^ 2 + (a + 3) * m + (b + 6) * n) := by ring
  simp only [sourceTerm]
  rw [he, pow_add]
  linear_combination q ^ (b + 3) * q ^ (m ^ 2 + 3 * m * n + 3 * n ^ 2 + (a + 3) * m + (b + 6) * n) *
    bInv (q; q)_m * hc

private theorem diagonalTerm_m_contiguity (a b m n : ℕ) :
    diagonalTerm a b (m + 1, n) - diagonalTerm (a + 1) b (m + 1, n) =
      PowerSeries.C (q ^ (a + 1)) * X * diagonalTerm (a + 2) (b + 3) (m, n) := by
  simp only [diagonalTerm, monomial_eq_C_mul_X_pow]
  rw [← sub_mul, ← map_sub, sourceTerm_m_contiguity, map_mul]
  simp only [diagonalWeight, show m + 1 + 3 * n = 1 + (m + 3 * n) by omega, pow_add, pow_one]
  ring

private theorem diagonalTerm_n_contiguity (a b m n : ℕ) :
    diagonalTerm a b (m, n + 1) - diagonalTerm a (b + 3) (m, n + 1) =
      PowerSeries.C (q ^ (b + 3)) * X ^ 3 * diagonalTerm (a + 3) (b + 6) (m, n) := by
  simp only [diagonalTerm, monomial_eq_C_mul_X_pow]
  rw [← sub_mul, ← map_sub, sourceTerm_n_contiguity, map_mul]
  simp only [diagonalWeight, show m + 3 * (n + 1) = 3 + (m + 3 * n) by omega, pow_add]
  ring

/-- The first F-contiguity for the antidiagonal series, with the m=0 boundary included. -/
theorem diagonal_m_contiguity (a b : ℕ) :
    diagonalSeries a b - diagonalSeries (a + 1) b =
      PowerSeries.C (q ^ (a + 1)) * X * diagonalSeries (a + 2) (b + 3) := by
  let shift : ℕ × ℕ → ℕ × ℕ := fun mn => (mn.1 + 1, mn.2)
  have hi : Function.Injective shift := by
    rintro ⟨m, n⟩ ⟨r, s⟩ h
    simp only [shift, Prod.mk.injEq] at h ⊢
    omega
  have hz : ∀ mn ∉ Set.range shift, diagonalTerm a b mn - diagonalTerm (a + 1) b mn = 0 := by
    rintro ⟨m, n⟩ hn
    cases m with
    | zero => simp [diagonalTerm, sourceTerm]
    | succ m => exact False.elim (hn ⟨(m, n), rfl⟩)
  have hr := ((hasSum_diagonal (a + 2) (b + 3)).mul_left
    (PowerSeries.C (q ^ (a + 1)) * X)).congr_fun
      (fun mn : ℕ × ℕ => diagonalTerm_m_contiguity a b mn.1 mn.2)
  have hh := (hi.hasSum_iff hz).mp hr
  exact ((hasSum_diagonal a b).sub (hasSum_diagonal (a + 1) b)).unique hh

/-- The second F-contiguity for the antidiagonal series, with the n=0 boundary included. -/
theorem diagonal_n_contiguity (a b : ℕ) :
    diagonalSeries a b - diagonalSeries a (b + 3) =
      PowerSeries.C (q ^ (b + 3)) * X ^ 3 * diagonalSeries (a + 3) (b + 6) := by
  let shift : ℕ × ℕ → ℕ × ℕ := fun mn => (mn.1, mn.2 + 1)
  have hi : Function.Injective shift := by
    rintro ⟨m, n⟩ ⟨r, s⟩ h
    simp only [shift, Prod.mk.injEq] at h ⊢
    omega
  have hz : ∀ mn ∉ Set.range shift, diagonalTerm a b mn - diagonalTerm a (b + 3) mn = 0 := by
    rintro ⟨m, n⟩ hn
    cases n with
    | zero => simp [diagonalTerm, sourceTerm]
    | succ n => exact False.elim (hn ⟨(m, n), rfl⟩)
  have hr := ((hasSum_diagonal (a + 3) (b + 6)).mul_left
    (PowerSeries.C (q ^ (b + 3)) * X ^ 3)).congr_fun
      (fun mn : ℕ × ℕ => diagonalTerm_n_contiguity a b mn.1 mn.2)
  have hh := (hi.hasSum_iff hz).mp hr
  exact ((hasSum_diagonal a b).sub (hasSum_diagonal a (b + 3))).unique hh

/-- Each x-coefficient is a finite antidiagonal sum, as required by design D6. -/
theorem coeff_diagonalSeries (a b j : ℕ) :
    coeff j (diagonalSeries a b) =
      ∑ mn ∈ Finset.range (j + 1) ×ˢ Finset.range (j + 1),
        if j = mn.1 + 3 * mn.2 then sourceTerm a b mn else 0 := by
  simp only [diagonalSeries, weightedSeries, coeff_mk, diagonalWeight]
  apply tsum_eq_sum
  intro mn hmn
  have hne : j ≠ mn.1 + 3 * mn.2 := by
    intro he
    apply hmn
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  simp only [if_neg hne]

private theorem sourceTerm_diagonal_rescale (a b k : ℕ) (mn : ℕ × ℕ) :
    (q ^ k) ^ diagonalWeight mn * sourceTerm a b mn =
      sourceTerm (a + k) (b + 3 * k) mn := by
  simp only [sourceTerm, diagonalWeight]
  rw [← mul_assoc, ← mul_assoc, ← pow_mul, ← pow_add]
  congr 2
  congr 1
  ring

private theorem diagonalTerm_rescale (a b k : ℕ) (mn : ℕ × ℕ) :
    rescale (q ^ k) (diagonalTerm a b mn) = diagonalTerm (a + k) (b + 3 * k) mn := by
  apply PowerSeries.ext
  intro j
  simp only [coeff_rescale, diagonalTerm, coeff_monomial]
  split_ifs with he
  · rw [he]
    exact sourceTerm_diagonal_rescale a b k mn
  · simp

theorem diagonalSeries_rescale (a b k : ℕ) :
    rescale (q ^ k) (diagonalSeries a b) = diagonalSeries (a + k) (b + 3 * k) := by
  have h := ((hasSum_diagonal a b).map (rescale (q ^ k)) (continuous_rescale _)).congr_fun
    (fun mn => (diagonalTerm_rescale a b k mn).symm)
  exact h.unique (hasSum_diagonal (a + k) (b + 3 * k))

noncomputable def p : PowerSeries QSeries := diagonalSeries 1 0
noncomputable def f₀ : PowerSeries QSeries := diagonalSeries 0 0

/-- Paper `eq:app-p-recurrence`; exact certificate from five F-contiguities.
The independent symbolic derivation is in `Comparator/certificates/find_p_recurrence.py`. -/
theorem p_recurrence :
    p = (1 - PowerSeries.C q * X) * rescale q p +
      PowerSeries.C q * X * (1 + PowerSeries.C q + PowerSeries.C (q ^ 2) * X ^ 2) *
        rescale (q ^ 2) p + PowerSeries.C (q ^ 4) * X ^ 2 * rescale (q ^ 3) p := by
  have hM00 := diagonal_m_contiguity 0 0
  have hN00 := diagonal_n_contiguity 0 0
  have hM03 := diagonal_m_contiguity 0 3
  have hM13 := diagonal_m_contiguity 1 3
  have hM26 := diagonal_m_contiguity 2 6
  simp only [Nat.reduceAdd, Nat.zero_add, pow_one] at hM00 hN00 hM03 hM13 hM26
  unfold p
  rw [show rescale q (diagonalSeries 1 0) = diagonalSeries 2 3 by
    simpa using diagonalSeries_rescale 1 0 1, diagonalSeries_rescale, diagonalSeries_rescale]
  norm_num only [Nat.reduceAdd, Nat.reduceMul] at *
  simp only [map_pow] at *
  linear_combination -hM00 + hN00 + hM03 + hM13 + PowerSeries.C q * X * hM26

/-- The first bridge in paper `eq:app-p-bridges`. -/
theorem f₀_eq_p_add : f₀ = p + PowerSeries.C q * X * rescale q p := by
  have h := diagonal_m_contiguity 0 0
  have hs : rescale q p = diagonalSeries 2 3 := by
    simpa [p] using diagonalSeries_rescale 1 0 1
  rw [hs]
  change diagonalSeries 0 0 = diagonalSeries 1 0 + PowerSeries.C q * X * diagonalSeries 2 3
  simpa using (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

@[simp] theorem sumCoeff_f₀ : sumCoeff f₀ = A := sumCoeff_diagonalSeries 0 0

@[simp] theorem sumCoeff_rescale_f₀ : sumCoeff (rescale q f₀) = B := by
  have h : rescale q f₀ = diagonalSeries 1 3 := by
    simpa [f₀] using diagonalSeries_rescale 0 0 1
  rw [h, sumCoeff_diagonalSeries]
  rfl

@[simp] theorem sumCoeff_rescale_p : sumCoeff (rescale q p) = C := by
  have h : rescale q p = diagonalSeries 2 3 := by
    simpa [p] using diagonalSeries_rescale 1 0 1
  rw [h, sumCoeff_diagonalSeries]
  rfl

@[simp] theorem constantCoeff_diagonalSeries (a b : ℕ) : constantCoeff (diagonalSeries a b) = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_diagonalSeries]
  simp [sourceTerm]

@[simp] theorem coeff_one_f₀ : coeff 1 f₀ = q * bInv (q; q)_1 := by
  rw [f₀, coeff_diagonalSeries]
  norm_num [Finset.sum_product, Finset.sum_range_succ, sourceTerm]

end KanadeRussell.Source
