import KanadeRussell.Tsuchioka.OrderingReduction

/-!
# Low-mode extraction for the repeated and adjacent reductions (F2), (F3)

All truncation cutoffs are explicit. The higher spans preserve total index.
-/

open scoped BigOperators

namespace KanadeRussell.Tsuchioka

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem symmetricSum_repeated_sub_mem (value : Word → V) (c : ℕ → K)
    (a : ℤ) (N : ℕ) :
    symmetricSum value c a a (N + 1) - (2 * c 0) • value [a, a] ∈
      higherSpan (K := K) value [a, a] := by
  let S := higherSpan (K := K) value [a, a]
  have ht :
      (∑ p ∈ Finset.range N,
        c (p + 1) • (value [a - (p + 1 : ℕ), a + (p + 1 : ℕ)] +
          value [a - (p + 1 : ℕ), a + (p + 1 : ℕ)])) ∈ S := by
    apply Submodule.sum_mem
    intro p hp
    have hv := mem_higherSpan (K := K) value (higher_pair_shift a a (p + 1) (by omega))
      (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
    exact S.smul_mem _ (S.add_mem hv hv)
  convert ht using 1
  simp only [symmetricSum, Finset.sum_range_succ', Nat.cast_zero, sub_zero, add_zero]
  module

theorem symmetricSum_adjacent_sub_mem (value : Word → V) (c : ℕ → K)
    (a : ℤ) (N : ℕ) :
    symmetricSum value c a (a + 1) (N + 2) -
      ((c 0 + c 1) • value [a, a + 1] + c 0 • value [a + 1, a]) ∈
      higherSpan (K := K) value [a, a + 1] := by
  let S := higherSpan (K := K) value [a, a + 1]
  have ht :
      (∑ p ∈ Finset.range N,
        c (p + 2) • (value [a - (p + 2 : ℕ), a + 1 + (p + 2 : ℕ)] +
          value [a + 1 - (p + 2 : ℕ), a + (p + 2 : ℕ)])) ∈ S := by
    apply Submodule.sum_mem
    intro p hp
    apply Submodule.smul_mem
    apply Submodule.add_mem
    · exact mem_higherSpan value (higher_pair_shift a (a + 1) (p + 2) (by omega))
        (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
    · exact mem_higherSpan value (higher_adjacent_swap a (p + 2) (by omega))
        (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
  have hn : c 1 • value [a - 1, a + 1 + 1] ∈ S := by
    apply Submodule.smul_mem
    exact mem_higherSpan value (higher_pair_shift a (a + 1) 1 (by omega))
      (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
  convert S.add_mem ht hn using 1
  simp only [symmetricSum, Finset.sum_range_succ', Nat.cast_zero, Nat.cast_one,
    sub_zero, add_zero, Nat.zero_add, add_sub_cancel_right, Nat.add_assoc]
  module

theorem skewSum_adjacent_sub_mem (value : Word → V) (c : ℕ → K)
    (a : ℤ) (N : ℕ) :
    skewSum value c a (a + 1) (N + 2) -
      ((c 0 - c 1) • value [a, a + 1] - c 0 • value [a + 1, a]) ∈
      higherSpan (K := K) value [a, a + 1] := by
  let S := higherSpan (K := K) value [a, a + 1]
  have ht :
      (∑ p ∈ Finset.range N,
        c (p + 2) • (value [a - (p + 2 : ℕ), a + 1 + (p + 2 : ℕ)] -
          value [a + 1 - (p + 2 : ℕ), a + (p + 2 : ℕ)])) ∈ S := by
    apply Submodule.sum_mem
    intro p hp
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact mem_higherSpan value (higher_pair_shift a (a + 1) (p + 2) (by omega))
        (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
    · exact mem_higherSpan value (higher_adjacent_swap a (p + 2) (by omega))
        (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
  have hn : c 1 • value [a - 1, a + 1 + 1] ∈ S := by
    apply Submodule.smul_mem
    exact mem_higherSpan value (higher_pair_shift a (a + 1) 1 (by omega))
      (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
  convert S.add_mem ht hn using 1
  simp only [skewSum, Finset.sum_range_succ', Nat.cast_zero, Nat.cast_one,
    sub_zero, add_zero, Nat.zero_add, add_sub_cancel_right, Nat.add_assoc]
  module


/-- Cancel a common mode from two relations, before extracting the leading
word. In the source the common mode is the second root family Z'. -/
theorem eliminate_common_mode (S : Submodule K V) (x y z : V) (α β : K)
    (hβ : β ≠ 0) (hx : x - α • z ∈ S) (hy : y - β • z ∈ S) :
    x - (α / β) • y ∈ S := by
  have h := S.sub_mem hx (S.smul_mem (α / β) hy)
  have hc : (α / β) * β = α := div_mul_cancel₀ α hβ
  convert h using 1
  simp only [smul_sub, smul_smul, hc]
  abel

variable [CharZero K]

/-- F2 extracted from the combined second and third relations. Those
relations apply in the source when the repeated pair has sum nonzero mod 3. -/
theorem repeated_reduction_of_combined_relation
    (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (value : Word → V) (c₂ c₃ : ℕ → K) (hc₂ : c₂ 0 = 1) (hc₃ : c₃ 0 = 1)
    (a : ℤ) (N M : ℕ)
    (hrel : symmetricSum value c₂ a a (N + 1) -
      (Coefficients.tCoeff w / Coefficients.mCoeff w) •
        symmetricSum value c₃ a a (M + 1) ∈
      higherSpan (K := K) value [a, a]) :
    value [a, a] ∈ higherSpan (K := K) value [a, a] := by
  let S := higherSpan (K := K) value [a, a]
  let r := Coefficients.tCoeff w / Coefficients.mCoeff w
  have h₂ := symmetricSum_repeated_sub_mem value c₂ a N
  have h₃ := symmetricSum_repeated_sub_mem value c₃ a M
  have ht := S.sub_mem h₂ (S.smul_mem r h₃)
  have hlead : (2 * (1 - r)) • value [a, a] ∈ S := by
    convert S.sub_mem hrel ht using 1
    rw [hc₂, hc₃]
    module
  have hn : 2 * (1 - r) ≠ 0 := by
    dsimp [r]
    rw [Coefficients.f2_coefficient w hw]
    intro hz
    apply Coefficients.f2_ne_zero w hw
    linear_combination hz
  exact (S.smul_mem_iff hn).mp hlead

/-- F3 extracted from the combined second/third relation and the fourth
relation. The coefficient of the reversed pair cancels exactly; the remaining
coefficient is the corrected nonzero value in Section 4.6. -/
theorem adjacent_reduction_of_combined_relations
    (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (value : Word → V) (c₂ c₃ c₆ : ℕ → K)
    (hc₂₀ : c₂ 0 = 1) (hc₃₀ : c₃ 0 = 1)
    (hc₂₁ : c₂ 1 = (-4 * w + 2 * w ^ 3) / 3)
    (hc₃₁ : c₃ 1 = (6 - 4 * w + 2 * w ^ 3) / 3)
    (hc₆₀ : c₆ 0 = 1 - Coefficients.pCoeff w / Coefficients.qCoeff w)
    (hc₆₁ : c₆ 1 = (4 * w - 2 * w ^ 3) / 3)
    (a : ℤ) (N M L : ℕ)
    (h₂₃ : symmetricSum value c₂ a (a + 1) (N + 2) -
      (Coefficients.tCoeff w / Coefficients.mCoeff w) •
        symmetricSum value c₃ a (a + 1) (M + 2) ∈
      higherSpan (K := K) value [a, a + 1])
    (h₆ : skewSum value c₆ a (a + 1) (L + 2) ∈
      higherSpan (K := K) value [a, a + 1]) :
    value [a, a + 1] ∈ higherSpan (K := K) value [a, a + 1] := by
  let S := higherSpan (K := K) value [a, a + 1]
  let r := Coefficients.tCoeff w / Coefficients.mCoeff w
  let c := 1 - Coefficients.pCoeff w / Coefficients.qCoeff w
  have ht₂ := symmetricSum_adjacent_sub_mem value c₂ a N
  have ht₃ := symmetricSum_adjacent_sub_mem value c₃ a M
  have ht₆ := skewSum_adjacent_sub_mem value c₆ a L
  have hr := S.add_mem (S.smul_mem c h₂₃) (S.smul_mem (1 - r) h₆)
  have ht := S.add_mem
    (S.smul_mem c (S.sub_mem ht₂ (S.smul_mem r ht₃)))
    (S.smul_mem (1 - r) ht₆)
  have hlead : (8 * (2 + 2 * w - w ^ 3)) • value [a, a + 1] ∈ S := by
    rw [← Coefficients.f3_coefficient_from_ratios w hw]
    convert S.sub_mem hr ht using 1
    rw [hc₂₀, hc₃₀, hc₂₁, hc₃₁, hc₆₀, hc₆₁]
    dsimp [r, c]
    module
  have hn : 8 * (2 + 2 * w - w ^ 3) ≠ 0 := by
    intro hz
    apply Coefficients.f3_ne_zero w hw
    linear_combination hz
  exact (S.smul_mem_iff hn).mp hlead



end KanadeRussell.Tsuchioka
