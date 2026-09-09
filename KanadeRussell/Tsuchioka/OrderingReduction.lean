import KanadeRussell.Tsuchioka.ExceptionalReduction
import KanadeRussell.Tsuchioka.Phases

/-!
# The ordering reduction (F1)

The hypotheses are finite truncations of the first two relations of
Tsuchioka's Theorem 3.2, modulo shorter words. This file derives (F1) in
every residue class, using the corrected exceptional relation.
The identities on the actual representation still have to be proved.
-/

open scoped BigOperators

namespace KanadeRussell.Tsuchioka

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def symmetricSum (value : Word → V) (c : ℕ → K) (a b : ℤ) (N : ℕ) : V :=
  ∑ p ∈ Finset.range N,
    c p • (value [a - p, b + p] + value [b - p, a + p])

theorem symmetricSum_sub_target_mem (value : Word → V) (c : ℕ → K)
    (hc : c 0 = 1) (a b : ℤ) (hab : b < a) (N : ℕ) :
    symmetricSum value c a b (N + 1) - value [a, b] ∈
      higherSpan (K := K) value [a, b] := by
  let S := higherSpan (K := K) value [a, b]
  have htail :
      (∑ p ∈ Finset.range N,
        c (p + 1) • (value [a - (p + 1 : ℕ), b + (p + 1 : ℕ)] +
          value [b - (p + 1 : ℕ), a + (p + 1 : ℕ)])) ∈ S := by
    apply Submodule.sum_mem
    intro p hp
    apply Submodule.smul_mem
    apply Submodule.add_mem
    · exact mem_higherSpan value (higher_pair_shift a b (p + 1) (by omega)) (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
    · exact mem_higherSpan value (higher_pair_swap a b (p + 1) hab) (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
  have hswap : value [b, a] ∈ S := by
    simpa using mem_higherSpan (K := K) value (higher_pair_swap a b 0 hab) (by simp only [List.sum_cons, List.sum_nil, add_zero]; ring)
  convert S.add_mem htail hswap using 1
  simp only [symmetricSum, Finset.sum_range_succ', hc, Nat.cast_zero,
    sub_zero, add_zero, one_smul]
  abel

theorem nonexceptional_ordering_reduction
    (value : Word → V) (c₁ c₂ : ℕ → K) (hc₁ : c₁ 0 = 1) (hc₂ : c₂ 0 = 1)
    (a b : ℤ) (hab : b < a) (N M : ℕ) (zprime : V)
    (u v : K) (hne : v - u ≠ 0)
    (h₁ : skewSum value c₁ a b (N + 1) - (u / 12) • zprime ∈
      higherSpan (K := K) value [a, b])
    (h₂ : symmetricSum value c₂ a b (M + 1) - (v / 12) • zprime ∈
      higherSpan (K := K) value [a, b]) :
    value [a, b] ∈ higherSpan (K := K) value [a, b] := by
  let S := higherSpan (K := K) value [a, b]
  have ht₁ := skewSum_sub_target_mem value c₁ hc₁ a b hab N
  have ht₂ := symmetricSum_sub_target_mem value c₂ hc₂ a b hab M
  have hcomb := S.sub_mem (S.smul_mem v h₁) (S.smul_mem u h₂)
  have htail := S.sub_mem (S.smul_mem v ht₁) (S.smul_mem u ht₂)
  have hlead : (v - u) • value [a, b] ∈ S := by
    convert S.sub_mem hcomb htail using 1
    module
  exact (S.smul_mem_iff hne).mp hlead

variable [CharZero K]

/-- The second-root coefficient in the skew relation, before division by 12. -/
def skewPhase (w : K) (a b : ℤ) : K :=
  (-52 + 104 * w ^ 2 + 90 * w ^ 3) *
    (w ^ (4 * a + 9 * b) - w ^ (9 * a + 4 * b))

/-- The second-root coefficient in the symmetric relation, before division by 12. -/
def symmetricPhase (w : K) (a b : ℤ) : K :=
  (-24 - 28 * w + 14 * w ^ 3) *
    (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b))

/-- F1 for arbitrary integer A>B, conditional on the stated finite operator
relations. In the exceptional class only the two skew relations are needed. -/
theorem ordering_reduction_of_relations
    (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (value : Word → V) (c₁ c₂ : ℕ → K) (hc₁ : c₁ 0 = 1) (hc₂ : c₂ 0 = 1)
    (a b : ℤ) (hab : b < a) (N M L : ℕ) (zprime : V)
    (h₁ : skewSum value c₁ a b (N + 1) - (skewPhase w a b / 12) • zprime ∈
      higherSpan (K := K) value [a, b])
    (h₂ : symmetricSum value c₂ a b (M + 1) -
        (symmetricPhase w a b / 12) • zprime ∈
      higherSpan (K := K) value [a, b])
    (hshift : skewSum value c₁ (a - 1) (b + 1) L -
        (skewPhase w (a - 1) (b + 1) / 12) • zprime ∈
      higherSpan (K := K) value [a, b]) :
    value [a, b] ∈ higherSpan (K := K) value [a, b] := by
  by_cases hr : (a - b) % 12 = 7
  · have he : skewPhase w (a - 1) (b + 1) = skewPhase w a b := by
      dsimp [skewPhase]
      rw [Coefficients.exceptional_cancellation w hw a b hr]
    rw [he] at hshift
    exact exceptional_ordering_reduction value c₁ hc₁ a b hab hr N L zprime
      (skewPhase w a b / 12) h₁ hshift
  · have hne : symmetricPhase w a b - skewPhase w a b ≠ 0 :=
      fun h => hr ((Coefficients.orderingLeading_eq_zero_iff w hw a b).mp h)
    exact nonexceptional_ordering_reduction value c₁ c₂ hc₁ hc₂ a b hab N M zprime
      (skewPhase w a b) (symmetricPhase w a b) hne h₁ h₂

end KanadeRussell.Tsuchioka
