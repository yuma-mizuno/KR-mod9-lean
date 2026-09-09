import KanadeRussell.Representation.WeylWeightReflection

/-! A reflection-invariant coefficient function supported in the positive cone
is supported on nonnegative multiples of the null root. No claim about an
actual residual series is assumed. -/
set_option autoImplicit false
namespace KanadeRussell.Representation.AffineWeightLattice
open Tsuchioka.Fock

theorem eq_nat_smul_marks_of_nonneg_of_dominant_zero (beta : RootCoefficients)
    (hbeta : ∀ i, 0 ≤ beta i) (hdom : ∀ i, 0 ≤ weightLabels 0 beta i) :
    ∃ n : ℕ, beta = (n : ℤ) • marks := by
  have hlevel := level_weightLabels 0 beta
  simp only [level, Pi.zero_apply, mul_zero, add_zero] at hlevel
  have h0 := hdom 0
  have h1 := hdom 1
  have h2 := hdom 2
  have hz0 : weightLabels 0 beta 0 = 0 := by omega
  have hz2 : weightLabels 0 beta 2 = 0 := by omega
  have hquad : rootQuadratic beta = 0 := by
    rw [rootQuadratic_eq_zero_iff]
    norm_num [weightLabels, Fin.sum_univ_three, affineCartanMatrix, Matrix.cons_val_two] at hz0 hz2
    omega
  obtain ⟨t, ht⟩ := (rootQuadratic_eq_zero_iff_multiple_marks beta).mp hquad
  have ht0 : 0 ≤ t := by
    have hb0 := hbeta 0
    rw [ht] at hb0
    simpa [marks] using hb0
  exact ⟨t.toNat, by rw [Int.toNat_of_nonneg ht0]; exact ht⟩

theorem simpleReflection_zero_smul_marks (i : Fin 3) (t : ℤ) :
    simpleReflection 0 i (t • marks) = t • marks := by
  have h00 : weightLabels 0 0 = 0 := by
    ext j
    simp [weightLabels]
  have hw : weightLabels 0 (t • marks) = 0 := by
    simpa only [zero_add, h00] using weightLabels_add_marks 0 0 t
  rw [simpleReflection, hw]
  simp

variable {K : Type*} [Zero K]

/-- Every nonzero invariant cone-supported coefficient is at a nonnegative null root. -/
theorem invariant_nonzero_eq_nat_smul_marks (a : RootCoefficients → K)
    (hsupport : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → a beta = 0)
    (hinvariant : ∀ i beta, a (simpleReflection 0 i beta) = a beta)
    (beta : RootCoefficients) (ha : a beta ≠ 0) :
    ∃ n : ℕ, beta = (n : ℤ) • marks := by
  classical
  have hnonneg (gamma : RootCoefficients) (hg : a gamma ≠ 0) : ∀ i, 0 ≤ gamma i := by
    by_contra hn
    exact hg (hsupport gamma hn)
  have heq : ∀ n : ℕ, ∀ gamma : RootCoefficients, (totalDegree gamma).toNat=n →
      a gamma ≠ 0 → ∃ m : ℕ, gamma = (m : ℤ) • marks := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro gamma hdegree hg
      have hgamma := hnonneg gamma hg
      by_cases hdom : ∀ i, 0 ≤ weightLabels 0 gamma i
      · exact eq_nat_smul_marks_of_nonneg_of_dominant_zero gamma hgamma hdom
      · push Not at hdom
        obtain ⟨i, hi⟩ := hdom
        have href : a (simpleReflection 0 i gamma) ≠ 0 := by rwa [hinvariant]
        have hgn := hnonneg _ href
        have hdeg0 : 0 ≤ totalDegree gamma := Finset.sum_nonneg (fun j _ => hgamma j)
        have hdegr0 : 0 ≤ totalDegree (simpleReflection 0 i gamma) :=
          Finset.sum_nonneg (fun j _ => hgn j)
        have hlt : totalDegree (simpleReflection 0 i gamma) < totalDegree gamma := by
          rw [totalDegree_simpleReflection]
          omega
        obtain ⟨m, hm⟩ := ih (totalDegree (simpleReflection 0 i gamma)).toNat
          (by omega) (simpleReflection 0 i gamma) rfl href
        refine ⟨m, ?_⟩
        have hh := congrArg (simpleReflection 0 i) hm
        simpa only [simpleReflection_twice, simpleReflection_zero_smul_marks] using hh
  exact heq (totalDegree beta).toNat beta rfl ha

theorem invariant_eq_zero_of_not_nat_smul_marks (a : RootCoefficients → K)
    (hsupport : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → a beta = 0)
    (hinvariant : ∀ i beta, a (simpleReflection 0 i beta) = a beta)
    (beta : RootCoefficients) (hbeta : ¬ ∃ n : ℕ, beta = (n : ℤ) • marks) : a beta = 0 := by
  by_contra ha
  exact hbeta (invariant_nonzero_eq_nat_smul_marks a hsupport hinvariant beta ha)

/-- Null-root coefficients determine an invariant cone-supported function. -/
theorem invariant_eq_of_nat_smul_marks (a b : RootCoefficients → K)
    (hsupportA : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → a beta = 0)
    (hsupportB : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → b beta = 0)
    (hinvariantA : ∀ i beta, a (simpleReflection 0 i beta) = a beta)
    (hinvariantB : ∀ i beta, b (simpleReflection 0 i beta) = b beta)
    (hnull : ∀ n : ℕ, a ((n : ℤ) • marks) = b ((n : ℤ) • marks)) : a = b := by
  classical
  funext beta
  by_cases hb : ∃ n : ℕ, beta = (n : ℤ) • marks
  · obtain ⟨n, rfl⟩ := hb
    exact hnull n
  · rw [invariant_eq_zero_of_not_nat_smul_marks a hsupportA hinvariantA beta hb,
      invariant_eq_zero_of_not_nat_smul_marks b hsupportB hinvariantB beta hb]

end KanadeRussell.Representation.AffineWeightLattice
