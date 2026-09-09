import KanadeRussell.Representation.WeylWeightReflection
import KanadeRussell.Representation.DominantCasimirRigidity
import Mathlib.Data.Finsupp.Basic

/-! Uniqueness from Weyl symmetry and a strictly lower-degree recurrence at
dominant weights. This theorem does not evaluate a character or assert that a
particular kernel supplies the recurrence. -/
set_option autoImplicit false
namespace KanadeRussell.Representation.AffineWeightLattice
variable {K : Type*} [Field K] [CharZero K]

/-- The value at zero, reflection symmetry, positive-cone support and a
lower-degree Casimir recurrence determine all root multiplicities uniquely. -/
theorem rootMultiplicity_unique
    (lambda : RootCoefficients) (hlambda : ∀ i, 0 ≤ lambda i)
    (R : RootCoefficients → RootCoefficients →₀ K)
    (hR : ∀ beta delta, delta ∈ (R beta).support → totalDegree delta < totalDegree beta)
    (m1 m2 : RootCoefficients → K)
    (hsupport1 : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → m1 beta=0)
    (hsupport2 : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → m2 beta=0)
    (hzero : m1 0=m2 0)
    (hweyl1 : ∀ i beta, m1 (simpleReflection lambda i beta)=m1 beta)
    (hweyl2 : ∀ i beta, m2 (simpleReflection lambda i beta)=m2 beta)
    (hrec1 : ∀ beta, beta ≠ 0 → (∀ i, 0 ≤ beta i) →
      (∀ i, 0 ≤ weightLabels lambda beta i) →
      (casimir (fun i => lambda i+1) beta : K)*m1 beta =
        ∑ delta ∈ (R beta).support, R beta delta*m1 delta)
    (hrec2 : ∀ beta, beta ≠ 0 → (∀ i, 0 ≤ beta i) →
      (∀ i, 0 ≤ weightLabels lambda beta i) →
      (casimir (fun i => lambda i+1) beta : K)*m2 beta =
        ∑ delta ∈ (R beta).support, R beta delta*m2 delta) : m1=m2 := by
  classical
  have hnonneg (beta : RootCoefficients) (hb : ∀ i, 0 ≤ beta i) : 0 ≤ totalDegree beta :=
    Finset.sum_nonneg (fun i _ => hb i)
  have heq : ∀ n : ℕ, ∀ beta : RootCoefficients, (totalDegree beta).toNat=n → m1 beta=m2 beta := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro beta hdegree
      by_cases hb : ∀ i, 0 ≤ beta i
      swap
      · rw [hsupport1 beta hb, hsupport2 beta hb]
      by_cases hz : beta=0
      · subst beta; exact hzero
      have hd := hnonneg beta hb
      have hlower (delta : RootCoefficients) (hlt : totalDegree delta < totalDegree beta) :
          m1 delta=m2 delta := by
        by_cases hdelta : ∀ i, 0 ≤ delta i
        · have hd0 := hnonneg delta hdelta
          exact ih (totalDegree delta).toNat (by omega) delta rfl
        · rw [hsupport1 delta hdelta, hsupport2 delta hdelta]
      by_cases hdom : ∀ i, 0 ≤ weightLabels lambda beta i
      · have hc : (casimir (fun i => lambda i+1) beta : K) ≠ 0 := by
          have hi : casimir (fun i => lambda i+1) beta ≠ 0 :=
            ne_of_lt (casimir_rho_neg_of_dominant lambda beta hlambda hb hdom hz)
          exact_mod_cast hi
        apply mul_left_cancel₀ hc
        rw [hrec1 beta hz hb hdom, hrec2 beta hz hb hdom]
        apply Finset.sum_congr rfl
        intro delta hdelta
        rw [hlower delta (hR beta delta hdelta)]
      · push_neg at hdom
        obtain ⟨i, hi⟩ := hdom
        rw [← hweyl1 i beta, ← hweyl2 i beta]
        apply hlower
        rw [totalDegree_simpleReflection]
        omega
  funext beta
  exact heq (totalDegree beta).toNat beta rfl

end KanadeRussell.Representation.AffineWeightLattice
