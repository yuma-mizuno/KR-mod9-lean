import KanadeRussell.Representation.WeylWeightReflection
import KanadeRussell.Representation.DominantCasimirRigidity

/-! Conditional uniqueness of shifted antisymmetric Casimir-zero coefficients.
This is a root-lattice uniqueness theorem, with no denominator identity assumed
or proved and no identification of a particular character. -/
set_option autoImplicit false
namespace KanadeRussell.Representation.AffineWeightLattice
variable {K : Type*} [Field K] [CharZero K]

/-- Cone support, shifted antisymmetry and the Casimir equation determine an
alternant from its constant coefficient. -/
theorem rootAlternant_unique (lambda : RootCoefficients)
    (hlambda : ∀ i, 0 ≤ lambda i) (a b : RootCoefficients → K)
    (hsupportA : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → a beta = 0)
    (hsupportB : ∀ beta, ¬ (∀ i, 0 ≤ beta i) → b beta = 0)
    (hzero : a 0 = b 0)
    (hantiA : ∀ i beta, a (simpleReflection (fun j => lambda j+1) i beta) = -a beta)
    (hantiB : ∀ i beta, b (simpleReflection (fun j => lambda j+1) i beta) = -b beta)
    (hcasA : ∀ beta, (casimir (fun i => lambda i+1) beta : K) * a beta = 0)
    (hcasB : ∀ beta, (casimir (fun i => lambda i+1) beta : K) * b beta = 0) :
    a = b := by
  classical
  have hnonneg (beta : RootCoefficients) (hb : ∀ i, 0 ≤ beta i) : 0 ≤ totalDegree beta :=
    Finset.sum_nonneg (fun i _ => hb i)
  have heq : ∀ n : ℕ, ∀ beta : RootCoefficients, (totalDegree beta).toNat=n → a beta=b beta := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro beta hdegree
      by_cases hb : ∀ i, 0 ≤ beta i
      swap
      · rw [hsupportA beta hb, hsupportB beta hb]
      by_cases hz : beta=0
      · subst beta; exact hzero
      have hd := hnonneg beta hb
      have hlower (delta : RootCoefficients) (hlt : totalDegree delta < totalDegree beta) :
          a delta=b delta := by
        by_cases hdelta : ∀ i, 0 ≤ delta i
        · have hd0 := hnonneg delta hdelta
          exact ih (totalDegree delta).toNat (by omega) delta rfl
        · rw [hsupportA delta hdelta, hsupportB delta hdelta]
      by_cases hc : casimir (fun i => lambda i+1) beta = 0
      swap
      · have hcK : (casimir (fun i => lambda i+1) beta : K) ≠ 0 := by exact_mod_cast hc
        rw [(mul_eq_zero.mp (hcasA beta)).resolve_left hcK,
          (mul_eq_zero.mp (hcasB beta)).resolve_left hcK]
      by_cases hdom : ∀ i, 0 ≤ weightLabels lambda beta i
      · have hneg := casimir_rho_neg_of_dominant lambda beta hlambda hb hdom hz
        omega
      push Not at hdom
      obtain ⟨i, hi⟩ := hdom
      have hshift : weightLabels (fun j => lambda j+1) beta i = weightLabels lambda beta i+1 := by
        simp only [weightLabels]
        ring
      have hle : weightLabels (fun j => lambda j+1) beta i ≤ 0 := by omega
      by_cases hfixlabel : weightLabels (fun j => lambda j+1) beta i = 0
      · have hfix : simpleReflection (fun j => lambda j+1) i beta = beta := by
          simp [simpleReflection, hfixlabel]
        have ha := hantiA i beta
        have hb' := hantiB i beta
        rw [hfix] at ha hb'
        rw [CharZero.eq_neg_self_iff.mp ha, CharZero.eq_neg_self_iff.mp hb']
      · have hlt : totalDegree (simpleReflection (fun j => lambda j+1) i beta) < totalDegree beta := by
          rw [totalDegree_simpleReflection]
          omega
        have hh := hlower _ hlt
        rw [hantiA, hantiB] at hh
        exact neg_injective hh
  funext beta
  exact heq (totalDegree beta).toNat beta rfl

end KanadeRussell.Representation.AffineWeightLattice
