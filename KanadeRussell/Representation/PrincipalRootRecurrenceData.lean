import KanadeRussell.Representation.NegativePrincipalModes
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Explicit finite scalar data for the principal-root multiplicity recurrence.
The kernel only refers to strictly smaller total degrees; no character or
operator bracket identity is assumed in its construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice
variable {K : Type*} [Field K]

noncomputable def principalRootBracketScalar (lambda alpha : RootCoefficients)
    (n : ℕ) (r : Fin 3) : K :=
  if principalWeightSlotActive (positiveModeResidue n) r then
    ∑ i : Fin 3, (symmetrizer i : K) * (positiveModeOccupation n r i : K) *
      (weightLabels lambda alpha i : K)
  else 0

theorem principalRoot_target_degree (beta : RootCoefficients) (n : ℕ) (r : Fin 3) (k : ℕ) :
    totalDegree (beta-((k+1 : ℕ) : ℤ) • positiveModeOccupation n r) =
      totalDegree beta - ((k+1 : ℕ) : ℤ) * ((n : ℤ)+1) := by
  simp only [totalDegree, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [show (∑ i : Fin 3, positiveModeOccupation n r i) = (n : ℤ)+1 from
    positiveModeOccupation_degree n r]

theorem principalRoot_target_degree_lt (beta : RootCoefficients) (n : ℕ) (r : Fin 3) (k : ℕ) :
    totalDegree (beta-((k+1 : ℕ) : ℤ) • positiveModeOccupation n r) < totalDegree beta := by
  rw [principalRoot_target_degree]
  have hpos : 0 < ((k+1 : ℕ) : ℤ) * ((n : ℤ)+1) := mul_pos (by omega) (by omega)
  omega

theorem principalRoot_terminal_degree_neg (beta : RootCoefficients) (n : ℕ) (r : Fin 3) :
    totalDegree (beta-(((totalDegree beta).toNat+1 : ℕ) : ℤ) •
      positiveModeOccupation n r) < 0 := by
  rw [principalRoot_target_degree]
  have hlarge : totalDegree beta < (((totalDegree beta).toNat+1 : ℕ) : ℤ) := by omega
  have hpos : 0 ≤ (((totalDegree beta).toNat+1 : ℕ) : ℤ) := by omega
  have hn : 1 ≤ (n : ℤ)+1 := by omega
  nlinarith

noncomputable def rootMultiplicityKernel (lambda beta : RootCoefficients) : RootCoefficients →₀ K :=
  - ∑ n ∈ Finset.range (totalDegree beta).toNat, ∑ r : Fin 3,
      ∑ k ∈ Finset.range ((totalDegree beta).toNat+1),
        Finsupp.single (beta-((k+1 : ℕ) : ℤ) • positiveModeOccupation n r)
          (principalRootBracketScalar lambda
            (beta-((k+1 : ℕ) : ℤ) • positiveModeOccupation n r) n r)

theorem rootMultiplicityKernel_support_degree_lt (lambda beta delta : RootCoefficients)
    (hdelta : delta ∈ (rootMultiplicityKernel (K := K) lambda beta).support) :
    totalDegree delta < totalDegree beta := by
  classical
  by_contra hdegree
  have hz : rootMultiplicityKernel (K := K) lambda beta delta = 0 := by
    simp only [rootMultiplicityKernel, Finsupp.neg_apply, Finsupp.finsetSum_apply]
    apply neg_eq_zero.mpr
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro k hk
    have hne : beta-((k+1 : ℕ) : ℤ) • positiveModeOccupation n r ≠ delta := by
      intro heq
      have hlt := principalRoot_target_degree_lt beta n r k
      rw [heq] at hlt
      exact hdegree hlt
    simp only [Finsupp.single_apply, if_neg hne]
  exact (Finsupp.mem_support_iff.mp hdelta) hz

theorem rootMultiplicityKernel_sum_mul (lambda beta : RootCoefficients) (m : RootCoefficients → K) :
    (∑ delta ∈ (rootMultiplicityKernel (K := K) lambda beta).support,
      rootMultiplicityKernel lambda beta delta * m delta) =
      - ∑ n ∈ Finset.range (totalDegree beta).toNat, ∑ r : Fin 3,
          ∑ k ∈ Finset.range ((totalDegree beta).toNat+1),
            principalRootBracketScalar lambda
              (beta-((k+1 : ℕ) : ℤ) • positiveModeOccupation n r) n r *
              m (beta-((k+1 : ℕ) : ℤ) • positiveModeOccupation n r) := by
  classical
  change Finsupp.linearCombination K m (rootMultiplicityKernel lambda beta) = _
  simp only [rootMultiplicityKernel, map_neg, map_sum, Finsupp.linearCombination_single,
    smul_eq_mul]

end KanadeRussell.Representation
