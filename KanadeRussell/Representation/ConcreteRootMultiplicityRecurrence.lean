import KanadeRussell.Representation.ConcreteCasimirModeTrace
import KanadeRussell.Representation.PrincipalRootRecurrenceData
import KanadeRussell.Representation.PrincipalModeUniformBracket

/-! Finite root-multiplicity recurrence from the actual mode Casimir. The
intermediate theorem states its diagonal commutator input explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice Sectors
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

private theorem mode_terminal_degree_neg (beta : RootCoefficients) (n : ℕ) (r : Fin 3) :
    totalDegree (beta-(((totalDegree beta).toNat+1:ℕ):ℤ) • positiveModeOccupation n r) < 0 := by
  have he (m : ℤ) : totalDegree (beta-m • positiveModeOccupation n r) =
      totalDegree beta-m*totalDegree (positiveModeOccupation n r) := by
    simp [totalDegree, Pi.sub_apply, Pi.smul_apply, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [he, positiveModeOccupation_degree]
  have h0 : 0 ≤ (n:ℤ) := Int.natCast_nonneg n
  have h1 : totalDegree beta < (((totalDegree beta).toNat+1:ℕ):ℤ) := by omega
  have h2 : 0 ≤ (((totalDegree beta).toNat+1:ℕ):ℤ) := Int.natCast_nonneg _
  nlinarith

theorem tensorPrincipalModule_rootMultiplicity_recurrence_of_scalar_brackets
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (c : RootCoefficients → ℕ → Fin 3 → K)
    (hcomm : ∀ n r alpha p, p ∈ M.rootGrade alpha →
      (positiveCyclicPrincipalMode w seed n r * negativeCyclicPrincipalMode w seed n r -
        negativeCyclicPrincipalMode w seed n r * positiveCyclicPrincipalMode w seed n r) p =
        c alpha n r • p)
    (beta : RootCoefficients) :
    (casimir (fun i => M.highestWeightLabels i+1) beta : K) *
      (Module.finrank K (M.rootGrade beta) : K) =
      -(∑ n ∈ Finset.range (totalDegree beta).toNat, ∑ r : Fin 3,
        ∑ k ∈ Finset.range ((totalDegree beta).toNat+1),
          c (beta-((k+1:ℕ):ℤ) • positiveModeOccupation n r) n r *
            (Module.finrank K (M.rootGrade (beta-((k+1:ℕ):ℤ) • positiveModeOccupation n r)) : K)) := by
  rw [tensorPrincipalModule_casimir_mul_finrank_eq_neg_modeSum w hw seed M haction d hD beta]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  exact M.rootModeTrace_eq_sum_of_terminal_degree_neg
    (positiveCyclicPrincipalMode w seed n r) (negativeCyclicPrincipalMode w seed n r)
    (positiveModeOccupation n r)
    (tensorPrincipalModule_positiveMode_mem_rootGrade w hw seed M haction d hD n r)
    (tensorPrincipalModule_negativeMode_mem_rootGrade w hw seed M haction d hD n r)
    (fun alpha => c alpha n r) (hcomm n r) beta ((totalDegree beta).toNat+1)
    (mode_terminal_degree_neg beta n r)

theorem tensorPrincipalModule_rootMode_scalar_bracket
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed)
    (n : ℕ) (r : Fin 3) (alpha : RootCoefficients)
    (p : tensorCyclicSpan w seed) (hp : p ∈ M.rootGrade alpha) :
    (positiveCyclicPrincipalMode w seed n r * negativeCyclicPrincipalMode w seed n r -
      negativeCyclicPrincipalMode w seed n r * positiveCyclicPrincipalMode w seed n r) p =
      principalRootBracketScalar (K := K) M.highestWeightLabels alpha n r • p := by
  have hH (j : Fin 3) : chevalleyH w j p.val =
      (weightLabels M.highestWeightLabels alpha j : K) • p.val := by
    have h := congrArg Subtype.val (M.rootGrade_H alpha p hp j)
    simpa only [haction, tensorCyclicChevalleyAction_H_val, Submodule.coe_smul] using h
  apply Subtype.ext
  change positivePrincipalMode w n r (negativePrincipalMode w n r p.val) -
    negativePrincipalMode w n r (positivePrincipalMode w n r p.val) =
      principalRootBracketScalar (K := K) M.highestWeightLabels alpha n r • p.val
  have h := congrArg (fun f : Module.End K (Space K) => f p.val)
    (positive_negativePrincipalMode_bracket w hw n r)
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [h]
  by_cases hr : principalWeightSlotActive (positiveModeResidue n) r
  · simp only [if_pos hr, principalRootBracketScalar, LinearMap.sum_apply,
      LinearMap.smul_apply, hH, smul_smul, Finset.sum_smul]
  · simp [hr, principalRootBracketScalar]

/-- The actual finite root-multiplicity recurrence with its explicit common kernel. -/
theorem tensorPrincipalModule_rootMultiplicity_recurrence
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (beta : RootCoefficients) :
    (casimir (fun i => M.highestWeightLabels i+1) beta : K) *
      (Module.finrank K (M.rootGrade beta) : K) =
      ∑ delta ∈ (rootMultiplicityKernel (K := K) M.highestWeightLabels beta).support,
        rootMultiplicityKernel M.highestWeightLabels beta delta *
          (Module.finrank K (M.rootGrade delta) : K) := by
  rw [rootMultiplicityKernel_sum_mul]
  exact tensorPrincipalModule_rootMultiplicity_recurrence_of_scalar_brackets
    w hw seed M haction d hD (principalRootBracketScalar (K := K) M.highestWeightLabels)
    (tensorPrincipalModule_rootMode_scalar_bracket w hw seed M haction) beta

theorem skewPrincipalModule_rootMultiplicity_recurrence
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients) :
    (casimir (fun i => (skewPrincipalModule w hw).highestWeightLabels i+1) beta : K) *
      (Module.finrank K ((skewPrincipalModule w hw).rootGrade beta) : K) =
      ∑ delta ∈ (rootMultiplicityKernel (K := K) (skewPrincipalModule w hw).highestWeightLabels beta).support,
        rootMultiplicityKernel (skewPrincipalModule w hw).highestWeightLabels beta delta *
          (Module.finrank K ((skewPrincipalModule w hw).rootGrade delta) : K) := by
  apply tensorPrincipalModule_rootMultiplicity_recurrence w hw skewSeed
    (skewPrincipalModule w hw) rfl 1 ?_ beta
  intro p
  simpa only [one_smul, zero_smul, add_zero] using skewPrincipalModule_principalDerivation_val w hw p
theorem vacuumPrincipalModule_rootMultiplicity_recurrence
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients) :
    (casimir (fun i => (vacuumPrincipalModule w hw).highestWeightLabels i+1) beta : K) *
      (Module.finrank K ((vacuumPrincipalModule w hw).rootGrade beta) : K) =
      ∑ delta ∈ (rootMultiplicityKernel (K := K) (vacuumPrincipalModule w hw).highestWeightLabels beta).support,
        rootMultiplicityKernel (vacuumPrincipalModule w hw).highestWeightLabels beta delta *
          (Module.finrank K ((vacuumPrincipalModule w hw).rootGrade delta) : K) := by
  apply tensorPrincipalModule_rootMultiplicity_recurrence w hw 1
    (vacuumPrincipalModule w hw) rfl 0 ?_ beta
  intro p
  simpa only [one_smul, zero_smul, add_zero] using vacuumPrincipalModule_principalDerivation_val w hw p
theorem alternatingPrincipalModule_rootMultiplicity_recurrence
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients) :
    (casimir (fun i => (alternatingPrincipalModule w hw).highestWeightLabels i+1) beta : K) *
      (Module.finrank K ((alternatingPrincipalModule w hw).rootGrade beta) : K) =
      ∑ delta ∈ (rootMultiplicityKernel (K := K) (alternatingPrincipalModule w hw).highestWeightLabels beta).support,
        rootMultiplicityKernel (alternatingPrincipalModule w hw).highestWeightLabels beta delta *
          (Module.finrank K ((alternatingPrincipalModule w hw).rootGrade delta) : K) := by
  apply tensorPrincipalModule_rootMultiplicity_recurrence w hw alternatingSeed
    (alternatingPrincipalModule w hw) rfl 3 ?_ beta
  intro p
  simpa only [one_smul, zero_smul, add_zero] using alternatingPrincipalModule_principalDerivation_val w hw p

end KanadeRussell.Representation
