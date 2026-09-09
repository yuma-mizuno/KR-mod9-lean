import KanadeRussell.Representation.PrincipalRootSeriesData
import KanadeRussell.Representation.RootMultiplicitySeries
import KanadeRussell.Representation.ConcreteRootMultiplicityRecurrence

/-! The actual finite multiplicity recurrence as a multivariate coefficient equation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

private theorem rootCoefficientsOfExponent_sub (e f : Fin 3 →₀ ℕ) (h : f ≤ e) :
    rootCoefficientsOfExponent (e-f) = rootCoefficientsOfExponent e-rootCoefficientsOfExponent f := by
  ext i
  simp only [rootCoefficientsOfExponent, Finsupp.tsub_apply, Pi.sub_apply]
  exact Nat.cast_sub (h i)

/-- Monomial shifts of the weighted actual character include the vanishing
outside the positive cone, so no truncation hypothesis is needed. -/
theorem coeff_monomial_mul_rootWeightLabelCharacter
    (M : PrincipalHighestWeightModule K V) (lambda : RootCoefficients) (i : Fin 3)
    (e f : Fin 3 →₀ ℕ) (a : K) :
    MvPowerSeries.coeff e (MvPowerSeries.monomial f a * (rootWeightLabelOperator lambda i M.rootCharacter)) =
      a * (weightLabels lambda (rootCoefficientsOfExponent e-rootCoefficientsOfExponent f) i : K) *
        M.rootMultiplicity (rootCoefficientsOfExponent e-rootCoefficientsOfExponent f) := by
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases h : f ≤ e
  · rw [if_pos h, coeff_rootWeightLabelOperator, M.coeff_rootCharacter,
      rootCoefficientsOfExponent_sub e f h]
    ring
  · rw [if_neg h]
    have hn : ¬ (∀ j, 0 ≤ (rootCoefficientsOfExponent e-rootCoefficientsOfExponent f) j) := by
      intro hh
      apply h
      intro j
      have hj := hh j
      simp only [Pi.sub_apply, rootCoefficientsOfExponent] at hj
      omega
    rw [M.rootMultiplicity_eq_zero_of_not_nonneg _ hn, mul_zero]

omit [CharZero K] in
private theorem coeff_mul_eq_of_coeff_eq_le
    (f g h : MvPowerSeries (Fin 3) K) (e : Fin 3 →₀ ℕ)
    (he : ∀ d, d ≤ e → MvPowerSeries.coeff d f = MvPowerSeries.coeff d g) :
    MvPowerSeries.coeff e (f*h) = MvPowerSeries.coeff e (g*h) := by
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [he p.1 (by rw [← Finset.mem_antidiagonal.mp hp]; exact le_add_right le_rfl)]

private noncomputable def finiteRootLambert (N : ℕ) (i : Fin 3) : MvPowerSeries (Fin 3) K :=
  ∑ n ∈ Finset.range N, ∑ r : Fin 3, ∑ k ∈ Finset.range (N+1),
    if principalWeightSlotActive (positiveModeResidue n) r then
      MvPowerSeries.monomial ((k+1) • positiveModeExponent n r) (positiveModeOccupation n r i : K)
    else 0

omit [CharZero K] in
private theorem coeff_finiteRootLambert (N : ℕ) (i : Fin 3) (e : Fin 3 →₀ ℕ)
    (he : rootExponentDegree e ≤ N) :
    MvPowerSeries.coeff e (finiteRootLambert (K := K) N i) =
      MvPowerSeries.coeff e (principalRootLambert i) := by
  rw [coeff_principalRootLambert_cutoff i e N he]
  simp only [finiteRootLambert, map_sum, apply_ite, map_zero, MvPowerSeries.coeff_monomial]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : e = (k+1) • positiveModeExponent n r
  · simp [h]
  · simp [h, Ne.symm h]

/-- The Lambert convolution is precisely the finite set of shifts in the actual recurrence. -/
theorem coeff_principalRootLambert_mul_rootWeightLabelCharacter
    (M : PrincipalHighestWeightModule K V) (lambda : RootCoefficients)
    (i : Fin 3) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (principalRootLambert i * rootWeightLabelOperator lambda i M.rootCharacter) =
      ∑ n ∈ Finset.range (rootExponentDegree e), ∑ r : Fin 3,
        ∑ k ∈ Finset.range (rootExponentDegree e+1),
          if principalWeightSlotActive (positiveModeResidue n) r then
            (positiveModeOccupation n r i : K) *
              (weightLabels lambda (rootCoefficientsOfExponent e-((k+1:ℕ):ℤ) • positiveModeOccupation n r) i : K) *
                M.rootMultiplicity (rootCoefficientsOfExponent e-((k+1:ℕ):ℤ) • positiveModeOccupation n r)
          else 0 := by
  rw [coeff_mul_eq_of_coeff_eq_le (principalRootLambert i) (finiteRootLambert (rootExponentDegree e) i)
    _ e (fun d hd => (coeff_finiteRootLambert _ i d (rootExponentDegree_mono hd)).symm)]
  simp only [finiteRootLambert, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro k hk
  by_cases ha : principalWeightSlotActive (positiveModeResidue n) r
  · rw [if_pos ha, if_pos ha, coeff_monomial_mul_rootWeightLabelCharacter,
      rootCoefficientsOfExponent_nsmul, rootCoefficientsOfExponent_positiveModeExponent]
  · simp [ha]

/-- The proved actual multiplicity recurrence is a multivariate series equation. -/
theorem tensorPrincipalModule_rootCharacter_equation
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val) :
    rootCasimirOperator (fun i => M.highestWeightLabels i+1) M.rootCharacter =
      -(∑ i : Fin 3, (symmetrizer i : K) •
        (principalRootLambert i * rootWeightLabelOperator M.highestWeightLabels i M.rootCharacter)) := by
  ext e
  have hrec := tensorPrincipalModule_rootMultiplicity_recurrence w hw seed M haction d hD
    (rootCoefficientsOfExponent e)
  rw [rootMultiplicityKernel_sum_mul] at hrec
  have hd : (totalDegree (rootCoefficientsOfExponent e)).toNat = rootExponentDegree e := by
    rw [← rootExponentDegree_cast]
    simp
  simp only [hd] at hrec
  rw [coeff_rootCasimirOperator, M.coeff_rootCharacter]
  change (casimir (fun i => M.highestWeightLabels i+1) (rootCoefficientsOfExponent e) : K) *
    M.rootMultiplicity (rootCoefficientsOfExponent e) = _ at hrec
  rw [hrec]
  simp only [map_neg, map_sum, map_smul, smul_eq_mul,
    coeff_principalRootLambert_mul_rootWeightLabelCharacter, Finset.mul_sum]
  congr 1
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases ha : principalWeightSlotActive (positiveModeResidue n) r
  · simp only [principalRootBracketScalar, if_pos ha, Finset.sum_mul,
      PrincipalHighestWeightModule.rootMultiplicity]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp [principalRootBracketScalar, ha]

theorem skewPrincipalModule_rootCharacter_equation (w : K) (hw : w^4-w^2+1=0) :
    rootCasimirOperator (fun i => (skewPrincipalModule w hw).highestWeightLabels i+1) (skewPrincipalModule w hw).rootCharacter =
      -(∑ i : Fin 3, (symmetrizer i : K) •
        (principalRootLambert i * rootWeightLabelOperator (skewPrincipalModule w hw).highestWeightLabels i (skewPrincipalModule w hw).rootCharacter)) := by
  apply tensorPrincipalModule_rootCharacter_equation w hw Sectors.skewSeed (skewPrincipalModule w hw) rfl 1
  intro p
  simpa only [one_smul, zero_smul, add_zero] using skewPrincipalModule_principalDerivation_val w hw p

theorem vacuumPrincipalModule_rootCharacter_equation (w : K) (hw : w^4-w^2+1=0) :
    rootCasimirOperator (fun i => (vacuumPrincipalModule w hw).highestWeightLabels i+1) (vacuumPrincipalModule w hw).rootCharacter =
      -(∑ i : Fin 3, (symmetrizer i : K) •
        (principalRootLambert i * rootWeightLabelOperator (vacuumPrincipalModule w hw).highestWeightLabels i (vacuumPrincipalModule w hw).rootCharacter)) := by
  apply tensorPrincipalModule_rootCharacter_equation w hw 1 (vacuumPrincipalModule w hw) rfl 0
  intro p
  simpa only [one_smul, zero_smul, add_zero] using vacuumPrincipalModule_principalDerivation_val w hw p

theorem alternatingPrincipalModule_rootCharacter_equation (w : K) (hw : w^4-w^2+1=0) :
    rootCasimirOperator (fun i => (alternatingPrincipalModule w hw).highestWeightLabels i+1) (alternatingPrincipalModule w hw).rootCharacter =
      -(∑ i : Fin 3, (symmetrizer i : K) •
        (principalRootLambert i * rootWeightLabelOperator (alternatingPrincipalModule w hw).highestWeightLabels i (alternatingPrincipalModule w hw).rootCharacter)) := by
  apply tensorPrincipalModule_rootCharacter_equation w hw alternatingSeed (alternatingPrincipalModule w hw) rfl 3
  intro p
  simpa only [one_smul, zero_smul, add_zero] using alternatingPrincipalModule_principalDerivation_val w hw p

end KanadeRussell.Representation
