import KanadeRussell.Representation.ConcreteRootNumeratorRigidity
import KanadeRussell.Representation.LevelNineNumeratorMasks
import KanadeRussell.Representation.RootPrincipalSpecialization

/-! Identification of the three actual root numerators with explicit signed
level-nine shell coefficients. This identifies the theta coefficients; no
rank-two theta/product evaluation is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open AffineWeightLattice Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

/-- Rigidity identifies an actual tensor numerator once its shifted labels are
one of the three explicit level-nine cases. -/
theorem tensorPrincipalModule_rootNumerator_eq_mask
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val+d • p.val)
    (k : Fin 3) (hlabels : (fun i => M.highestWeightLabels i+1)=LevelNineNumeratorMasks.labels k) :
    rootCoefficient (M.rootCharacter*principalRootEulerDenominator) =
      fun beta => (LevelNineNumeratorMasks.candidate k beta : K) := by
  apply tensorPrincipalModule_rootNumerator_eq_of_conditions w hw seed M haction d hD
  · intro beta hnot
    have hz : LevelNineNumeratorMasks.candidate k beta=0 := by
      by_contra hn
      exact hnot (LevelNineNumeratorMasks.candidate_support k beta hn)
    simp [hz]
  · simp only [LevelNineNumeratorMasks.candidate_zero, Int.cast_one]
  · intro i beta
    rw [hlabels]
    simpa using congrArg (Int.castRingHom K)
      (LevelNineNumeratorMasks.candidate_reflection k i beta)
  · intro beta
    rw [hlabels]
    simpa using congrArg (Int.castRingHom K)
      (LevelNineNumeratorMasks.candidate_casimir k beta)

theorem skewPrincipalModule_shifted_labels (w : K) (hw : w^4-w^2+1=0) :
    (fun i => (skewPrincipalModule w hw).highestWeightLabels i+1)=LevelNineNumeratorMasks.labels 0 := by
  ext i
  change ((if i=2 then 0 else 1 : ℕ) : ℤ)+1=LevelNineNumeratorMasks.labels 0 i
  fin_cases i <;> decide

theorem vacuumPrincipalModule_shifted_labels (w : K) (hw : w^4-w^2+1=0) :
    (fun i => (vacuumPrincipalModule w hw).highestWeightLabels i+1)=LevelNineNumeratorMasks.labels 1 := by
  ext i
  change ((if i=0 then 3 else 0 : ℕ) : ℤ)+1=LevelNineNumeratorMasks.labels 1 i
  fin_cases i <;> decide

theorem alternatingPrincipalModule_shifted_labels (w : K) (hw : w^4-w^2+1=0) :
    (fun i => (alternatingPrincipalModule w hw).highestWeightLabels i+1)=LevelNineNumeratorMasks.labels 2 := by
  ext i
  change ((if i=2 then 1 else 0 : ℕ) : ℤ)+1=LevelNineNumeratorMasks.labels 2 i
  fin_cases i <;> decide

theorem skewPrincipalModule_rootNumerator_eq_mask (w : K) (hw : w^4-w^2+1=0) :
    rootCoefficient ((skewPrincipalModule w hw).rootCharacter*principalRootEulerDenominator) =
      fun beta => (LevelNineNumeratorMasks.candidate 0 beta : K) :=
  tensorPrincipalModule_rootNumerator_eq_mask w hw KanadeRussell.Sectors.skewSeed
    (skewPrincipalModule w hw) rfl 1
    (by simpa only [one_smul] using skewPrincipalModule_principalDerivation_val w hw)
    0 (skewPrincipalModule_shifted_labels w hw)

theorem vacuumPrincipalModule_rootNumerator_eq_mask (w : K) (hw : w^4-w^2+1=0) :
    rootCoefficient ((vacuumPrincipalModule w hw).rootCharacter*principalRootEulerDenominator) =
      fun beta => (LevelNineNumeratorMasks.candidate 1 beta : K) :=
  tensorPrincipalModule_rootNumerator_eq_mask w hw 1 (vacuumPrincipalModule w hw) rfl 0
    (by simpa only [zero_smul, add_zero] using vacuumPrincipalModule_principalDerivation_val w hw)
    1 (vacuumPrincipalModule_shifted_labels w hw)

theorem alternatingPrincipalModule_rootNumerator_eq_mask (w : K) (hw : w^4-w^2+1=0) :
    rootCoefficient ((alternatingPrincipalModule w hw).rootCharacter*principalRootEulerDenominator) =
      fun beta => (LevelNineNumeratorMasks.candidate 2 beta : K) :=
  tensorPrincipalModule_rootNumerator_eq_mask w hw alternatingSeed (alternatingPrincipalModule w hw) rfl 3
    (alternatingPrincipalModule_principalDerivation_val w hw)
    2 (alternatingPrincipalModule_shifted_labels w hw)

omit [CharZero K] in
private theorem coeff_specialization_mask (f : MvPowerSeries (Fin 3) K) (k : Fin 3)
    (h : rootCoefficient f = fun beta => (LevelNineNumeratorMasks.candidate k beta : K)) (n : ℕ) :
    PowerSeries.coeff n (rootPrincipalSpecialization f) =
      ∑ b : PrincipalDegreeOccupation n, (LevelNineNumeratorMasks.candidate k b.root : K) := by
  rw [coeff_rootPrincipalSpecialization]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← rootCoefficient_ofExponent, h, b.exponent_root]

theorem skewPrincipalModule_principalNumerator_coeff (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    PowerSeries.coeff n (rootPrincipalSpecialization
      ((skewPrincipalModule w hw).rootCharacter*principalRootEulerDenominator)) =
      ∑ b : PrincipalDegreeOccupation n, (LevelNineNumeratorMasks.candidate 0 b.root : K) :=
  coeff_specialization_mask _ 0 (skewPrincipalModule_rootNumerator_eq_mask w hw) n

theorem vacuumPrincipalModule_principalNumerator_coeff (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    PowerSeries.coeff n (rootPrincipalSpecialization
      ((vacuumPrincipalModule w hw).rootCharacter*principalRootEulerDenominator)) =
      ∑ b : PrincipalDegreeOccupation n, (LevelNineNumeratorMasks.candidate 1 b.root : K) :=
  coeff_specialization_mask _ 1 (vacuumPrincipalModule_rootNumerator_eq_mask w hw) n

theorem alternatingPrincipalModule_principalNumerator_coeff (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    PowerSeries.coeff n (rootPrincipalSpecialization
      ((alternatingPrincipalModule w hw).rootCharacter*principalRootEulerDenominator)) =
      ∑ b : PrincipalDegreeOccupation n, (LevelNineNumeratorMasks.candidate 2 b.root : K) :=
  coeff_specialization_mask _ 2 (alternatingPrincipalModule_rootNumerator_eq_mask w hw) n

end KanadeRussell.Representation
