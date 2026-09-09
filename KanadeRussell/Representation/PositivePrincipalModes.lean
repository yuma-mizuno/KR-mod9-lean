import KanadeRussell.Representation.PrincipalModeWeights
import KanadeRussell.Representation.PrincipalModeRootGrade

/-! The finite Cartan-eigenvector certificates apply in every positive degree.
The zero coordinate used in inactive residues remains a zero operator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

def positiveModeResidue (n : ℕ) : Fin 12 := ⟨n % 12, Nat.mod_lt n (by decide)⟩

def positiveModeOccupation (n : ℕ) (r : Fin 3) : RootCoefficients := fun i =>
  (principalWeightOccupation (positiveModeResidue n) r i : ℤ) +
    (n / 12 : ℕ) * (![3, 6, 3] : Fin 3 → ℤ) i

theorem positiveModeOccupation_degree (n : ℕ) (r : Fin 3) :
    totalDegree (positiveModeOccupation n r) = (n : ℤ)+1 := by
  have h := principalWeightOccupation_degree (positiveModeResidue n) r
  have hcast : (∑ i : Fin 3, (principalWeightOccupation (positiveModeResidue n) r i : ℤ)) =
      (n % 12 : ℕ) + 1 := by exact_mod_cast h
  simp only [positiveModeOccupation, totalDegree, Finset.sum_add_distrib,
    ← Finset.mul_sum, Fin.sum_univ_three] at hcast ⊢
  norm_num [Matrix.cons_val_two] at hcast ⊢
  omega

theorem positiveModeOccupation_nonneg (n : ℕ) (r i : Fin 3) :
    0 ≤ positiveModeOccupation n r i := by
  apply add_nonneg (Int.natCast_nonneg _)
  apply mul_nonneg (Int.natCast_nonneg _)
  fin_cases i <;> norm_num

theorem positiveModeOccupation_cartan (n : ℕ) (r i : Fin 3) :
    (∑ j : Fin 3, (affineCartanMatrix i j : K) * (positiveModeOccupation n r j : K)) =
      ∑ j : Fin 3, (affineCartanMatrix i j : K) *
        (principalWeightOccupation (positiveModeResidue n) r j : K) := by
  fin_cases i <;>
    simp [positiveModeOccupation, affineCartanMatrix, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_succ] <;> ring

theorem positiveModeResidue_congr (n : ℕ) :
    ((n : ℤ)+1) % 12 = ((positiveModeResidue n).val+1 : ℤ) % 12 := by
  simp only [positiveModeResidue]
  omega

theorem positiveModeCoordinates_eigen (w : K) (hw : w^4-w^2+1=0)
    (n : ℕ) (r i : Fin 3) :
    (principalCartanMatrix w ((n : ℤ)+1) i).mulVec
        (principalWeightCoordinates w (positiveModeResidue n) r) =
      (∑ j : Fin 3, (affineCartanMatrix i j : K) * (positiveModeOccupation n r j : K)) •
        principalWeightCoordinates w (positiveModeResidue n) r := by
  rw [principalCartanMatrix_eq_of_mod w hw _ _ (positiveModeResidue_congr n),
    positiveModeOccupation_cartan]
  exact principalWeightCoordinates_eigen w hw (positiveModeResidue n) r i

noncomputable def positivePrincipalMode (w : K) (n : ℕ) (r : Fin 3) :
    Module.End K (Space K) :=
  principalModeCombination w ((n : ℤ)+1) (principalWeightCoordinates w (positiveModeResidue n) r)

theorem positivePrincipalMode_H (w : K) (hw : w^4-w^2+1=0)
    (n : ℕ) (r i : Fin 3) :
    ⁅chevalleyH w i, positivePrincipalMode w n r⁆ =
      (∑ j : Fin 3, (affineCartanMatrix i j : K) * (positiveModeOccupation n r j : K)) •
        positivePrincipalMode w n r :=
  principalModeCombination_eigenoperator w hw _ (by omega) i _ _
    (positiveModeCoordinates_eigen w hw n r i)

theorem positivePrincipalMode_D (w : K) (n : ℕ) (r : Fin 3) :
    ⁅Fock.principalDerivation (K := K), positivePrincipalMode w n r⁆ =
      ((n : K)+1) • positivePrincipalMode w n r := by
  simpa only [positivePrincipalMode, Int.cast_add, Int.cast_natCast, Int.cast_one] using
    principalDerivation_lie_principalModeCombination w ((n : ℤ)+1)
      (principalWeightCoordinates w (positiveModeResidue n) r)

theorem principalModeCombination_eq_sum_positivePrincipalMode
    (w : K) (hw : w^4-w^2+1=0) (n : ℕ) (v : Fin 3 → K) :
    principalModeCombination w ((n : ℤ)+1) v =
      ∑ r, ((principalWeightReconstruction w (positiveModeResidue n)).mulVec v) r •
        positivePrincipalMode w n r := by
  have h := congrArg (principalModeCombination w ((n : ℤ)+1))
    (principalWeightCoordinates_reconstruct w hw (positiveModeResidue n) v)
  simp only [map_sum, map_smul] at h
  change principalModeCombination w ((n : ℤ)+1) v =
    ∑ r, ((principalWeightReconstruction w (positiveModeResidue n)).mulVec v) r •
      principalModeCombination w ((n : ℤ)+1)
        (principalWeightCoordinates w (positiveModeResidue n) r)
  rw [h]
  have habs : (((positiveModeResidue n).val : ℤ)+1).natAbs =
      (positiveModeResidue n).val+1 := by omega
  by_cases hn : IsMode ((n : ℤ)+1).natAbs
  · have hr : IsMode ((positiveModeResidue n).val+1) := by
      have he : IsMode ((n : ℤ)+1).natAbs =
          IsMode (((positiveModeResidue n).val+1 : ℤ)).natAbs := by
        apply propext
        rw [isMode_natAbs_iff_residue, isMode_natAbs_iff_residue,
          positiveModeResidue_congr]
      simpa only [habs] using he.mp hn
    simp only [if_pos hr]
    congr 1
    ext i
    fin_cases i <;> rfl
  · have hr : ¬ IsMode ((positiveModeResidue n).val+1) := by
      intro hr
      apply hn
      rw [isMode_natAbs_iff_residue, positiveModeResidue_congr]
      exact (isMode_natAbs_iff_residue _).mp (by simpa only [habs] using hr)
    simp only [if_neg hr]
    exact principalModeCombination_eq_of_inactive w _ hn v

noncomputable def positiveCyclicPrincipalMode (w : K) (seed : Space K) (n : ℕ) (r : Fin 3) :
    Module.End K (tensorCyclicSpan w seed) :=
  tensorCyclicPrincipalModeCombination w seed ((n : ℤ)+1)
    (principalWeightCoordinates w (positiveModeResidue n) r)

theorem tensorPrincipalModule_positiveMode_mem_rootGrade (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (n : ℕ) (r : Fin 3) (beta : RootCoefficients)
    (p : tensorCyclicSpan w seed) (hp : p ∈ M.rootGrade beta) :
    positiveCyclicPrincipalMode w seed n r p ∈ M.rootGrade (beta-positiveModeOccupation n r) := by
  have he (i : Fin 3) := positiveModeCoordinates_eigen w hw n r i
  have h := tensorPrincipalModule_modeCombination_mem_rootGrade w hw seed M haction d hD
    (positiveModeOccupation n r) (by rw [positiveModeOccupation_degree]; omega)
    (principalWeightCoordinates w (positiveModeResidue n) r)
    (by intro i; rw [positiveModeOccupation_degree]; exact he i) beta p hp
  simpa only [positiveCyclicPrincipalMode, positiveModeOccupation_degree] using h

theorem skewPrincipalModule_positiveMode_mem_rootGrade (w : K) (hw : w^4-w^2+1=0)
    (n : ℕ) (r : Fin 3) (beta : RootCoefficients)
    (p : tensorCyclicSpan w (Sectors.skewSeed : Space K))
    (hp : p ∈ (skewPrincipalModule w hw).rootGrade beta) :
    positiveCyclicPrincipalMode w Sectors.skewSeed n r p ∈
      (skewPrincipalModule w hw).rootGrade (beta-positiveModeOccupation n r) := by
  apply tensorPrincipalModule_positiveMode_mem_rootGrade w hw Sectors.skewSeed
    (skewPrincipalModule w hw) rfl 1 ?_ n r beta p hp
  intro p
  simpa only [one_smul] using skewPrincipalModule_principalDerivation_val w hw p

theorem vacuumPrincipalModule_positiveMode_mem_rootGrade (w : K) (hw : w^4-w^2+1=0)
    (n : ℕ) (r : Fin 3) (beta : RootCoefficients)
    (p : tensorCyclicSpan w (1 : Space K))
    (hp : p ∈ (vacuumPrincipalModule w hw).rootGrade beta) :
    positiveCyclicPrincipalMode w 1 n r p ∈
      (vacuumPrincipalModule w hw).rootGrade (beta-positiveModeOccupation n r) := by
  apply tensorPrincipalModule_positiveMode_mem_rootGrade w hw 1
    (vacuumPrincipalModule w hw) rfl 0 ?_ n r beta p hp
  intro p
  simpa only [zero_smul, add_zero] using vacuumPrincipalModule_principalDerivation_val w hw p

theorem alternatingPrincipalModule_positiveMode_mem_rootGrade (w : K) (hw : w^4-w^2+1=0)
    (n : ℕ) (r : Fin 3) (beta : RootCoefficients)
    (p : tensorCyclicSpan w (alternatingSeed : Space K))
    (hp : p ∈ (alternatingPrincipalModule w hw).rootGrade beta) :
    positiveCyclicPrincipalMode w alternatingSeed n r p ∈
      (alternatingPrincipalModule w hw).rootGrade (beta-positiveModeOccupation n r) := by
  apply tensorPrincipalModule_positiveMode_mem_rootGrade w hw alternatingSeed
    (alternatingPrincipalModule w hw) rfl 3
    (alternatingPrincipalModule_principalDerivation_val w hw) n r beta p hp

end KanadeRussell.Representation
