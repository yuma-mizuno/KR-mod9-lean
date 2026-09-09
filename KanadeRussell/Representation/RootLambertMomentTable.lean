import KanadeRussell.Representation.PrincipalRootSeriesData

/-! Exact twelve-period root moments. Null-root translates disappear from
the two finite-root projections and their quadratic norm; active slots,
including the two equal imaginary-root occupations, are counted separately. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
open AffineWeightLattice

def principalRootMomentA : Fin 12 → ℤ := ![0,0,-1,-1,-1,0,1,1,1,0,0,0]
def principalRootMomentB : Fin 12 → ℤ := ![-1,0,-1,1,0,0,0,-1,1,0,1,0]
def principalRootMomentNorm : Fin 12 → ℤ := ![5,2,2,3,5,2,5,3,2,2,5,0]
def principalRootMomentCount : Fin 12 → ℤ := ![3,2,2,2,3,2,3,2,2,2,3,2]

theorem positiveModeOccupation_projectionA (n : ℕ) (r : Fin 3) :
    positiveModeOccupation n r 0-positiveModeOccupation n r 2 =
      (principalWeightOccupation (positiveModeResidue n) r 0 : ℤ)-
        (principalWeightOccupation (positiveModeResidue n) r 2 : ℤ) := by
  simp [positiveModeOccupation]

theorem positiveModeOccupation_projectionB (n : ℕ) (r : Fin 3) :
    positiveModeOccupation n r 1-2*positiveModeOccupation n r 2 =
      (principalWeightOccupation (positiveModeResidue n) r 1 : ℤ)-
        2*(principalWeightOccupation (positiveModeResidue n) r 2 : ℤ) := by
  norm_num [positiveModeOccupation, Matrix.cons_val_two]
  ring

theorem positiveModeOccupation_rootQuadratic (n : ℕ) (r : Fin 3) :
    rootQuadratic (positiveModeOccupation n r) =
      rootQuadratic (fun i => (principalWeightOccupation (positiveModeResidue n) r i : ℤ)) := by
  norm_num [rootQuadratic_eq, positiveModeOccupation, Matrix.cons_val_two]
  ring

theorem principalRootMomentA_eq (n : ℕ) :
    (∑ r : Fin 3, if principalWeightSlotActive (positiveModeResidue n) r then
      positiveModeOccupation n r 0-positiveModeOccupation n r 2 else 0) =
      principalRootMomentA (positiveModeResidue n) := by
  simp_rw [positiveModeOccupation_projectionA]
  exact (by decide : ∀ s : Fin 12,
    (∑ r : Fin 3, if principalWeightSlotActive s r then
      (principalWeightOccupation s r 0 : ℤ)-(principalWeightOccupation s r 2 : ℤ) else 0) =
      principalRootMomentA s) (positiveModeResidue n)

theorem principalRootMomentB_eq (n : ℕ) :
    (∑ r : Fin 3, if principalWeightSlotActive (positiveModeResidue n) r then
      positiveModeOccupation n r 1-2*positiveModeOccupation n r 2 else 0) =
      principalRootMomentB (positiveModeResidue n) := by
  simp_rw [positiveModeOccupation_projectionB]
  exact (by decide : ∀ s : Fin 12,
    (∑ r : Fin 3, if principalWeightSlotActive s r then
      (principalWeightOccupation s r 1 : ℤ)-2*(principalWeightOccupation s r 2 : ℤ) else 0) =
      principalRootMomentB s) (positiveModeResidue n)

theorem principalRootMomentNorm_eq (n : ℕ) :
    (∑ r : Fin 3, if principalWeightSlotActive (positiveModeResidue n) r then
      rootQuadratic (positiveModeOccupation n r) else 0) =
      principalRootMomentNorm (positiveModeResidue n) := by
  simp_rw [positiveModeOccupation_rootQuadratic]
  exact (by decide : ∀ s : Fin 12,
    (∑ r : Fin 3, if principalWeightSlotActive s r then
      rootQuadratic (fun i => (principalWeightOccupation s r i : ℤ)) else 0) =
      principalRootMomentNorm s) (positiveModeResidue n)

theorem principalRootMomentCount_eq (n : ℕ) :
    (∑ r : Fin 3, if principalWeightSlotActive (positiveModeResidue n) r then (1 : ℤ) else 0) =
      principalRootMomentCount (positiveModeResidue n) := by
  exact (by decide : ∀ s : Fin 12,
    (∑ r : Fin 3, if principalWeightSlotActive s r then (1 : ℤ) else 0) =
      principalRootMomentCount s) (positiveModeResidue n)

/-- The linear moment is determined by height, multiplicity, and the two projections. -/
theorem principalRootMomentLinear_eq (n : ℕ) :
    2*(∑ r : Fin 3, if principalWeightSlotActive (positiveModeResidue n) r then
      positiveModeOccupation n r 0+positiveModeOccupation n r 1+3*positiveModeOccupation n r 2
      else 0) =
      3*((n : ℤ)+1)*principalRootMomentCount (positiveModeResidue n)-
        principalRootMomentA (positiveModeResidue n)-principalRootMomentB (positiveModeResidue n) := by
  classical
  rw [← principalRootMomentCount_eq, ← principalRootMomentA_eq, ← principalRootMomentB_eq,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs
  · have hd := positiveModeOccupation_degree n r
    simp only [totalDegree, Fin.sum_univ_three] at hd
    linear_combination 3*hd
  · ring

end KanadeRussell.Representation
