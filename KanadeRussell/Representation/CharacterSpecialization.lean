import KanadeRussell.Product.VacuumNumerator

/-! Concrete substitutions in the untwisted G2 affine denominator used by
Lepowsky's numerator formula. Root multiplicities and the general character
formula are external inputs; the specialization and product algebra are proved. -/
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Product

/-- Positive finite-root coordinates, with node 1 long and node 2 short.
This records the data supplied by the standard G2 root classification. -/
def dualPositiveRootCoordinates : List (ℕ × ℕ) :=
  [(1,0),(0,1),(1,1),(1,2),(1,3),(2,3)]

def dualRootHeights (s₁ s₂ : ℕ) : List ℕ :=
  dualPositiveRootCoordinates.map (fun ab => ab.1*s₁ + ab.2*s₂)

def dualImaginaryPeriod (s₀ s₁ s₂ : ℕ) : ℕ := s₀ + 2*s₁ + 3*s₂

noncomputable def progressionProduct (m r : ℕ) : PowerSeries ℤ := (q^r; q^m)_∞

noncomputable def dualAffineDenominator (s₀ s₁ s₂ : ℕ) : PowerSeries ℤ :=
  let m := dualImaginaryPeriod s₀ s₁ s₂
  (E m)^2 * ((dualRootHeights s₁ s₂).map
    (fun h => progressionProduct m h * progressionProduct m (m-h))).prod

/-- The actual principal Heisenberg mode set, expressed as an Euler product. -/
noncomputable def principalHeisenbergEuler : PowerSeries ℤ :=
  progressionProduct 12 1 * progressionProduct 12 5 *
    progressionProduct 12 7 * progressionProduct 12 11

theorem dualRootHeights_one : dualRootHeights 1 1 = [1,1,2,3,4,5] := rfl

theorem dualAffineDenominator_411 :
    dualAffineDenominator 4 1 1 = levelThreeVacuumNumerator := rfl

theorem progression_six_split (r : ℕ) :
    progressionProduct 6 r = progressionProduct 12 r * progressionProduct 12 (r+6) := by
  rw [progressionProduct,qPochhammerInf_eq_prod_range (by decide : 2 ≠ 0) (by simp [q])]
  norm_num only [Finset.prod_range_succ,Finset.prod_range_zero,pow_zero,mul_one,one_mul,
    pow_one,← pow_mul,← pow_add,Nat.reduceMul]
  rfl

theorem principalHeisenbergEuler_eq_six :
    principalHeisenbergEuler = progressionProduct 6 1 * progressionProduct 6 5 := by
  rw [progression_six_split,progression_six_split]
  dsimp [principalHeisenbergEuler]
  ring

theorem E_one_split_six : E 1 =
    progressionProduct 6 1 * progressionProduct 6 2 * progressionProduct 6 3 *
    progressionProduct 6 4 * progressionProduct 6 5 * E 6 := by
  rw [E,pow_one,qPochhammerInf_eq_prod_range (by decide : 6 ≠ 0) (by simp [q])]
  norm_num only [Finset.prod_range_succ,Finset.prod_range_zero,pow_zero,mul_one,one_mul,
    ← pow_succ',Nat.reduceAdd]
  rfl

theorem dualAffineDenominator_111 :
    dualAffineDenominator 1 1 1 = (E 1)^2 * principalHeisenbergEuler := by
  rw [E_one_split_six,principalHeisenbergEuler_eq_six]
  norm_num [dualAffineDenominator,dualImaginaryPeriod,dualRootHeights_one]
  ring

/-- The two inputs are the cleared standard character formula and the
Heisenberg character factorization, after the stated root-data substitution.
Neither input says that the desired vacuum character is K2. -/
theorem vacuum_eq_K₂_of_standard_character_formulas (C S : PowerSeries ℤ)
    (hchar : dualAffineDenominator 1 1 1 * C = dualAffineDenominator 4 1 1)
    (hHeisenberg : principalHeisenbergEuler * C = S) : S = K₂ := by
  apply (vacuumCharacter_eq_K₂_iff S).mpr
  rw [dualAffineDenominator_111,dualAffineDenominator_411,mul_assoc,hHeisenberg] at hchar
  exact hchar

end KanadeRussell.Product
