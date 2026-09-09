import KanadeRussell.Tsuchioka.AffineAlternatingLowering
import KanadeRussell.Tsuchioka.AffineAlternatingHighestWeight
import KanadeRussell.Tsuchioka.AlternatingSmallGrades

/-! The remaining lowering square on the alternating highest-weight vector. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries
open RootData (Lattice rootWeight)
variable {K : Type*} [Field K] [CharZero K]

theorem coeff_two_diagonalRootCreation (w : K) (beta : Lattice) :
    coeff 2 (diagonalRootCreation w beta) =
      (8 * rootWeight (w ^ (-1 : ℤ)) beta ^ 2) • (diagonalCoordinate firstMode ^ 2) := by
  rw [diagonalRootCreation, FormalSeries.coeff_two_exponential
    (constantCoeff_diagonalRootCreationLog w beta)]
  have h1 : coeff 1 (diagonalRootCreationLog w beta) =
      (4 * rootWeight (w ^ (-1 : ℤ)) beta) • diagonalCoordinate firstMode := by
    simp [diagonalRootCreationLog, IsMode, firstMode, MvPolynomial.C_eq_smul_one]
  have h2 : coeff 2 (diagonalRootCreationLog w beta) = 0 := by
    simp [diagonalRootCreationLog, IsMode]
  rw [h1, h2, zero_add, IsScalarTower.algebraMap_apply ℚ K (Space K), MvPolynomial.algebraMap_eq]
  norm_num [MvPolynomial.C_eq_smul_one, mul_pow, smul_pow, smul_smul]
  module

theorem tensorRootMode_neg_two_alternatingSeed (w : K) (hw : w^4-w^2+1=0)
    (beta : RootData.Root) :
    tensorRootMode w beta.val (-2) (alternatingSeed : Space K) =
      (8 * rootWeight (w ^ (-1 : ℤ)) beta.val ^ 2) •
        (diagonalCoordinate firstMode ^ 2 * tensorRootMode w beta.val 0 alternatingSeed) := by
  let p : PowerSeries (Space K) := PowerSeries.mk fun n : ℕ => (rootField w beta.val alternatingSeed).coeff n
  have hp : (p : LaurentSeries (Space K)) = rootField w beta.val alternatingSeed := by
    apply HahnSeries.ext
    funext n
    rw [PowerSeries.coeff_coe]
    by_cases hn : n < 0
    · rw [if_pos hn]
      have hz := rootMode_alternatingSeed_pos w hw beta.val (-n) (by omega)
      change (rootField w beta.val alternatingSeed).coeff (-(-n)) = 0 at hz
      simpa only [neg_neg] using hz.symm
    · rw [if_neg hn]
      simp only [p, coeff_mk, ← Int.eq_natAbs_of_nonneg (by omega : 0 ≤ n)]
  have h0 : coeff 0 p = tensorRootMode w beta.val 0 alternatingSeed :=
    by simpa [p, rootMode] using rootMode_zero_alternatingSeed w hw beta.val
  have h1 : coeff 1 p = 0 := by simpa [p, rootMode] using rootMode_neg_one_alternatingSeed w hw beta
  have h2 : coeff 2 p = 0 := by simpa [p, rootMode] using rootMode_neg_two_alternatingSeed w hw beta
  change (tensorRootField w beta.val alternatingSeed).coeff 2 = _
  rw [tensorRootField_on_vacuum w hw beta.val alternatingSeed (alternatingSeed_heisenbergVacuum w),
    ← hp, ← PowerSeries.coe_mul]
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, LaurentSeries.coeff_coe_powerSeries, coeff_mul]
  have ha : Finset.antidiagonal 2 = {(0,2),(1,1),(2,0)} := rfl
  norm_num [ha, Finset.sum_insert, Finset.sum_singleton, Prod.fst, Prod.snd,
    h0, h1, h2, mul_zero, zero_add, coeff_two_diagonalRootCreation, smul_mul_assoc]

theorem tensorRootMode_neg_one_diagonal_alternatingSeed (w : K) (hw : w^4-w^2+1=0)
    (beta : Lattice) (hbeta : RootData.IsRoot beta) :
    tensorRootMode w beta (-1) (diagonalCoordinate firstMode * (alternatingSeed : Space K)) =
      diagonalCoordinate firstMode * tensorRootMode w beta (-1) alternatingSeed -
      (8 * contraction w 1 * rootWeight w beta * rootWeight (w ^ (-1 : ℤ)) beta ^ 2) •
        (diagonalCoordinate firstMode ^ 2 * tensorRootMode w beta 0 alternatingSeed) := by
  have h := tensorRootMode_heisenbergNegative w beta firstMode (-1) (alternatingSeed : Space K)
  simp only [heisenbergNegative_apply, show firstMode.val = 1 from rfl, Nat.cast_one, zpow_one] at h
  norm_num only [Int.reduceSub] at h
  erw [h, tensorRootMode_neg_two_alternatingSeed w hw ⟨beta,hbeta⟩, smul_smul]
  congr 2
  ring

theorem chevalleyF_two_diagonal_alternatingSeed (w : K) (hw : w^4-w^2+1=0) :
    chevalleyF w 2 (diagonalCoordinate firstMode * (alternatingSeed : Space K)) = 0 := by
  have hh : heisenbergMode w (-1) (diagonalCoordinate firstMode * (alternatingSeed : Space K)) =
      diagonalCoordinate firstMode ^ 2 * alternatingSeed := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    change diagonalCoordinate firstMode * (diagonalCoordinate firstMode * alternatingSeed) = _
    ring
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply, LinearMap.smul_apply,
    hh]
  rw [tensorRootMode_neg_one_diagonal_alternatingSeed w hw (RootData.simpleRoot 0) RootData.firstRoot.property,
    tensorRootMode_neg_one_diagonal_alternatingSeed w hw (RootData.simpleRoot 1) RootData.secondRoot.property]
  rw [tensorRootMode_neg_one_alternatingSeed, tensorRootMode_neg_one_alternatingSeed,
    tensorFirstRoot_zero_alternatingSeed w hw, tensorSecondRoot_zero_alternatingSeed w hw]
  have hi : rootWeight (w ^ (-1 : ℤ)) (RootData.simpleRoot 1) = -w^3+w^2-1 := by
    rw [RootData.rootWeight_second, Scalar.zpow_phasePolynomial w hw (-1)]
    norm_num [Scalar.phasePolynomial]
    grind only
  rw [hi, RootData.rootWeight_first, RootData.rootWeight_first, RootData.rootWeight_second,
    contraction_one w hw]
  norm_num [chevalleyFCoordinates, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [smul_smul, ← mul_assoc, ← pow_two,
    ← sub_smul, ← add_smul]
  conv_rhs => rw [← zero_smul K (diagonalCoordinate firstMode ^ 2 * (alternatingSeed : Space K))]
  congr 1
  clear hh hi
  grind only
theorem chevalleyF_two_sq_alternatingSeed (w : K) (hw : w^4-w^2+1=0) :
    ((chevalleyF w 2)^2) (alternatingSeed : Space K) = 0 := by
  rw [pow_two, Module.End.mul_apply]
  have hh : heisenbergMode w (-1) (alternatingSeed : Space K) =
      diagonalCoordinate firstMode * alternatingSeed := by
    rw [show (-1 : ℤ) = -(firstMode.val : ℤ) from rfl, heisenbergMode_negative]
    rfl
  conv_lhs => arg 2; unfold chevalleyF; rw [tensorModeEvaluate_apply]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, tensorRootMode_neg_one_alternatingSeed, hh,
    map_add, map_smul]
  rw [chevalleyF_two_diagonal_alternatingSeed w hw]
  norm_num [chevalleyFCoordinates, Matrix.cons_val_two, Matrix.cons_val_three]

/-- All three finite simple-root lowering equations on the alternating seed. -/
theorem chevalleyF_alternatingSeed_integrability (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    ((chevalleyF w i)^(if i = 2 then 2 else 1)) (alternatingSeed : Space K) = 0 := by
  by_cases hi : i = 2
  · subst i
    simp only [ite_true]
    exact chevalleyF_two_sq_alternatingSeed w hw
  · rw [if_neg hi, pow_one]
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · exact chevalleyF_zero_alternatingSeed w hw
    · exact chevalleyF_one_alternatingSeed w hw

end KanadeRussell.Tsuchioka.Fock
