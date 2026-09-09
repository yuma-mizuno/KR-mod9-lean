import KanadeRussell.Representation.ChevalleyQuotient
import KanadeRussell.Representation.CharacterSpecialization

/-! The minimum-two lower bound from two explicit standard character formulas.
These are application hypotheses, not axioms or a discharge of LowerBounds. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock Heisenberg
variable {K : Type*} [Field K] [CharZero K]

/-- The transpose uses the untwisted G2 affine convention used in the denominator. -/
theorem sourceCartan_transpose : affineCartanMatrix.transpose =
    (!![2,-1,0; -1,2,-1; 0,-3,2] : Matrix (Fin 3) (Fin 3) ℤ) := by decide

/-- These are the null-root coefficients on the dual side. -/
theorem dual_nullRoot_coefficients :
    Matrix.mulVec affineCartanMatrix.transpose (![1,2,3] : Fin 3 → ℤ) = 0 := by decide

noncomputable def quotientVacuumCharacter (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Module.finrank K (quotientCyclicGrade w S n ⊓
    vacuum (fun m : Mode => quotientHeisenberg w hw S hS m.val) :
      Submodule K (Space K ⧸ S)) : ℤ)

theorem coeff_quotientVacuumCharacter_le_B (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : ℕ) :
    PowerSeries.coeff n (quotientVacuumCharacter w hw S hS) ≤ PowerSeries.coeff n B := by
  rw [quotientVacuumCharacter,PowerSeries.coeff_mk,Partitions.coeff_B_count]
  exact_mod_cast quotientCyclicGrade_principalVacuum_finrank_le_count w hw S hS n

/-- Once the standard quotient supplies the normalized full-character and
Heisenberg-factorization formulas, the second KR lower bound follows.
The character equations are explicit and are not inferred from stability alone. -/
theorem second_lowerBound_of_standard_character_formulas
    (w : K) (hw : w^4-w^2+1=0) (S : Submodule K (Space K)) (hS : ChevalleyStable w S)
    (fullCharacter : PowerSeries ℤ)
    (hchar : Product.dualAffineDenominator 1 1 1 * fullCharacter =
      Product.dualAffineDenominator 4 1 1)
    (hfactor : Product.principalHeisenbergEuler * fullCharacter =
      quotientVacuumCharacter w hw S hS) :
    ∀ n : ℕ, PowerSeries.coeff n K₂ ≤ PowerSeries.coeff n B := by
  have hv := Product.vacuum_eq_K₂_of_standard_character_formulas fullCharacter
    (quotientVacuumCharacter w hw S hS) hchar hfactor
  intro n
  rw [← hv]
  exact coeff_quotientVacuumCharacter_le_B w hw S hS n

end KanadeRussell.Representation
