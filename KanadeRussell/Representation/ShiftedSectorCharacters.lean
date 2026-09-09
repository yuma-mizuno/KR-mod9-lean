import KanadeRussell.Representation.ShiftedChevalleyQuotient
import KanadeRussell.Representation.OtherCharacterSpecializations
import KanadeRussell.Sectors.SpanningBounds

/-! Actual quotient vacuum dimensions, graded relative to the chosen seed.
The coefficient bounds use the proved spanning and vacuum-lifting theorems. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock Heisenberg Sectors
variable {K : Type*} [Field K] [CharZero K]

noncomputable def shiftedQuotientVacuumCharacter (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (S : Submodule K (Space K)) (hS : ChevalleyStable w S) :
    PowerSeries ℤ :=
  PowerSeries.mk fun n => (Module.finrank K (shiftedQuotientCyclicGrade w seed d S n ⊓
    vacuum (fun m : Mode => quotientHeisenberg w hw S hS m.val) :
      Submodule K (Space K ⧸ S)) : ℤ)

theorem coeff_shiftedQuotientVacuumCharacter_le (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (hv : seed ∈ heisenbergVacuum w) (hd : seed ∈ grade d)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n b : ℕ)
    [Module.Finite K (firstWordSpan w seed (-(n : ℤ)))]
    (hb : Module.finrank K (firstWordSpan w seed (-(n : ℤ))) ≤ b) :
    PowerSeries.coeff n (shiftedQuotientVacuumCharacter w hw seed d S hS) ≤ (b : ℤ) := by
  rw [shiftedQuotientVacuumCharacter, PowerSeries.coeff_mk]
  exact_mod_cast shiftedQuotientCyclicGrade_principalVacuum_finrank_le_bound
    w hw seed d hv hd S hS n b hb

theorem coeff_skewQuotientVacuumCharacter_le_A (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : ℕ) :
    PowerSeries.coeff n (shiftedQuotientVacuumCharacter w hw skewSeed 1 S hS) ≤
      PowerSeries.coeff n A := by
  rw [Partitions.coeff_A_count]
  letI := skew_firstWordSpan_finite w hw n
  exact coeff_shiftedQuotientVacuumCharacter_le w hw skewSeed 1
    (skewSeed_heisenbergVacuum w) skewSeed_grade S hS n _
    (skew_firstWordSpan_finrank_le_count w hw n)

theorem coeff_alternatingQuotientVacuumCharacter_le_C (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : ℕ) :
    PowerSeries.coeff n (shiftedQuotientVacuumCharacter w hw alternatingSeed 3 S hS) ≤
      PowerSeries.coeff n C := by
  rw [Partitions.coeff_C_count]
  letI := alternating_firstWordSpan_finite w hw n
  exact coeff_shiftedQuotientVacuumCharacter_le w hw alternatingSeed 3
    (alternatingSeed_heisenbergVacuum w) alternatingSeed_grade S hS n _
    (alternating_firstWordSpan_finrank_le_count w hw n)

theorem coeff_vacuumQuotientVacuumCharacter_le_B (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : ℕ) :
    PowerSeries.coeff n (shiftedQuotientVacuumCharacter w hw 1 0 S hS) ≤
      PowerSeries.coeff n B := by
  rw [Partitions.coeff_B_count]
  have hf : Module.Finite K (firstWordSpan w 1 (-(n : ℤ))) := by
    rw [firstWordSpan_vacuum_eq_cyclicGrade]
    exact Straightening.fock_cyclicGrade_finite w hw n
  letI := hf
  have hb : Module.finrank K (firstWordSpan w 1 (-(n : ℤ))) ≤ Partitions.count 2 n := by
    rw [firstWordSpan_vacuum_eq_cyclicGrade]
    exact Straightening.fock_finrank_le_count w hw n
  exact coeff_shiftedQuotientVacuumCharacter_le w hw 1 0
    (one_mem_heisenbergVacuum w) (MvPolynomial.isWeightedHomogeneous_one K variableWeight)
    S hS n _ hb

end KanadeRussell.Representation
