import KanadeRussell.Straightening.SectorSpanning
import KanadeRussell.Sectors.SkewCyclicity
import KanadeRussell.Sectors.AlternatingCyclicity

/-! The three concrete first-root cyclic spaces have the admissible-partition
dimension bounds. These statements contain no character assumptions. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Sectors
open Tsuchioka Tsuchioka.Fock Straightening
variable {K : Type*} [Field K] [CharZero K]

theorem skew_firstWordSpan_finite (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.Finite K (firstWordSpan w skewSeed (-(n : ℤ))) := by
  rw [← skew_cyclicGrade_map]
  letI := skew_cyclicGrade_finite w hw n
  infer_instance

theorem skew_firstWordSpan_finrank_le_count (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.finrank K (firstWordSpan w skewSeed (-(n : ℤ))) ≤ Partitions.count 1 n := by
  rw [← skew_cyclicGrade_map]
  rw [← (Submodule.equivMapOfInjective (skewSpace (K := K)).subtype
    (skewSpace (K := K)).subtype_injective
    (Partitions.cyclicGrade (skewHighestWeightAction w) n)).finrank_eq]
  exact skew_finrank_le_count w hw n

theorem alternating_firstWordSpan_finite (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.Finite K (firstWordSpan w alternatingSeed (-(n : ℤ))) := by
  rw [← alternating_cyclicGrade_map]
  letI := alternating_cyclicGrade_finite w hw n
  infer_instance

theorem alternating_firstWordSpan_finrank_le_count (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.finrank K (firstWordSpan w alternatingSeed (-(n : ℤ))) ≤ Partitions.count 3 n := by
  rw [← alternating_cyclicGrade_map]
  rw [← (Submodule.equivMapOfInjective (alternatingSpace (K := K)).subtype
    (alternatingSpace (K := K)).subtype_injective
    (Partitions.cyclicGrade (alternatingHighestWeightAction w) n)).finrank_eq]
  exact alternating_finrank_le_count w hw n

end KanadeRussell.Sectors
