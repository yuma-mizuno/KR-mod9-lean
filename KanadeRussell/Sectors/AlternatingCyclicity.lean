import KanadeRussell.Tsuchioka.AlternatingInitialReduction
import KanadeRussell.Tsuchioka.TensorCyclicity

/-! The shifted alternating Z grades are exactly the corresponding vacuum
grades of the actual tensor cyclic module. No character formula is used. -/
set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

theorem alternating_cyclicGrade_map (w : K) (n : ℕ) :
    (Partitions.cyclicGrade (alternatingHighestWeightAction w) n).map
        (alternatingSpace (K := K)).subtype =
      firstWordSpan w alternatingSeed (-(n : ℤ)) := by
  unfold Partitions.cyclicGrade firstWordSpan
  rw [Submodule.map_span, Set.image_image]
  congr 1
  apply Set.image_congr
  intro u hu
  exact alternating_wordValue_val w u

theorem tensor_alternating_vacuum_grade (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    (tensorCyclicSpan w alternatingSeed ⊓ heisenbergVacuum w) ⊓ grade ((n : ℤ)+3) =
      (Partitions.cyclicGrade (alternatingHighestWeightAction w) n).map
        (alternatingSpace (K := K)).subtype := by
  rw [tensorCyclicSpan_inf_vacuum_eq_zCyclicSpan w hw alternatingSeed
      (alternatingSeed_heisenbergVacuum w),
    zCyclicSpan_inf_grade_eq_firstWordSpan w hw alternatingSeed 3 ((n : ℤ)+3)
      alternatingSeed_grade,
    alternating_cyclicGrade_map]
  congr 1
  ring

end KanadeRussell.Tsuchioka.Fock
