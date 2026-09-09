import KanadeRussell.Sectors.SkewSeed
import KanadeRussell.Tsuchioka.TensorCyclicity

/-! The concrete degree-one seed is highest for every positive root mode.
Its tensor vacuum grades are precisely the shifted first-root cyclic grades. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Sectors
open Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

theorem rootMode_skewSeed_pos (w : K) (hw : w^4-w^2+1=0)
    (β : RootData.Root) (i : ℤ) (hi : 0 < i) :
    rootMode w β.val i (skewSeed (K := K)) = 0 := by
  have hs := rootMode_mem_of_mode_stable w hw (skewSpace (K := K))
    (mode_mem_skewSpace w) β i skewSeed skewSeed_mem
  let p : skewSpace (K := K) := ⟨rootMode w β.val i skewSeed, hs⟩
  have hg : p ∈ skewGrade (-i) := by
    change rootMode w β.val i skewSeed ∈ grade (-i+1)
    simpa only [show -i+1 = 1-i by ring] using
      rootMode_mem_grade w hw β i 1 skewSeed skewSeed_grade
  rw [skewGrade_negative (-i) (by omega), Submodule.mem_bot] at hg
  exact congrArg Subtype.val hg

/-- A creation dressing cannot introduce negative Laurent powers. -/
theorem tensorRootMode_pos_of_rootMode_pos (w : K) (hw : w^4-w^2+1=0)
    (β : RootData.Lattice) (f : Space K) (hf : f ∈ heisenbergVacuum w)
    (hZ : ∀ j : ℤ, 0 < j → rootMode w β j f = 0) (i : ℤ) (hi : 0 < i) :
    tensorRootMode w β i f = 0 := by
  change (tensorRootField w β f).coeff (-i) = 0
  rw [tensorRootField_on_vacuum w hw β f hf, HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have he : ab.1 + ab.2 = -i := (Finset.mem_addAntidiagonal.mp hab).2.2
  by_cases ha : ab.1 < 0
  · rw [PowerSeries.coeff_coe, if_pos ha, zero_mul]
  · have hb : 0 < -ab.2 := by omega
    have hz := hZ (-ab.2) hb
    change (rootField w β f).coeff (-(-ab.2)) = 0 at hz
    rw [neg_neg] at hz
    rw [hz, mul_zero]

theorem tensorRootMode_skewSeed_pos (w : K) (hw : w^4-w^2+1=0)
    (β : RootData.Root) (i : ℤ) (hi : 0 < i) :
    tensorRootMode w β.val i (skewSeed (K := K)) = 0 :=
  tensorRootMode_pos_of_rootMode_pos w hw β.val skewSeed (skewSeed_heisenbergVacuum w)
    (rootMode_skewSeed_pos w hw β) i hi

theorem skew_wordValue_val (w : K) (u : Word) :
    ((skewHighestWeightAction w).wordValue u).val =
      (highestWeightAction w).wordOperator u skewSeed := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    change mode w i ((skewHighestWeightAction w).wordValue u).val =
      mode w i ((highestWeightAction w).wordOperator u skewSeed)
    rw [ih]

theorem skew_cyclicGrade_map (w : K) (n : ℕ) :
    (Partitions.cyclicGrade (skewHighestWeightAction w) n).map (skewSpace (K := K)).subtype =
      firstWordSpan w skewSeed (-(n:ℤ)) := by
  unfold Partitions.cyclicGrade firstWordSpan
  rw [Submodule.map_span, Set.image_image]
  congr 1
  apply Set.image_congr
  intro u hu
  exact skew_wordValue_val w u

theorem tensor_skew_vacuum_grade (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    (tensorCyclicSpan w skewSeed ⊓ heisenbergVacuum w) ⊓ grade ((n:ℤ)+1) =
      (Partitions.cyclicGrade (skewHighestWeightAction w) n).map (skewSpace (K := K)).subtype := by
  rw [tensorCyclicSpan_inf_vacuum_eq_zCyclicSpan w hw skewSeed (skewSeed_heisenbergVacuum w),
    zCyclicSpan_inf_grade_eq_firstWordSpan w hw skewSeed 1 ((n:ℤ)+1) skewSeed_grade,
    skew_cyclicGrade_map]
  congr 1
  ring

end KanadeRussell.Sectors
