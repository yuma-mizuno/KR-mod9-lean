import KanadeRussell.Heisenberg.PolynomialGrading
import KanadeRussell.Sectors.LowerTensorGrades

/-! Seed-normalized nonnegative oscillator gradings on the actual three cyclic tensor modules. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Heisenberg
open Tsuchioka Tsuchioka.Fock Sectors
variable {K : Type*} [Field K] [CharZero K]

/-- Shift only the degree labels. The underlying space and both actual normalized
oscillators are exactly those of tensorCyclicGrading. -/
noncomputable def shiftedTensorCyclicGrading (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ)
    (hlow : ∀ e : ℤ, e < d → tensorCyclicSpan w seed ⊓ grade e = ⊥) :
    GradedSystem K (tensorCyclicSpan w seed) Mode where
  annihilate := (tensorCyclicGrading w hw seed).annihilate
  create := (tensorCyclicGrading w hw seed).create
  weight := (tensorCyclicGrading w hw seed).weight
  weight_pos := (tensorCyclicGrading w hw seed).weight_pos
  weight_finite := (tensorCyclicGrading w hw seed).weight_finite
  grade n := (tensorCyclicGrading w hw seed).grade (n+d)
  negative n hn := by
    apply le_antisymm _ bot_le
    intro p hp
    rw [Submodule.mem_bot]
    apply Subtype.ext
    have hx : p.val ∈ tensorCyclicSpan w seed ⊓ grade (n+d) := ⟨p.property,hp⟩
    rw [hlow (n+d) (by omega), Submodule.mem_bot] at hx
    exact hx
  lower i n p hp := by
    have h := (tensorCyclicGrading w hw seed).lower i (n+d) p hp
    convert h using 1 <;> congr 1 <;> ring
  raise i n p hp := by
    have h := (tensorCyclicGrading w hw seed).raise i (n+d) p hp
    convert h using 1 <;> congr 1 <;> ring
  pair := (tensorCyclicGrading w hw seed).pair
  positive_commute := (tensorCyclicGrading w hw seed).positive_commute
  cross_commute := (tensorCyclicGrading w hw seed).cross_commute

@[simp] theorem shiftedTensorCyclicGrading_grade (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ)
    (hlow : ∀ e : ℤ, e < d → tensorCyclicSpan w seed ⊓ grade e = ⊥) (n : ℤ) :
    (shiftedTensorCyclicGrading w hw seed d hlow).grade n =
      (grade (n+d)).comap (tensorCyclicSpan w seed).subtype := rfl

theorem shiftedTensorCyclicGrading_grade_map (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ)
    (hlow : ∀ e : ℤ, e < d → tensorCyclicSpan w seed ⊓ grade e = ⊥) (n : ℤ) :
    ((shiftedTensorCyclicGrading w hw seed d hlow).grade n).map
      (tensorCyclicSpan w seed).subtype = tensorCyclicSpan w seed ⊓ grade (n+d) := by
  ext p
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨v.property,hv⟩
  · rintro ⟨hp,hg⟩
    exact ⟨⟨p,hp⟩,hg,rfl⟩

theorem shiftedTensorCyclicGrading_vacuum (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ)
    (hlow : ∀ e : ℤ, e < d → tensorCyclicSpan w seed ⊓ grade e = ⊥) :
    vacuum (shiftedTensorCyclicGrading w hw seed d hlow).annihilate =
      (heisenbergVacuum w).comap (tensorCyclicSpan w seed).subtype :=
  tensorCyclicGrading_vacuum w hw seed

noncomputable def skewTensorCyclicGrading (w : K) (hw : w^4-w^2+1=0) :
    GradedSystem K (tensorCyclicSpan w (skewSeed : Space K)) Mode :=
  shiftedTensorCyclicGrading w hw skewSeed 1 (tensor_skew_grade_below_one w hw)

noncomputable def vacuumTensorCyclicGrading (w : K) (hw : w^4-w^2+1=0) :
    GradedSystem K (tensorCyclicSpan w (1 : Space K)) Mode :=
  shiftedTensorCyclicGrading w hw 1 0 (tensor_vacuum_grade_below_zero w)

noncomputable def alternatingTensorCyclicGrading (w : K) (hw : w^4-w^2+1=0) :
    GradedSystem K (tensorCyclicSpan w (alternatingSeed : Space K)) Mode :=
  shiftedTensorCyclicGrading w hw alternatingSeed 3 (tensor_alternating_grade_below_three w hw)

end KanadeRussell.Heisenberg
