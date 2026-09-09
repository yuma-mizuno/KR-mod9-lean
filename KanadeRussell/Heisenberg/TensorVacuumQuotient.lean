import KanadeRussell.Heisenberg.PolynomialGrading

/-! A degreewise quotient of the concrete tensor cyclic module inherits the
minimum-two vacuum dimension bound. The map and its intertwining and grading
properties are explicit inputs. No character formula is an input or a conclusion. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Heisenberg
open Tsuchioka Tsuchioka.Fock
variable {K W : Type*} [Field K] [CharZero K] [AddCommGroup W] [Module K W]

noncomputable def tensorVacuumGrade (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Submodule K (tensorCyclicSpan w (1 : Space K)) :=
  (tensorCyclicGrading w hw 1).grade n ⊓ vacuum (tensorCyclicGrading w hw 1).annihilate

theorem tensorVacuumGrade_map (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    (tensorVacuumGrade w hw n).map (tensorCyclicSpan w 1).subtype =
      (tensorCyclicSpan w 1 ⊓ heisenbergVacuum w) ⊓ grade (n:ℤ) := by
  unfold tensorVacuumGrade
  rw [tensorCyclicGrading_vacuum]
  change ((grade (n:ℤ)).comap (tensorCyclicSpan w 1).subtype ⊓
    (heisenbergVacuum w).comap (tensorCyclicSpan w 1).subtype).map _ = _
  rw [← Submodule.comap_inf, Submodule.map_comap_subtype]
  ac_rfl

theorem tensorVacuumGrade_finite (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.Finite K (tensorVacuumGrade w hw n) := by
  letI : Module.Finite K ((tensorVacuumGrade w hw n).map (tensorCyclicSpan w 1).subtype) := by
    rw [tensorVacuumGrade_map w hw n]
    exact tensorCyclicSpan_vacuum_grade_finite w hw n
  let e := Submodule.equivMapOfInjective (tensorCyclicSpan w 1).subtype
    (tensorCyclicSpan w 1).subtype_injective (tensorVacuumGrade w hw n)
  exact Module.Finite.of_injective e.toLinearMap e.injective

theorem tensorVacuumGrade_finrank_le_count (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.finrank K (tensorVacuumGrade w hw n) ≤ Partitions.count 2 n := by
  have h := (Submodule.equivMapOfInjective (tensorCyclicSpan w 1).subtype
    (tensorCyclicSpan w 1).subtype_injective (tensorVacuumGrade w hw n)).finrank_eq
  rw [tensorVacuumGrade_map w hw n] at h
  rw [h]
  exact finrank_tensorCyclicSpan_vacuum_grade_le_count w hw n

/-- The graded highest-weight quotient only needs to commute with the oscillators.
Vacuum surjectivity is proved here rather than supplied as an assumption. -/
theorem quotient_vacuum_finrank_le_count (w : K) (hw : w^4-w^2+1=0)
    (a' b' : Mode → Module.End K W) (f : tensorCyclicSpan w (1 : Space K) →ₗ[K] W)
    (hfa : ∀ i v, f ((tensorCyclicGrading w hw 1).annihilate i v) = a' i (f v))
    (hfb : ∀ i v, f ((tensorCyclicGrading w hw 1).create i v) = b' i (f v))
    (n : ℕ) (T : Submodule K W)
    (hmap : ((tensorCyclicGrading w hw 1).grade n).map f = T) :
    Module.finrank K (T ⊓ vacuum a' : Submodule K W) ≤ Partitions.count 2 n := by
  letI : Module.Finite K ((tensorCyclicGrading w hw 1).grade (n:ℤ) ⊓
      vacuum (tensorCyclicGrading w hw 1).annihilate : Submodule K (tensorCyclicSpan w (1 : Space K))) :=
    tensorVacuumGrade_finite w hw n
  have h := (tensorCyclicGrading w hw 1).finrank_vacuum_grade_le a' b' f hfa hfb n T hmap
  exact h.trans (tensorVacuumGrade_finrank_le_count w hw n)

end KanadeRussell.Heisenberg
