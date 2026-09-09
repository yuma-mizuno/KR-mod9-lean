import KanadeRussell.Tsuchioka.SecondRootElimination
import KanadeRussell.Tsuchioka.FockGrading
import KanadeRussell.Tsuchioka.LocalReduction

/-! Homogeneous generation by the first-root modes, for every polynomial seed.
This identifies two concrete cyclic spans and assumes no affine-module character. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

/-- First-root words of prescribed total index acting on a fixed seed. -/
noncomputable def firstWordSpan (w : K) (f : Space K) (d : ℤ) : Submodule K (Space K) :=
  Submodule.span K ((fun u : Word => (highestWeightAction w).wordOperator u f) ''
    {u | u.sum = d})

theorem firstWordSpan_seed (w : K) (f : Space K) :
    f ∈ firstWordSpan w f 0 :=
  Submodule.subset_span ⟨[], rfl, rfl⟩

theorem firstWordSpan_mode_mem (w : K) (seed : Space K) (i d : ℤ)
    (f : Space K) (hf : f ∈ firstWordSpan w seed d) :
    mode w i f ∈ firstWordSpan w seed (i + d) := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact Submodule.subset_span ⟨i :: u, by simpa using congrArg (i + ·) hu, rfl⟩
  | zero => simp
  | add x y hx hy hix hiy =>
    simpa only [map_add] using (firstWordSpan w seed (i + d)).add_mem hix hiy
  | smul c x hx hi =>
    simpa only [map_smul] using (firstWordSpan w seed (i + d)).smul_mem c hi

theorem firstWordSpan_secondRootMode_mem (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (seed : Space K) (i d : ℤ) (f : Space K) (hf : f ∈ firstWordSpan w seed d) :
    secondRootMode w i f ∈ firstWordSpan w seed (i + d) :=
  secondRootMode_mem_of_graded_mode_stable w hw (firstWordSpan w seed)
    (firstWordSpan_mode_mem w seed) i d f hf

/-- A single second-root mode can be eliminated using at most two first-root
modes; the algebraic span is homogeneous in the mode index. -/
theorem secondRootMode_mem_length_two (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (i : ℤ) (f : Space K) :
    secondRootMode w i f ∈ Submodule.span K
      ((fun u : Word => (highestWeightAction w).wordOperator u f) ''
        {u | u.length ≤ 2 ∧ u.sum = i}) := by
  apply secondRootMode_mem_of_quadratic w hw
  · exact Submodule.subset_span ⟨[i], ⟨by simp, by simp⟩, rfl⟩
  · intro hi
    exact Submodule.subset_span ⟨[], ⟨by simp, by simpa using hi.symm⟩, rfl⟩
  · intro a b hab
    exact Submodule.subset_span ⟨[a, b], ⟨by simp, by simpa using hab⟩, rfl⟩

/-- Colour zero is the first-root family, and colour one is the second. -/
noncomputable def twoRootWordOperator (w : K) : List (Fin 2 × ℤ) → Module.End K (Space K)
  | [] => LinearMap.id
  | r :: u =>
    (if r.1 = 0 then mode w r.2 else secondRootMode w r.2).comp
      (twoRootWordOperator w u)

noncomputable def twoRootWordSpan (w : K) (f : Space K) (d : ℤ) : Submodule K (Space K) :=
  Submodule.span K ((fun u : List (Fin 2 × ℤ) => twoRootWordOperator w u f) ''
    {u | (u.map Prod.snd).sum = d})

theorem twoRootWord_mem_firstWordSpan (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (u : List (Fin 2 × ℤ)) :
    twoRootWordOperator w u f ∈ firstWordSpan w f (u.map Prod.snd).sum := by
  induction u with
  | nil => exact firstWordSpan_seed w f
  | cons r u ih =>
    simp only [twoRootWordOperator, LinearMap.comp_apply, List.map_cons, List.sum_cons]
    split_ifs
    · exact firstWordSpan_mode_mem w f r.2 _ _ ih
    · exact firstWordSpan_secondRootMode_mem w hw f r.2 _ _ ih

theorem twoRootWordOperator_first (w : K) (u : Word) :
    twoRootWordOperator w (u.map (fun i => ((0 : Fin 2), i))) =
      (highestWeightAction w).wordOperator u := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    simp only [List.map_cons, twoRootWordOperator, if_true, ih,
      HighestWeightAction.wordOperator]
    rfl

/-- The two root families generate exactly the same space as the first family,
separately in every total mode index and for every polynomial seed. -/
theorem twoRootWordSpan_eq_firstWordSpan (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (d : ℤ) : twoRootWordSpan w f d = firstWordSpan w f d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    change (u.map Prod.snd).sum = d at hu
    change twoRootWordOperator w u f ∈ firstWordSpan w f d
    rw [← hu]
    exact twoRootWord_mem_firstWordSpan w hw f u
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    change u.sum = d at hu
    apply Submodule.subset_span
    refine ⟨u.map (fun i => ((0 : Fin 2), i)), ?_, ?_⟩
    · change ((u.map (fun i => ((0 : Fin 2), i))).map Prod.snd).sum = d
      rw [List.map_map]
      change (u.map id).sum = d
      rw [List.map_id]
      exact hu
    · dsimp only
      rw [twoRootWordOperator_first]

end KanadeRussell.Tsuchioka.Fock
