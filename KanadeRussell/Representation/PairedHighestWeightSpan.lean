import KanadeRussell.Representation.NegativeWordGrades
import Mathlib.LinearAlgebra.Prod

/-! The simultaneous lowering words of two highest-weight modules form a stable
subspace of their product. Its projections are onto, and its degree-zero part
is the diagonal highest line. No comparison or character theorem is assumed. -/

set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open PrincipalHighestWeightModule
attribute [local instance] LieRing.ofAssociativeRing
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable (M : PrincipalHighestWeightModule K V) (N : PrincipalHighestWeightModule K W)

def pairedNegativeWordValue (u : List (Fin 3)) : V × W :=
  (M.negativeWordValue u, N.negativeWordValue u)

noncomputable def pairedHighestWeightSpan : Submodule K (V × W) :=
  Submodule.span K (Set.range (pairedNegativeWordValue M N))

theorem pairedNegativeWordValue_mem_span (u : List (Fin 3)) :
    pairedNegativeWordValue M N u ∈ pairedHighestWeightSpan M N :=
  Submodule.subset_span ⟨u, rfl⟩

theorem pairedHighestVector_mem_span :
    (M.highestVector, N.highestVector) ∈ pairedHighestWeightSpan M N :=
  pairedNegativeWordValue_mem_span M N []

theorem pairedHighestWeightSpan_F_stable (i : Fin 3) (p : V × W)
    (hp : p ∈ pairedHighestWeightSpan M N) :
    (M.action.F i p.1, N.action.F i p.2) ∈ pairedHighestWeightSpan M N := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u, rfl⟩ := hp
    exact pairedNegativeWordValue_mem_span M N (i :: u)
  | zero =>
    simpa only [Prod.fst_zero, Prod.snd_zero, map_zero, Prod.mk_zero_zero] using
      (pairedHighestWeightSpan M N).zero_mem
  | add p q hp hq ihp ihq =>
    simpa only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk] using
      (pairedHighestWeightSpan M N).add_mem ihp ihq
  | smul c p hp ih =>
    simpa only [Prod.smul_fst, Prod.smul_snd, map_smul, Prod.smul_mk] using
      (pairedHighestWeightSpan M N).smul_mem c ih

theorem pairedHighestWeightSpan_H_stable (hweight : M.highestWeight = N.highestWeight)
    (i : Fin 3) (p : V × W) (hp : p ∈ pairedHighestWeightSpan M N) :
    (M.action.H i p.1, N.action.H i p.2) ∈ pairedHighestWeightSpan M N := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u, rfl⟩ := hp
    change (M.action.H i (M.negativeWordValue u),
      N.action.H i (N.negativeWordValue u)) ∈ _
    rw [M.H_negativeWordValue, N.H_negativeWordValue, hweight]
    simpa only [Prod.smul_mk, pairedNegativeWordValue] using
      (pairedHighestWeightSpan M N).smul_mem _ (pairedNegativeWordValue_mem_span M N u)
  | zero =>
    simpa only [Prod.fst_zero, Prod.snd_zero, map_zero, Prod.mk_zero_zero] using
      (pairedHighestWeightSpan M N).zero_mem
  | add p q hp hq ihp ihq =>
    simpa only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk] using
      (pairedHighestWeightSpan M N).add_mem ihp ihq
  | smul c p hp ih =>
    simpa only [Prod.smul_fst, Prod.smul_snd, map_smul, Prod.smul_mk] using
      (pairedHighestWeightSpan M N).smul_mem c ih

private theorem E_negativeWordValue_cons (i j : Fin 3) (u : List (Fin 3)) :
    M.action.E i (M.negativeWordValue (j :: u)) =
      (if i = j then M.action.H i (M.negativeWordValue u) else 0) +
        M.action.F j (M.action.E i (M.negativeWordValue u)) := by
  have h := congrArg (fun a : Module.End K V => a (M.negativeWordValue u))
    (M.action.EF i j)
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  by_cases hij : i = j
  · simpa only [negativeWordValue_cons, hij, if_true] using h
  · simpa only [negativeWordValue_cons, hij, if_false, LinearMap.zero_apply] using h

theorem pairedHighestWeightSpan_E_stable (hweight : M.highestWeight = N.highestWeight)
    (i : Fin 3) (p : V × W) (hp : p ∈ pairedHighestWeightSpan M N) :
    (M.action.E i p.1, N.action.E i p.2) ∈ pairedHighestWeightSpan M N := by
  have hw (u : List (Fin 3)) :
      (M.action.E i (M.negativeWordValue u), N.action.E i (N.negativeWordValue u)) ∈
        pairedHighestWeightSpan M N := by
    induction u with
    | nil =>
      simp only [negativeWordValue_nil, M.E_highestVector, N.E_highestVector]
      simpa only [Prod.mk_zero_zero] using (pairedHighestWeightSpan M N).zero_mem
    | cons j u ih =>
      rw [E_negativeWordValue_cons M, E_negativeWordValue_cons N]
      have hF := pairedHighestWeightSpan_F_stable M N j _ ih
      by_cases hij : i = j
      · simp only [hij, if_true]
        simpa only [Prod.mk_add_mk, Prod.fst, Prod.snd, pairedNegativeWordValue, hij] using
          (pairedHighestWeightSpan M N).add_mem
          (pairedHighestWeightSpan_H_stable M N hweight j _
            (pairedNegativeWordValue_mem_span M N u)) hF
      · simpa only [hij, if_false, zero_add] using hF
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨u, rfl⟩ := hp; exact hw u
  | zero =>
    simpa only [Prod.fst_zero, Prod.snd_zero, map_zero, Prod.mk_zero_zero] using
      (pairedHighestWeightSpan M N).zero_mem
  | add p q hp hq ihp ihq =>
    simpa only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk] using
      (pairedHighestWeightSpan M N).add_mem ihp ihq
  | smul c p hp ih =>
    simpa only [Prod.smul_fst, Prod.smul_snd, map_smul, Prod.smul_mk] using
      (pairedHighestWeightSpan M N).smul_mem c ih

noncomputable def pairedHighestWeightFst : pairedHighestWeightSpan M N →ₗ[K] V :=
  (LinearMap.fst K V W).comp (pairedHighestWeightSpan M N).subtype

noncomputable def pairedHighestWeightSnd : pairedHighestWeightSpan M N →ₗ[K] W :=
  (LinearMap.snd K V W).comp (pairedHighestWeightSpan M N).subtype

@[simp] theorem pairedHighestWeightFst_apply (p : pairedHighestWeightSpan M N) :
    pairedHighestWeightFst M N p = p.val.1 := rfl

@[simp] theorem pairedHighestWeightSnd_apply (p : pairedHighestWeightSpan M N) :
    pairedHighestWeightSnd M N p = p.val.2 := rfl

theorem pairedHighestWeightFst_range : (pairedHighestWeightFst M N).range = ⊤ := by
  apply top_unique
  rw [← M.negativeWordSpan_eq_top]
  apply Submodule.span_le.mpr
  rintro p ⟨u, rfl⟩
  exact ⟨⟨pairedNegativeWordValue M N u, pairedNegativeWordValue_mem_span M N u⟩, rfl⟩

theorem pairedHighestWeightSnd_range : (pairedHighestWeightSnd M N).range = ⊤ := by
  apply top_unique
  rw [← N.negativeWordSpan_eq_top]
  apply Submodule.span_le.mpr
  rintro p ⟨u, rfl⟩
  exact ⟨⟨pairedNegativeWordValue M N u, pairedNegativeWordValue_mem_span M N u⟩, rfl⟩

theorem pairedHighestWeightFst_surjective : Function.Surjective (pairedHighestWeightFst M N) :=
  LinearMap.range_eq_top.mp (pairedHighestWeightFst_range M N)

theorem pairedHighestWeightSnd_surjective : Function.Surjective (pairedHighestWeightSnd M N) :=
  LinearMap.range_eq_top.mp (pairedHighestWeightSnd_range M N)

/-- Simultaneous degree projection retains exactly the paired words of that length. -/
theorem pairedHighestWeightSpan_gradeProjection_mem_span (d : ℤ) (p : V × W)
    (hp : p ∈ pairedHighestWeightSpan M N) :
    (M.gradeProjection d p.1, N.gradeProjection d p.2) ∈ Submodule.span K
      (pairedNegativeWordValue M N '' {u : List (Fin 3) | (u.length : ℤ) = d}) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u, rfl⟩ := hp
    change (M.gradeProjection d (M.negativeWordValue u),
      N.gradeProjection d (N.negativeWordValue u)) ∈ _
    by_cases hu : (u.length : ℤ) = d
    · rw [M.gradeProjection_of_mem d _ (hu ▸ M.negativeWordValue_mem_grade u),
        N.gradeProjection_of_mem d _ (hu ▸ N.negativeWordValue_mem_grade u)]
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    · rw [M.gradeProjection_of_mem_ne d _ _ (M.negativeWordValue_mem_grade u) (Ne.symm hu),
        N.gradeProjection_of_mem_ne d _ _ (N.negativeWordValue_mem_grade u) (Ne.symm hu)]
      exact Submodule.zero_mem _
  | zero => simpa only [Prod.fst_zero, Prod.snd_zero, map_zero, Prod.mk_zero_zero] using (Submodule.zero_mem (Submodule.span K
      (pairedNegativeWordValue M N '' {u : List (Fin 3) | (u.length : ℤ) = d})))
  | add p q hp hq ihp ihq =>
    simpa only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk] using Submodule.add_mem _ ihp ihq
  | smul c p hp ih =>
    simpa only [Prod.smul_fst, Prod.smul_snd, map_smul, Prod.smul_mk] using Submodule.smul_mem _ c ih

theorem pairedHighestWeightSpan_gradeProjection (d : ℤ) (p : V × W)
    (hp : p ∈ pairedHighestWeightSpan M N) :
    (M.gradeProjection d p.1, N.gradeProjection d p.2) ∈ pairedHighestWeightSpan M N := by
  apply (show Submodule.span K
      (pairedNegativeWordValue M N '' {u : List (Fin 3) | (u.length : ℤ) = d}) ≤
        pairedHighestWeightSpan M N from Submodule.span_mono (Set.image_subset_range _ _))
  exact pairedHighestWeightSpan_gradeProjection_mem_span M N d p hp

theorem pairedHighestWeightSpan_gradeProjection_zero (p : V × W)
    (hp : p ∈ pairedHighestWeightSpan M N) :
    (M.gradeProjection 0 p.1, N.gradeProjection 0 p.2) ∈
      Submodule.span K {(M.highestVector, N.highestVector)} := by
  have h := pairedHighestWeightSpan_gradeProjection_mem_span M N 0 p hp
  have hs : pairedNegativeWordValue M N '' {u : List (Fin 3) | (u.length : ℤ) = 0} =
      {(M.highestVector, N.highestVector)} := by
    ext p
    simp [pairedNegativeWordValue]
  rwa [hs] at h

end KanadeRussell.Representation
