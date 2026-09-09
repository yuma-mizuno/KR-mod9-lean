import KanadeRussell.Representation.PrincipalHighestWeight

/-! Every vector is a finite linear combination of words in the actual lowering operators. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

def negativeWordValue : List (Fin 3) → V
  | [] => M.highestVector
  | i :: u => M.action.F i (negativeWordValue u)

@[simp] theorem negativeWordValue_nil : M.negativeWordValue [] = M.highestVector := rfl

@[simp] theorem negativeWordValue_cons (i : Fin 3) (u : List (Fin 3)) :
    M.negativeWordValue (i::u) = M.action.F i (M.negativeWordValue u) := rfl

theorem negativeWordValue_mem_grade (u : List (Fin 3)) :
    M.negativeWordValue u ∈ M.grade (u.length : ℤ) := by
  induction u with
  | nil => exact M.highestVector_grade
  | cons i u ih =>
    simpa only [negativeWordValue_cons, List.length_cons, Nat.cast_add, Nat.cast_one] using
      M.F_grade i (u.length:ℤ) (M.negativeWordValue u) ih

theorem H_negativeWordValue (i : Fin 3) (u : List (Fin 3)) :
    M.action.H i (M.negativeWordValue u) =
      ((M.highestWeight i:K) - (u.map (fun j => (affineCartanMatrix i j:K))).sum) •
        M.negativeWordValue u := by
  induction u with
  | nil => simpa using M.H_highestVector i
  | cons j u ih =>
    have h := congrArg (fun a : Module.End K V => a (M.negativeWordValue u)) (M.action.HF i j)
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      ← Int.cast_smul_eq_zsmul K, LinearMap.neg_apply, LinearMap.smul_apply, ih, map_smul] at h
    rw [sub_eq_iff_eq_add] at h
    simp only [negativeWordValue_cons, List.map_cons, List.sum_cons]
    rw [h]
    module

noncomputable def negativeWordSpan : Submodule K V :=
  Submodule.span K (Set.range M.negativeWordValue)

theorem negativeWordValue_mem_span (u : List (Fin 3)) : M.negativeWordValue u ∈ M.negativeWordSpan :=
  Submodule.subset_span ⟨u,rfl⟩

theorem highestVector_mem_negativeWordSpan : M.highestVector ∈ M.negativeWordSpan :=
  M.negativeWordValue_mem_span []

theorem negativeWordSpan_F_stable (i : Fin 3) (v : V) (hv : v ∈ M.negativeWordSpan) :
    M.action.F i v ∈ M.negativeWordSpan := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u,rfl⟩ := hv
    exact M.negativeWordValue_mem_span (i::u)
  | zero => simp
  | add v w hv hw hiv hiw => simpa only [map_add] using M.negativeWordSpan.add_mem hiv hiw
  | smul c v hv hi => simpa only [map_smul] using M.negativeWordSpan.smul_mem c hi

theorem negativeWordSpan_H_stable (i : Fin 3) (v : V) (hv : v ∈ M.negativeWordSpan) :
    M.action.H i v ∈ M.negativeWordSpan := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u,rfl⟩ := hv
    rw [M.H_negativeWordValue]
    exact M.negativeWordSpan.smul_mem _ (M.negativeWordValue_mem_span u)
  | zero => simp
  | add v w hv hw hiv hiw => simpa only [map_add] using M.negativeWordSpan.add_mem hiv hiw
  | smul c v hv hi => simpa only [map_smul] using M.negativeWordSpan.smul_mem c hi

/-- Commuting E past the leftmost F decreases the word length in the commutator term. -/
theorem E_negativeWordValue_mem_span (i : Fin 3) (u : List (Fin 3)) :
    M.action.E i (M.negativeWordValue u) ∈ M.negativeWordSpan := by
  induction u with
  | nil => rw [negativeWordValue_nil, M.E_highestVector]; exact M.negativeWordSpan.zero_mem
  | cons j u ih =>
    have h := congrArg (fun a : Module.End K V => a (M.negativeWordValue u)) (M.action.EF i j)
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [sub_eq_iff_eq_add] at h
    rw [negativeWordValue_cons, h]
    apply M.negativeWordSpan.add_mem _ (M.negativeWordSpan_F_stable j _ ih)
    by_cases hij : i=j
    · rw [if_pos hij]
      exact M.negativeWordSpan_H_stable i _ (M.negativeWordValue_mem_span u)
    · rw [if_neg hij, LinearMap.zero_apply]
      exact M.negativeWordSpan.zero_mem

theorem negativeWordSpan_E_stable (i : Fin 3) (v : V) (hv : v ∈ M.negativeWordSpan) :
    M.action.E i v ∈ M.negativeWordSpan := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u,rfl⟩ := hv
    exact M.E_negativeWordValue_mem_span i u
  | zero => simp
  | add v w hv hw hiv hiw => simpa only [map_add] using M.negativeWordSpan.add_mem hiv hiw
  | smul c v hv hi => simpa only [map_smul] using M.negativeWordSpan.smul_mem c hi

theorem negativeWordSpan_algebra_stable (a : Module.End K V)
    (ha : a ∈ Algebra.adjoin K (Set.range M.action.E ∪ (Set.range M.action.F ∪ Set.range M.action.H))) :
    ∀ v ∈ M.negativeWordSpan, a v ∈ M.negativeWordSpan := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩
    · exact M.negativeWordSpan_E_stable i
    · exact M.negativeWordSpan_F_stable i
    · exact M.negativeWordSpan_H_stable i
  | algebraMap c => intro v hv; exact M.negativeWordSpan.smul_mem c hv
  | add a b ha hb hia hib => intro v hv; exact M.negativeWordSpan.add_mem (hia v hv) (hib v hv)
  | mul a b ha hb hia hib => intro v hv; exact hia _ (hib v hv)

/-- Highest-weight cyclicity and EF/HF relations force lowering words to span all of V. -/
theorem negativeWordSpan_eq_top : M.negativeWordSpan = ⊤ := by
  apply top_unique
  rw [← M.cyclic]
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,rfl⟩
  exact M.negativeWordSpan_algebra_stable a ha M.highestVector M.highestVector_mem_negativeWordSpan

end KanadeRussell.Representation.PrincipalHighestWeightModule
