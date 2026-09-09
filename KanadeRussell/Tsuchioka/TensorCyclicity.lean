import KanadeRussell.Tsuchioka.ModeDressing

/-! Cyclic spaces for the source tensor root fields. Finite dressing proves
that their Heisenberg vacuum is exactly the Z-cyclic space. No affine
standard-module or character identification is assumed. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

noncomputable def tensorGenerators (w : K) : Set (Module.End K (Space K)) :=
  Set.range (fun r : RootData.Root × ℤ => tensorRootMode w r.1.val r.2) ∪
    {centralOperator, principalDerivation}

noncomputable def tensorOperatorAlgebra (w : K) : Subalgebra K (Module.End K (Space K)) :=
  Algebra.adjoin K (tensorGenerators w ∪
    (Set.range (heisenbergPositive w) ∪ Set.range (heisenbergNegative (K := K))))

theorem tensorRootMode_mem_tensorOperatorAlgebra (w : K) (β : RootData.Root) (i : ℤ) :
    tensorRootMode w β.val i ∈ tensorOperatorAlgebra w :=
  Algebra.subset_adjoin (Or.inl (Or.inl ⟨(β, i), rfl⟩))

theorem heisenbergPositive_mem_tensorOperatorAlgebra (w : K) (n : Mode) :
    heisenbergPositive w n ∈ tensorOperatorAlgebra w :=
  Algebra.subset_adjoin (Or.inr (Or.inl ⟨n, rfl⟩))

theorem heisenbergNegative_mem_tensorOperatorAlgebra (w : K) (n : Mode) :
    heisenbergNegative n ∈ tensorOperatorAlgebra w :=
  Algebra.subset_adjoin (Or.inr (Or.inr ⟨n, rfl⟩))

theorem centralOperator_mem_tensorOperatorAlgebra (w : K) :
    centralOperator ∈ tensorOperatorAlgebra w :=
  Algebra.subset_adjoin (Or.inl (Or.inr (by simp)))

theorem principalDerivation_mem_tensorOperatorAlgebra (w : K) :
    principalDerivation ∈ tensorOperatorAlgebra w :=
  Algebra.subset_adjoin (Or.inl (Or.inr (by simp)))

noncomputable def tensorCyclicSpan (w : K) (seed : Space K) : Submodule K (Space K) :=
  Submodule.span K ((fun a : Module.End K (Space K) => a seed) ''
    (tensorOperatorAlgebra w : Set (Module.End K (Space K))))

theorem tensorCyclicSpan_seed (w : K) (seed : Space K) : seed ∈ tensorCyclicSpan w seed :=
  Submodule.subset_span ⟨1, (tensorOperatorAlgebra w).one_mem, rfl⟩

theorem tensorCyclicSpan_algebra_mem (w : K) (seed : Space K)
    (a : Module.End K (Space K)) (ha : a ∈ tensorOperatorAlgebra w)
    (f : Space K) (hf : f ∈ tensorCyclicSpan w seed) :
    a f ∈ tensorCyclicSpan w seed := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b, hb, rfl⟩ := hf
    exact Submodule.subset_span ⟨a * b, (tensorOperatorAlgebra w).mul_mem ha hb, rfl⟩
  | zero => simp
  | add f g hf hg hif hig => simpa only [map_add] using (tensorCyclicSpan w seed).add_mem hif hig
  | smul c f hf hi => simpa only [map_smul] using (tensorCyclicSpan w seed).smul_mem c hi

theorem heisenbergNegative_mem_tensorCyclicSpan (w : K) (seed : Space K)
    (n : Mode) (f : Space K) (hf : f ∈ tensorCyclicSpan w seed) :
    heisenbergNegative n f ∈ tensorCyclicSpan w seed :=
  tensorCyclicSpan_algebra_mem w seed _ (heisenbergNegative_mem_tensorOperatorAlgebra w n) f hf

theorem tensorRootMode_mem_tensorCyclicSpan (w : K) (seed : Space K)
    (β : RootData.Root) (i : ℤ) (f : Space K) (hf : f ∈ tensorCyclicSpan w seed) :
    tensorRootMode w β.val i f ∈ tensorCyclicSpan w seed :=
  tensorCyclicSpan_algebra_mem w seed _ (tensorRootMode_mem_tensorOperatorAlgebra w β i) f hf

theorem principalDerivation_mem_tensorCyclicSpan (w : K) (seed : Space K)
    (f : Space K) (hf : f ∈ tensorCyclicSpan w seed) :
    principalDerivation f ∈ tensorCyclicSpan w seed :=
  tensorCyclicSpan_algebra_mem w seed _ (principalDerivation_mem_tensorOperatorAlgebra w) f hf

/-- Inverse dressing proves Z stability of the actual tensor cyclic vacuum. -/
theorem rootMode_mem_tensorCyclicVacuum (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (seed : Space K) (β : RootData.Root) (i : ℤ) (f : Space K)
    (hf : f ∈ tensorCyclicSpan w seed ⊓ heisenbergVacuum w) :
    rootMode w β.val i f ∈ tensorCyclicSpan w seed ⊓ heisenbergVacuum w := by
  constructor
  · exact rootMode_mem_of_tensorRootModes w hw β.val (tensorCyclicSpan w seed)
      (heisenbergNegative_mem_tensorCyclicSpan w seed) f hf.2
      (fun j => tensorRootMode_mem_tensorCyclicSpan w seed β j f hf.1) i
  · exact rootMode_mem_heisenbergVacuum w β.val i f hf.2

theorem zOperatorAlgebra_preserves_tensorCyclicVacuum (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (seed : Space K)
    (a : Module.End K (Space K)) (ha : a ∈ zOperatorAlgebra w) :
    ∀ f ∈ tensorCyclicSpan w seed ⊓ heisenbergVacuum w,
      a f ∈ tensorCyclicSpan w seed ⊓ heisenbergVacuum w := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    intro f hf
    rcases ha with hr | hd
    · obtain ⟨⟨β, i⟩, rfl⟩ := hr
      exact rootMode_mem_tensorCyclicVacuum w hw seed β i f hf
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl
      · exact (tensorCyclicSpan w seed ⊓ heisenbergVacuum w).smul_mem 3 hf
      · exact ⟨principalDerivation_mem_tensorCyclicSpan w seed f hf.1,
          principalDerivation_mem_heisenbergVacuum w f hf.2⟩
  | algebraMap c =>
    intro f hf
    exact (tensorCyclicSpan w seed ⊓ heisenbergVacuum w).smul_mem c hf
  | add a b ha hb hia hib =>
    intro f hf
    exact (tensorCyclicSpan w seed ⊓ heisenbergVacuum w).add_mem (hia f hf) (hib f hf)
  | mul a b ha hb hia hib =>
    intro f hf
    exact hia _ (hib f hf)

theorem zCyclicSpan_le_tensorCyclicVacuum (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (seed : Space K) (hseed : seed ∈ heisenbergVacuum w) :
    zCyclicSpan w seed ≤ tensorCyclicSpan w seed ⊓ heisenbergVacuum w := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  exact zOperatorAlgebra_preserves_tensorCyclicVacuum w hw seed a ha seed
    ⟨tensorCyclicSpan_seed w seed, hseed⟩

theorem tensorOperatorAlgebra_preserves_heisenbergSpan (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (seed : Space K) (hseed : seed ∈ heisenbergVacuum w)
    (a : Module.End K (Space K)) (ha : a ∈ tensorOperatorAlgebra w) :
    ∀ f ∈ heisenbergSpan (zCyclicSpan w seed),
      a f ∈ heisenbergSpan (zCyclicSpan w seed) := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    intro f hf
    rcases ha with hx | hp | hn
    · rcases hx with hx | hd
      · obtain ⟨⟨β, i⟩, rfl⟩ := hx
        exact tensorRootMode_mem_heisenbergSpan_zCyclicSpan w hw seed hseed β i f hf
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
        rcases hd with rfl | rfl
        · exact (heisenbergSpan (zCyclicSpan w seed)).smul_mem 3 hf
        · exact (heisenbergSpan (zCyclicSpan w seed)).neg_mem
            (degreeOperator_mem_heisenbergSpan (zCyclicSpan w seed)
              (degreeOperator_mem_zCyclicSpan w seed) f hf)
    · obtain ⟨n, rfl⟩ := hp
      exact heisenbergPositive_mem_span w (zCyclicSpan w seed)
        (zCyclicSpan_le_heisenbergVacuum w seed hseed) n f hf
    · obtain ⟨n, rfl⟩ := hn
      exact heisenbergNegative_mem_span (zCyclicSpan w seed) n f hf
  | algebraMap c =>
    intro f hf
    exact (heisenbergSpan (zCyclicSpan w seed)).smul_mem c hf
  | add a b ha hb hia hib =>
    intro f hf
    exact (heisenbergSpan (zCyclicSpan w seed)).add_mem (hia f hf) (hib f hf)
  | mul a b ha hb hia hib =>
    intro f hf
    exact hia _ (hib f hf)

/-- The source tensor fields generate precisely the negative-Heisenberg
span of the Z-cyclic space, from every vacuum seed. -/
theorem tensorCyclicSpan_eq_heisenbergSpan (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (seed : Space K) (hseed : seed ∈ heisenbergVacuum w) :
    tensorCyclicSpan w seed = heisenbergSpan (zCyclicSpan w seed) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact tensorOperatorAlgebra_preserves_heisenbergSpan w hw seed hseed a ha seed
      (le_heisenbergSpan _ (zCyclicSpan_seed w seed))
  · apply heisenbergSpan_le
    · exact le_trans (zCyclicSpan_le_tensorCyclicVacuum w hw seed hseed) inf_le_left
    · exact heisenbergNegative_mem_tensorCyclicSpan w seed

theorem tensorCyclicSpan_eq_oscillatorZCyclicSpan (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (seed : Space K) (hseed : seed ∈ heisenbergVacuum w) :
    tensorCyclicSpan w seed = oscillatorZCyclicSpan w seed := by
  rw [tensorCyclicSpan_eq_heisenbergSpan w hw seed hseed,
    oscillatorZCyclicSpan_eq_heisenbergSpan w seed hseed]

/-- This establishes vacuum cyclicity for the explicitly constructed tensor
root action, rather than assuming a Z-cyclicity input. -/
theorem tensorCyclicSpan_inf_vacuum_eq_zCyclicSpan (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (seed : Space K) (hseed : seed ∈ heisenbergVacuum w) :
    tensorCyclicSpan w seed ⊓ heisenbergVacuum w = zCyclicSpan w seed := by
  rw [tensorCyclicSpan_eq_heisenbergSpan w hw seed hseed]
  exact heisenbergSpan_inf_vacuum_eq w hw _ (zCyclicSpan_le_heisenbergVacuum w seed hseed)

theorem tensorCyclicSpan_vacuum_grade_eq_cyclicGrade (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : ℕ) :
    (tensorCyclicSpan w 1 ⊓ heisenbergVacuum w) ⊓ grade (n : ℤ) =
      Partitions.cyclicGrade (highestWeightAction w) n := by
  rw [tensorCyclicSpan_inf_vacuum_eq_zCyclicSpan w hw 1 (one_mem_heisenbergVacuum w),
    zCyclicSpan_vacuum_inf_grade_eq_cyclicGrade w hw]

theorem tensorCyclicSpan_vacuum_grade_finite (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : ℕ) :
    Module.Finite K ↥((tensorCyclicSpan w 1 ⊓ heisenbergVacuum w) ⊓
      grade (n : ℤ) : Submodule K (Space K)) := by
  rw [tensorCyclicSpan_vacuum_grade_eq_cyclicGrade w hw n]
  exact KanadeRussell.Straightening.fock_cyclicGrade_finite w hw n

theorem finrank_tensorCyclicSpan_vacuum_grade_le_count (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : ℕ) :
    Module.finrank K ↥((tensorCyclicSpan w 1 ⊓ heisenbergVacuum w) ⊓
      grade (n : ℤ) : Submodule K (Space K)) ≤ Partitions.count 2 n := by
  rw [tensorCyclicSpan_vacuum_grade_eq_cyclicGrade w hw n]
  exact KanadeRussell.Straightening.fock_finrank_le_count w hw n

end KanadeRussell.Tsuchioka.Fock
