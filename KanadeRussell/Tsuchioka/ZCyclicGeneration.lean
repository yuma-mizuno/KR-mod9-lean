import KanadeRussell.Tsuchioka.DegreeOperator

/-! Cyclic generation for the algebra of all concrete root modes, the level
operator and the principal derivation. No affine-module identification is assumed. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

noncomputable def firstCyclicSpan (w : K) (seed : Space K) : Submodule K (Space K) :=
  Submodule.span K (Set.range (fun u : Word => (highestWeightAction w).wordOperator u seed))

theorem firstCyclicSpan_seed (w : K) (seed : Space K) :
    seed ∈ firstCyclicSpan w seed := Submodule.subset_span ⟨[], rfl⟩

theorem firstCyclicSpan_mode_mem (w : K) (seed : Space K) (i : ℤ)
    (f : Space K) (hf : f ∈ firstCyclicSpan w seed) :
    mode w i f ∈ firstCyclicSpan w seed := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    exact Submodule.subset_span ⟨i :: u, rfl⟩
  | zero => simp
  | add f g hf hg hif hig =>
    simpa only [map_add] using (firstCyclicSpan w seed).add_mem hif hig
  | smul c f hf hi =>
    simpa only [map_smul] using (firstCyclicSpan w seed).smul_mem c hi

theorem firstCyclicSpan_degreeOperator_mem (w : K) (seed : Space K) (d : ℤ)
    (hseed : seed ∈ grade d) (f : Space K) (hf : f ∈ firstCyclicSpan w seed) :
    degreeOperator f ∈ firstCyclicSpan w seed := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    rw [degreeOperator_eq_of_grade _ _ (wordOperator_mem_grade w u d seed hseed)]
    exact (firstCyclicSpan w seed).smul_mem _ (Submodule.subset_span ⟨u, rfl⟩)
  | zero => simp
  | add f g hf hg hif hig =>
    simpa only [map_add] using (firstCyclicSpan w seed).add_mem hif hig
  | smul c f hf hi =>
    simpa only [map_smul] using (firstCyclicSpan w seed).smul_mem c hi

noncomputable def centralOperator : Module.End K (Space K) := (3 : K) • LinearMap.id

noncomputable def zGenerators (w : K) : Set (Module.End K (Space K)) :=
  Set.range (fun r : RootData.Root × ℤ => rootMode w r.1.val r.2) ∪
    {centralOperator, principalDerivation}

noncomputable def zOperatorAlgebra (w : K) : Subalgebra K (Module.End K (Space K)) :=
  Algebra.adjoin K (zGenerators w)

noncomputable def zCyclicSpan (w : K) (seed : Space K) : Submodule K (Space K) :=
  Submodule.span K ((fun a : Module.End K (Space K) => a seed) ''
    (zOperatorAlgebra w : Set (Module.End K (Space K))))

/-- Algebra elements act by finite compositions and sums. Root-mode stability
uses the proved pointwise finite elimination, without a uniform operator cutoff. -/
theorem zOperatorAlgebra_preserves_firstCyclicSpan (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (seed : Space K) (d : ℤ) (hseed : seed ∈ grade d)
    (a : Module.End K (Space K)) (ha : a ∈ zOperatorAlgebra w) :
    ∀ f ∈ firstCyclicSpan w seed, a f ∈ firstCyclicSpan w seed := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    intro f hf
    rcases ha with ha | ha
    · obtain ⟨⟨β, i⟩, rfl⟩ := ha
      exact rootMode_mem_of_mode_stable w hw (firstCyclicSpan w seed)
        (firstCyclicSpan_mode_mem w seed) β i f hf
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact (firstCyclicSpan w seed).smul_mem 3 hf
      · exact (firstCyclicSpan w seed).neg_mem
          (firstCyclicSpan_degreeOperator_mem w seed d hseed f hf)
  | algebraMap c =>
    intro f hf
    exact (firstCyclicSpan w seed).smul_mem c hf
  | add a b ha hb hia hib =>
    intro f hf
    exact (firstCyclicSpan w seed).add_mem (hia f hf) (hib f hf)
  | mul a b ha hb hia hib =>
    intro f hf
    exact hia _ (hib f hf)

theorem wordOperator_mem_zOperatorAlgebra (w : K) (u : Word) :
    (highestWeightAction w).wordOperator u ∈ zOperatorAlgebra w := by
  induction u with
  | nil => exact (zOperatorAlgebra w).one_mem
  | cons i u ih =>
    have hm : mode w i ∈ zOperatorAlgebra w := by
      apply Algebra.subset_adjoin
      apply Or.inl
      refine ⟨(RootData.firstRoot, i), ?_⟩
      simp only [RootData.firstRoot_val, rootMode_first]
    exact (zOperatorAlgebra w).mul_mem hm ih

/-- This is the concrete cyclic-generation conclusion of Section 4.1,
including all roots, the central scalar and the affine-sign derivation. -/
theorem zCyclicSpan_eq_firstCyclicSpan (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (seed : Space K) (d : ℤ) (hseed : seed ∈ grade d) :
    zCyclicSpan w seed = firstCyclicSpan w seed := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact zOperatorAlgebra_preserves_firstCyclicSpan w hw seed d hseed a ha seed
      (firstCyclicSpan_seed w seed)
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    exact Submodule.subset_span ⟨(highestWeightAction w).wordOperator u,
      wordOperator_mem_zOperatorAlgebra w u, rfl⟩

end KanadeRussell.Tsuchioka.Fock
