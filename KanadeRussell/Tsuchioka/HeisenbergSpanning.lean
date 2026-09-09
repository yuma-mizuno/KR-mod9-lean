import KanadeRussell.Tsuchioka.VacuumProjection
import KanadeRussell.Tsuchioka.HeisenbergCyclicSpace

/-! Finite spans of negative Heisenberg words, their operator stability,
and recovery of the original vacuum subspace by the vacuum projection. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

noncomputable def heisenbergWord : List Mode → Module.End K (Space K)
  | [] => LinearMap.id
  | n :: u => (heisenbergNegative n).comp (heisenbergWord u)

@[simp] theorem heisenbergWord_nil (f : Space K) : heisenbergWord [] f = f := rfl

@[simp] theorem heisenbergWord_cons (n : Mode) (u : List Mode) (f : Space K) :
    heisenbergWord (n :: u) f = heisenbergNegative n (heisenbergWord u f) := rfl

noncomputable def heisenbergSpan (S : Submodule K (Space K)) : Submodule K (Space K) :=
  Submodule.span K (Set.range (fun us : List Mode × S => heisenbergWord us.1 us.2.val))

theorem heisenbergWord_mem_span (S : Submodule K (Space K))
    (u : List Mode) (f : Space K) (hf : f ∈ S) :
    heisenbergWord u f ∈ heisenbergSpan S :=
  Submodule.subset_span ⟨(u, ⟨f, hf⟩), rfl⟩

theorem le_heisenbergSpan (S : Submodule K (Space K)) : S ≤ heisenbergSpan S := by
  intro f hf
  exact heisenbergWord_mem_span S [] f hf

theorem heisenbergSpan_mono {S T : Submodule K (Space K)} (hST : S ≤ T) :
    heisenbergSpan S ≤ heisenbergSpan T := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, f⟩, rfl⟩
  exact heisenbergWord_mem_span T u f.val (hST f.property)

theorem heisenbergNegative_mem_span (S : Submodule K (Space K))
    (n : Mode) (f : Space K) (hf : f ∈ heisenbergSpan S) :
    heisenbergNegative n f ∈ heisenbergSpan S := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨u, s⟩, rfl⟩ := hf
    dsimp only
    exact heisenbergWord_mem_span S (n :: u) s.val s.property
  | zero => simp
  | add f g hf hg hif hig =>
    simpa only [map_add] using (heisenbergSpan S).add_mem hif hig
  | smul c f hf hi =>
    simpa only [map_smul] using (heisenbergSpan S).smul_mem c hi

theorem heisenbergSpan_le (S T : Submodule K (Space K)) (hST : S ≤ T)
    (hT : ∀ n f, f ∈ T → heisenbergNegative n f ∈ T) :
    heisenbergSpan S ≤ T := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, f⟩, rfl⟩
  induction u with
  | nil => exact hST f.property
  | cons n u ih => exact hT n _ ih

theorem centerProjection_heisenbergWord_cons (n : Mode) (u : List Mode) (f : Space K) :
    centerProjection (heisenbergWord (n :: u) f) = 0 :=
  centerProjection_heisenbergNegative n _

theorem centerProjection_mem_of_heisenbergSpan (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (S : Submodule K (Space K)) (hS : S ≤ heisenbergVacuum w)
    (f : Space K) (hf : f ∈ heisenbergSpan S) :
    centerProjection f ∈ S := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨u, s⟩, rfl⟩ := hf
    dsimp only
    cases u with
    | nil =>
      rw [heisenbergWord_nil,
        centerProjection_eq_self_of_mem_heisenbergVacuum w hw s.val (hS s.property)]
      exact s.property
    | cons n u => rw [centerProjection_heisenbergWord_cons]; exact S.zero_mem
  | zero => simp
  | add f g hf hg hif hig => simpa only [map_add] using S.add_mem hif hig
  | smul c f hf hi => simpa only [map_smul] using S.smul_mem c hi

/-- Adding negative Heisenberg modes creates no new vacuum vectors. -/
theorem heisenbergSpan_inf_vacuum_eq (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (S : Submodule K (Space K)) (hS : S ≤ heisenbergVacuum w) :
    heisenbergSpan S ⊓ heisenbergVacuum w = S := by
  apply le_antisymm
  · intro f hf
    have h := centerProjection_mem_of_heisenbergSpan w hw S hS f hf.1
    rwa [centerProjection_eq_self_of_mem_heisenbergVacuum w hw f hf.2] at h
  · intro f hf
    exact ⟨le_heisenbergSpan S hf, hS hf⟩

theorem heisenbergPositive_mem_span (w : K) (S : Submodule K (Space K))
    (hS : S ≤ heisenbergVacuum w) (n : Mode)
    (f : Space K) (hf : f ∈ heisenbergSpan S) :
    heisenbergPositive w n f ∈ heisenbergSpan S := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨u, s⟩, rfl⟩ := hf
    dsimp only
    induction u with
    | nil =>
      rw [heisenbergWord_nil, (mem_heisenbergVacuum w s.val).mp (hS s.property) n]
      exact (heisenbergSpan S).zero_mem
    | cons m u ih =>
      rw [heisenbergWord_cons,
        sub_eq_iff_eq_add.mp (heisenberg_mixed_commutator w n m (heisenbergWord u s.val))]
      apply (heisenbergSpan S).add_mem
      · split_ifs
        · exact (heisenbergSpan S).smul_mem _ ((heisenbergSpan S).smul_mem _
            (heisenbergWord_mem_span S u s.val s.property))
        · exact (heisenbergSpan S).zero_mem
      · exact heisenbergNegative_mem_span S m _ ih
  | zero => simp
  | add f g hf hg hif hig =>
    simpa only [map_add] using (heisenbergSpan S).add_mem hif hig
  | smul c f hf hi =>
    simpa only [map_smul] using (heisenbergSpan S).smul_mem c hi

theorem rootMode_heisenbergWord (w : K) (β : RootData.Lattice) (i : ℤ)
    (u : List Mode) (f : Space K) :
    rootMode w β i (heisenbergWord u f) = heisenbergWord u (rootMode w β i f) := by
  induction u with
  | nil => rfl
  | cons n u ih =>
    rw [heisenbergWord_cons, ← heisenbergNegative_rootMode, ih, heisenbergWord_cons]

theorem rootMode_mem_heisenbergSpan (w : K) (β : RootData.Lattice) (i : ℤ)
    (S : Submodule K (Space K)) (hS : ∀ f ∈ S, rootMode w β i f ∈ S)
    (f : Space K) (hf : f ∈ heisenbergSpan S) :
    rootMode w β i f ∈ heisenbergSpan S := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨u, s⟩, rfl⟩ := hf
    dsimp only
    rw [rootMode_heisenbergWord]
    exact heisenbergWord_mem_span S u _ (hS s.val s.property)
  | zero => simp
  | add f g hf hg hif hig =>
    simpa only [map_add] using (heisenbergSpan S).add_mem hif hig
  | smul c f hf hi =>
    simpa only [map_smul] using (heisenbergSpan S).smul_mem c hi

theorem degreeOperator_diagonalCoordinate (n : Mode) :
    degreeOperator (diagonalCoordinate (K := K) n) =
      (n.val : K) • diagonalCoordinate n := by
  simp only [diagonalCoordinate, map_sum, degreeOperator_X, ← Finset.smul_sum]

theorem degreeOperator_heisenbergNegative (n : Mode) (f : Space K) :
    degreeOperator (heisenbergNegative n f) =
      (n.val : K) • heisenbergNegative n f + heisenbergNegative n (degreeOperator f) := by
  simp only [heisenbergNegative_apply, degreeOperator_mul,
    degreeOperator_diagonalCoordinate, smul_mul_assoc]

theorem degreeOperator_mem_heisenbergSpan (S : Submodule K (Space K))
    (hS : ∀ f ∈ S, degreeOperator f ∈ S)
    (f : Space K) (hf : f ∈ heisenbergSpan S) :
    degreeOperator f ∈ heisenbergSpan S := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨u, s⟩, rfl⟩ := hf
    dsimp only
    induction u with
    | nil => exact le_heisenbergSpan S (hS s.val s.property)
    | cons n u ih =>
      rw [heisenbergWord_cons, degreeOperator_heisenbergNegative]
      exact (heisenbergSpan S).add_mem
        ((heisenbergSpan S).smul_mem _ (heisenbergWord_mem_span S (n :: u) s.val s.property))
        (heisenbergNegative_mem_span S n _ ih)
  | zero => simp
  | add f g hf hg hif hig =>
    simpa only [map_add] using (heisenbergSpan S).add_mem hif hig
  | smul c f hf hi =>
    simpa only [map_smul] using (heisenbergSpan S).smul_mem c hi

end KanadeRussell.Tsuchioka.Fock
