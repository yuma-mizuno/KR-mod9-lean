import KanadeRussell.Tsuchioka.RootOrbits
import KanadeRussell.Tsuchioka.RootGeneration
import KanadeRussell.Tsuchioka.AnnihilationCovariance

/-! Homogeneous generation for the modes of every D4 root. The exhaustive
lattice classification discharges the two-orbit reduction used in Section 4.1. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

/-- A root determines one of the two root families and one phase, uniformly
for every mode index. -/
theorem rootMode_orbit (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (β : RootData.Root) :
    ∃ r : Fin 2, ∃ p : Fin 12, ∀ i : ℤ,
      rootMode w β.val i = w ^ ((p.val : ℤ) * i) •
        (if r = 0 then mode w i else secondRootMode w i) := by
  obtain ⟨r, p, hp⟩ := RootData.isRoot_mem_orbits β.val β.property
  refine ⟨r, p, ?_⟩
  intro i
  apply LinearMap.ext
  intro f
  simp only [hp, RootData.orbitRoot, rootMode_iterate w hw, LinearMap.smul_apply]
  fin_cases r <;> simp [RootData.orbitRepresentative, rootMode_first, secondRootMode]

theorem rootMode_mem_of_graded_mode_stable (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (S : ℤ → Submodule K (Space K))
    (hstable : ∀ i d : ℤ, ∀ f ∈ S d, mode w i f ∈ S (i + d))
    (β : RootData.Root) (i d : ℤ) (f : Space K) (hf : f ∈ S d) :
    rootMode w β.val i f ∈ S (i + d) := by
  obtain ⟨r, p, hp⟩ := rootMode_orbit w hw β
  rw [hp i, LinearMap.smul_apply]
  apply Submodule.smul_mem
  split_ifs
  · exact hstable i d f hf
  · exact secondRootMode_mem_of_graded_mode_stable w hw S hstable i d f hf

theorem rootMode_mem_of_mode_stable (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (S : Submodule K (Space K))
    (hstable : ∀ i : ℤ, ∀ f ∈ S, mode w i f ∈ S)
    (β : RootData.Root) (i : ℤ) (f : Space K) (hf : f ∈ S) :
    rootMode w β.val i f ∈ S :=
  rootMode_mem_of_graded_mode_stable w hw (fun _ => S)
    (fun i _ f hf => hstable i f hf) β i 0 f hf

theorem rootMode_mem_grade (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : RootData.Root) (i d : ℤ) (f : Space K) (hf : f ∈ grade d) :
    rootMode w β.val i f ∈ grade (d - i) := by
  have hstable : ∀ j e : ℤ, ∀ p ∈ grade (d - e),
      mode w j p ∈ grade (d - (j + e)) := by
    intro j e p hp
    convert mode_mem_grade w j (d - e) p hp using 1 <;> congr 1 <;> ring
  simpa only [add_zero, sub_zero] using
    rootMode_mem_of_graded_mode_stable w hw (fun e => grade (d - e)) hstable β i 0 f
      (by simpa only [sub_zero] using hf)

theorem firstWordSpan_rootMode_mem (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (seed : Space K) (β : RootData.Root) (i d : ℤ)
    (f : Space K) (hf : f ∈ firstWordSpan w seed d) :
    rootMode w β.val i f ∈ firstWordSpan w seed (i + d) :=
  rootMode_mem_of_graded_mode_stable w hw (firstWordSpan w seed)
    (firstWordSpan_mode_mem w seed) β i d f hf

theorem rootMode_mem_length_two (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : RootData.Root) (i : ℤ) (f : Space K) :
    rootMode w β.val i f ∈ Submodule.span K
      ((fun u : Word => (highestWeightAction w).wordOperator u f) ''
        {u | u.length ≤ 2 ∧ u.sum = i}) := by
  obtain ⟨r, p, hp⟩ := rootMode_orbit w hw β
  rw [hp i, LinearMap.smul_apply]
  apply Submodule.smul_mem
  split_ifs
  · exact Submodule.subset_span ⟨[i], ⟨by simp, by simp⟩, rfl⟩
  · exact secondRootMode_mem_length_two w hw i f

noncomputable def allRootWordOperator (w : K) :
    List (RootData.Root × ℤ) → Module.End K (Space K)
  | [] => LinearMap.id
  | r :: u => (rootMode w r.1.val r.2).comp (allRootWordOperator w u)

noncomputable def allRootWordSpan (w : K) (f : Space K) (d : ℤ) : Submodule K (Space K) :=
  Submodule.span K ((fun u : List (RootData.Root × ℤ) => allRootWordOperator w u f) ''
    {u | (u.map Prod.snd).sum = d})

theorem allRootWord_mem_firstWordSpan (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (u : List (RootData.Root × ℤ)) :
    allRootWordOperator w u f ∈ firstWordSpan w f (u.map Prod.snd).sum := by
  induction u with
  | nil => exact firstWordSpan_seed w f
  | cons r u ih =>
    exact firstWordSpan_rootMode_mem w hw f r.1 r.2 _ _ ih

theorem allRootWordOperator_first (w : K) (u : Word) :
    allRootWordOperator w (u.map (fun i => (RootData.firstRoot, i))) =
      (highestWeightAction w).wordOperator u := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    simp only [List.map_cons, allRootWordOperator, RootData.firstRoot_val,
      rootMode_first, ih, HighestWeightAction.wordOperator]
    rfl

/-- Every root is included, and equality holds in each total mode index. -/
theorem allRootWordSpan_eq_firstWordSpan (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (d : ℤ) : allRootWordSpan w f d = firstWordSpan w f d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    change (u.map Prod.snd).sum = d at hu
    change allRootWordOperator w u f ∈ firstWordSpan w f d
    rw [← hu]
    exact allRootWord_mem_firstWordSpan w hw f u
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    change u.sum = d at hu
    apply Submodule.subset_span
    refine ⟨u.map (fun i => (RootData.firstRoot, i)), ?_, ?_⟩
    · change ((u.map (fun i => (RootData.firstRoot, i))).map Prod.snd).sum = d
      rw [List.map_map]
      change (u.map id).sum = d
      rw [List.map_id]
      exact hu
    · dsimp only
      rw [allRootWordOperator_first]

end KanadeRussell.Tsuchioka.Fock
