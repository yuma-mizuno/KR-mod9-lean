import KanadeRussell.Heisenberg.GradedVacuum

/-! Restrict a graded oscillator system to the common kernels of finitely many
annihilators. The remaining oscillator pairs act on this subspace. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Heisenberg.GradedSystem
variable {K V ι : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V]
variable (G : GradedSystem K V ι)

noncomputable def finiteVacuum (s : Finset ι) : Submodule K V :=
  ⨅ i ∈ s, LinearMap.ker (G.annihilate i)

@[simp] theorem mem_finiteVacuum (s : Finset ι) (v : V) :
    v ∈ G.finiteVacuum s ↔ ∀ i ∈ s, G.annihilate i v = 0 := by
  simp only [finiteVacuum, Submodule.mem_iInf, LinearMap.mem_ker]

@[simp] theorem finiteVacuum_empty : G.finiteVacuum ∅ = ⊤ := by
  ext v
  simp

theorem finiteVacuum_insert [DecidableEq ι] (i : ι) (s : Finset ι) :
    G.finiteVacuum (insert i s) = G.finiteVacuum s ⊓ LinearMap.ker (G.annihilate i) := by
  ext v
  simp only [mem_finiteVacuum, Finset.mem_insert, forall_eq_or_imp,
    Submodule.mem_inf, LinearMap.mem_ker]
  exact and_comm

theorem annihilate_mem_finiteVacuum (s : Finset ι) (i : ι) (v : V)
    (hv : v ∈ G.finiteVacuum s) : G.annihilate i v ∈ G.finiteVacuum s := by
  rw [mem_finiteVacuum] at hv ⊢
  intro j hj
  rw [G.positive_commute, hv j hj, map_zero]

theorem create_mem_finiteVacuum (s : Finset ι) (i : ι) (hi : i ∉ s) (v : V)
    (hv : v ∈ G.finiteVacuum s) : G.create i v ∈ G.finiteVacuum s := by
  rw [mem_finiteVacuum] at hv ⊢
  intro j hj
  have hji : j ≠ i := by rintro rfl; exact hi hj
  rw [G.cross_commute j i hji, hv j hj, map_zero]

noncomputable def awayFrom (s : Finset ι) :
    GradedSystem K (G.finiteVacuum s) {i : ι // i ∉ s} where
  annihilate i := (G.annihilate i.val).restrict (G.annihilate_mem_finiteVacuum s i.val)
  create i := (G.create i.val).restrict (G.create_mem_finiteVacuum s i.val i.property)
  weight i := G.weight i.val
  weight_pos i := G.weight_pos i.val
  weight_finite N := (G.weight_finite N).preimage
    (Set.injOn_of_injective Subtype.val_injective)
  grade d := (G.grade d).comap (G.finiteVacuum s).subtype
  negative d hd := by
    ext v
    simp only [Submodule.mem_comap, G.negative d hd, Submodule.mem_bot]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  lower i d v hv := G.lower i.val d v.val hv
  raise i d v hv := G.raise i.val d v.val hv
  pair i v := by apply Subtype.ext; exact G.pair i.val v.val
  positive_commute i j v := by apply Subtype.ext; exact G.positive_commute i.val j.val v.val
  cross_commute i j hij v := by
    apply Subtype.ext
    exact G.cross_commute i.val j.val (fun h => hij (Subtype.ext h)) v.val

theorem awayFrom_grade_map (s : Finset ι) (d : ℤ) :
    ((G.awayFrom s).grade d).map (G.finiteVacuum s).subtype =
      G.grade d ⊓ G.finiteVacuum s := by
  change ((G.grade d).comap (G.finiteVacuum s).subtype).map _ = _
  rw [Submodule.map_comap_subtype, inf_comm]

theorem awayFrom_grade_finrank (s : Finset ι) (d : ℤ) :
    Module.finrank K ((G.awayFrom s).grade d) =
      Module.finrank K (G.grade d ⊓ G.finiteVacuum s : Submodule K V) := by
  rw [← G.awayFrom_grade_map, Submodule.finrank_map_subtype_eq]

theorem awayFrom_grade_finite (s : Finset ι) (d : ℤ) [Module.Finite K (G.grade d)] :
    Module.Finite K ((G.awayFrom s).grade d) := by
  let f : (G.awayFrom s).grade d →ₗ[K] G.grade d :=
    { toFun := fun v => ⟨v.val.val, v.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact Module.Finite.of_injective f (by
    intro v u h
    apply Subtype.ext
    apply Subtype.ext
    simpa [f] using congrArg (fun x : G.grade d => (x : V)) h)

theorem awayFrom_grade_ker_map [DecidableEq ι] (s : Finset ι)
    (i : {i : ι // i ∉ s}) (d : ℤ) :
    (((G.awayFrom s).grade d ⊓ LinearMap.ker ((G.awayFrom s).annihilate i)).map
      (G.finiteVacuum s).subtype) = G.grade d ⊓ G.finiteVacuum (insert i.val s) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨hu.1, ?_⟩
    rw [G.finiteVacuum_insert]
    exact ⟨u.property, congrArg Subtype.val hu.2⟩
  · intro hv
    rw [G.finiteVacuum_insert] at hv
    refine ⟨⟨v, hv.2.1⟩, ⟨hv.1, ?_⟩, rfl⟩
    apply Subtype.ext
    exact hv.2.2

theorem awayFrom_grade_ker_finrank [DecidableEq ι] (s : Finset ι)
    (i : {i : ι // i ∉ s}) (d : ℤ) :
    Module.finrank K ((G.awayFrom s).grade d ⊓
      LinearMap.ker ((G.awayFrom s).annihilate i) : Submodule K (G.finiteVacuum s)) =
      Module.finrank K (G.grade d ⊓ G.finiteVacuum (insert i.val s) : Submodule K V) := by
  rw [← G.awayFrom_grade_ker_map, Submodule.finrank_map_subtype_eq]

theorem finiteVacuum_grade_eq_vacuum (s : Finset ι) (d : ℤ)
    (hs : ∀ i, (G.weight i : ℤ) ≤ d → i ∈ s) :
    G.grade d ⊓ G.finiteVacuum s = G.grade d ⊓ vacuum G.annihilate := by
  ext v
  constructor
  · intro hv
    refine ⟨hv.1, (mem_vacuum _ _).mpr ?_⟩
    intro i
    by_cases hi : (G.weight i : ℤ) ≤ d
    · exact (G.mem_finiteVacuum s v).mp hv.2 i (hs i hi)
    · have h := G.lower i d v hv.1
      rw [G.negative _ (by omega), Submodule.mem_bot] at h
      exact h
  · intro hv
    exact ⟨hv.1, (G.mem_finiteVacuum s v).mpr (fun i _ => (mem_vacuum _ _).mp hv.2 i)⟩

end KanadeRussell.Heisenberg.GradedSystem
