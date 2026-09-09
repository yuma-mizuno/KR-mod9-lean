import KanadeRussell.Heisenberg.FiniteProjection

/-! Vacuum lifting through surjections of restricted oscillator representations.
The construction uses finite Taylor projections, not an assumed exactness theorem.
The balanced-power condition allows lifting inside one specified graded slice. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Heisenberg
variable {K V W ι : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

noncomputable def vacuum (a : ι → Module.End K V) : Submodule K V :=
  ⨅ i, LinearMap.ker (a i)

omit [CharZero K] in
theorem mem_vacuum (a : ι → Module.End K V) (v : V) :
    v ∈ vacuum a ↔ ∀ i, a i v = 0 := by
  simp only [vacuum, Submodule.mem_iInf, LinearMap.mem_ker]

/-- Correct finitely many annihilators, preserving every kernel already satisfied. -/
theorem finite_vacuum_lift
    (a b : ι → Module.End K V) (a' b' : ι → Module.End K W)
    (f : V →ₗ[K] W) (S : Submodule K V)
    (hab : ∀ i v, a i (b i v) = b i (a i v) + v)
    (haa : ∀ i j v, a i (a j v) = a j (a i v))
    (hab' : ∀ i j, i ≠ j → ∀ v, a i (b j v) = b j (a i v))
    (hfa : ∀ i v, f (a i v) = a' i (f v))
    (hfb : ∀ i v, f (b i v) = b' i (f v))
    (hnil : ∀ i v, v ∈ S → ∃ n : ℕ, ((a i)^(n+1)) v = 0)
    (hS : ∀ i r v, v ∈ S → ((b i)^r) (((a i)^r) v) ∈ S)
    (s : Finset ι) (y : W) (hy : ∀ i, a' i y = 0)
    (x : V) (hx : x ∈ S) (hxy : f x = y) :
    ∃ v ∈ S, f v = y ∧ ∀ i, i ∈ s ∨ a i x = 0 → a i v = 0 := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    refine ⟨x, hx, hxy, ?_⟩
    intro i hi
    simpa using hi
  | @insert j s hj ih =>
    obtain ⟨n, hn⟩ := hnil j x hx
    let z := projection (a j) (b j) n x
    have hzS : z ∈ S := projection_mem (a j) (b j) S x hx (fun r => hS j r x hx) n
    have hzy : f z = y := by
      rw [projection_natural f (a j) (b j) (a' j) (b' j) (hfa j) (hfb j), hxy]
      exact projection_fixed (a' j) (b' j) n y (hy j)
    have hjz : a j z = 0 := projection_mem_ker (a j) (b j) (hab j) n x hn
    obtain ⟨v,hv,hvy,hvker⟩ := ih z hzS hzy
    refine ⟨v,hv,hvy,?_⟩
    intro i hi
    by_cases hij : i = j
    · subst i
      exact hvker j (Or.inr hjz)
    · apply hvker i
      rcases hi with hi | hi
      · exact Or.inl ((Finset.mem_insert.mp hi).resolve_left hij)
      · exact Or.inr (projection_preserves_ker (a j) (b j) (a i)
          (haa i j) (hab' i j hij) n x hi)

/-- Lift any target vacuum in a specified subspace of the source.
Only finitely many annihilators act on a chosen lift; each is locally nilpotent. -/
theorem exists_vacuum_lift
    (a b : ι → Module.End K V) (a' b' : ι → Module.End K W)
    (f : V →ₗ[K] W) (S : Submodule K V)
    (hab : ∀ i v, a i (b i v) = b i (a i v) + v)
    (haa : ∀ i j v, a i (a j v) = a j (a i v))
    (hab' : ∀ i j, i ≠ j → ∀ v, a i (b j v) = b j (a i v))
    (hfa : ∀ i v, f (a i v) = a' i (f v))
    (hfb : ∀ i v, f (b i v) = b' i (f v))
    (hnil : ∀ i v, v ∈ S → ∃ n : ℕ, ((a i)^(n+1)) v = 0)
    (hS : ∀ i r v, v ∈ S → ((b i)^r) (((a i)^r) v) ∈ S)
    (hfin : ∀ v ∈ S, {i | a i v ≠ 0}.Finite)
    (y : W) (hy : y ∈ vacuum a') (hlift : ∃ x ∈ S, f x = y) :
    ∃ v ∈ S ⊓ vacuum a, f v = y := by
  classical
  obtain ⟨x,hx,hxy⟩ := hlift
  have hfinite := hfin x hx
  obtain ⟨v,hv,hvy,hker⟩ := finite_vacuum_lift a b a' b' f S hab haa hab' hfa hfb hnil hS
    hfinite.toFinset y ((mem_vacuum a' y).mp hy) x hx hxy
  refine ⟨v,⟨hv, (mem_vacuum a v).mpr ?_⟩,hvy⟩
  intro i
  by_cases hi : a i x = 0
  · exact hker i (Or.inr hi)
  · exact hker i (Or.inl (by simpa using hi))

/-- A surjection restricts to a surjection between the two common kernels. -/
theorem vacuum_map_eq_of_surjective
    (a b : ι → Module.End K V) (a' b' : ι → Module.End K W)
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    (hab : ∀ i v, a i (b i v) = b i (a i v) + v)
    (haa : ∀ i j v, a i (a j v) = a j (a i v))
    (hab' : ∀ i j, i ≠ j → ∀ v, a i (b j v) = b j (a i v))
    (hfa : ∀ i v, f (a i v) = a' i (f v))
    (hfb : ∀ i v, f (b i v) = b' i (f v))
    (hnil : ∀ i v, ∃ n : ℕ, ((a i)^(n+1)) v = 0)
    (hfin : ∀ v, {i | a i v ≠ 0}.Finite) :
    (vacuum a).map f = vacuum a' := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    apply (mem_vacuum a' (f x)).mpr
    intro i
    rw [← hfa, (mem_vacuum a x).mp hx i, map_zero]
  · intro y hy
    obtain ⟨v,hv,hvy⟩ := exists_vacuum_lift a b a' b' f ⊤ hab haa hab' hfa hfb
      (fun i v _ => hnil i v) (fun _ _ _ _ => Submodule.mem_top)
      (fun v _ => hfin v) y hy (by obtain ⟨x,hx⟩ := hf y; exact ⟨x,Submodule.mem_top,hx⟩)
    exact ⟨v,hv.2,hvy⟩

end KanadeRussell.Heisenberg
