import KanadeRussell.Heisenberg.VacuumSurjection

/-! Nonnegative oscillator gradings supply all finiteness conditions for
vacuum lifting. The conclusion is an equality of images in each graded slice. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Heisenberg
variable {K V W ι : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

structure GradedSystem (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V] where
  annihilate : ι → Module.End K V
  create : ι → Module.End K V
  weight : ι → ℕ
  weight_pos : ∀ i, 0 < weight i
  weight_finite : ∀ N, {i | weight i ≤ N}.Finite
  grade : ℤ → Submodule K V
  negative : ∀ d, d < 0 → grade d = ⊥
  lower : ∀ i d v, v ∈ grade d → annihilate i v ∈ grade (d-weight i)
  raise : ∀ i d v, v ∈ grade d → create i v ∈ grade (d+weight i)
  pair : ∀ i v, annihilate i (create i v) = create i (annihilate i v) + v
  positive_commute : ∀ i j v, annihilate i (annihilate j v) = annihilate j (annihilate i v)
  cross_commute : ∀ i j, i ≠ j → ∀ v, annihilate i (create j v) = create j (annihilate i v)

namespace GradedSystem
variable (G : GradedSystem K V ι)

omit [CharZero K] in
theorem annihilate_pow_mem (i : ι) (r : ℕ) (d : ℤ) (v : V) (hv : v ∈ G.grade d) :
    ((G.annihilate i)^r) v ∈ G.grade (d-(r:ℤ)*G.weight i) := by
  induction r with
  | zero => simpa using hv
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := G.lower i (d-(r:ℤ)*G.weight i) _ ih
    convert h using 1
    congr 1
    push_cast
    ring

omit [CharZero K] in
theorem create_pow_mem (i : ι) (r : ℕ) (d : ℤ) (v : V) (hv : v ∈ G.grade d) :
    ((G.create i)^r) v ∈ G.grade (d+(r:ℤ)*G.weight i) := by
  induction r with
  | zero => simpa using hv
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := G.raise i (d+(r:ℤ)*G.weight i) _ ih
    convert h using 1
    congr 1
    push_cast
    ring

omit [CharZero K] in
theorem balanced_mem (i : ι) (r : ℕ) (d : ℤ) (v : V) (hv : v ∈ G.grade d) :
    ((G.create i)^r) (((G.annihilate i)^r) v) ∈ G.grade d := by
  have h := G.create_pow_mem i r (d-(r:ℤ)*G.weight i) _ (G.annihilate_pow_mem i r d v hv)
  simpa only [sub_add_cancel] using h

omit [CharZero K] in
theorem annihilate_nilpotent (i : ι) (d : ℤ) (v : V) (hv : v ∈ G.grade d) :
    ((G.annihilate i)^(d.toNat+1)) v = 0 := by
  have h := G.annihilate_pow_mem i (d.toNat+1) d v hv
  have hp : (1:ℤ) ≤ G.weight i := by exact_mod_cast G.weight_pos i
  have hd : d < (d.toNat+1:ℕ) := by omega
  have hn : d - ((d.toNat+1:ℕ):ℤ) * G.weight i < 0 := by nlinarith
  rw [G.negative _ hn, Submodule.mem_bot] at h
  exact h

omit [CharZero K] in
theorem annihilate_support_finite (d : ℤ) (v : V) (hv : v ∈ G.grade d) :
    {i | G.annihilate i v ≠ 0}.Finite := by
  apply (G.weight_finite d.toNat).subset
  intro i hi
  change G.weight i ≤ d.toNat
  by_contra h
  have hn : d - G.weight i < 0 := by omega
  have hz := G.lower i d v hv
  rw [G.negative _ hn, Submodule.mem_bot] at hz
  exact hi hz

/-- Grade-by-grade exactness of the vacuum functor for a surjection on that grade. -/
theorem vacuum_grade_map (a' b' : ι → Module.End K W) (f : V →ₗ[K] W)
    (hfa : ∀ i v, f (G.annihilate i v) = a' i (f v))
    (hfb : ∀ i v, f (G.create i v) = b' i (f v))
    (d : ℤ) (T : Submodule K W) (hmap : (G.grade d).map f = T) :
    (G.grade d ⊓ vacuum G.annihilate).map f = T ⊓ vacuum a' := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    constructor
    · rw [← hmap]
      exact ⟨x,hx.1,rfl⟩
    · apply (mem_vacuum a' (f x)).mpr
      intro i
      rw [← hfa, (mem_vacuum G.annihilate x).mp hx.2 i, map_zero]
  · intro y hy
    have hlift : ∃ x ∈ G.grade d, f x = y := by
      have h := hy.1
      rw [← hmap] at h
      exact h
    exact exists_vacuum_lift G.annihilate G.create a' b' f (G.grade d)
      G.pair G.positive_commute G.cross_commute hfa hfb
      (fun i v hv => ⟨d.toNat, G.annihilate_nilpotent i d v hv⟩)
      (fun i r v hv => G.balanced_mem i r d v hv)
      (fun v hv => G.annihilate_support_finite d v hv) y hy.2 hlift

/-- Finite source vacuum grades give finite target vacuum grades. -/
theorem vacuum_grade_finite (a' b' : ι → Module.End K W) (f : V →ₗ[K] W)
    (hfa : ∀ i v, f (G.annihilate i v) = a' i (f v))
    (hfb : ∀ i v, f (G.create i v) = b' i (f v))
    (d : ℤ) (T : Submodule K W) (hmap : (G.grade d).map f = T)
    [Module.Finite K (G.grade d ⊓ vacuum G.annihilate : Submodule K V)] :
    Module.Finite K (T ⊓ vacuum a' : Submodule K W) := by
  rw [← G.vacuum_grade_map a' b' f hfa hfb d T hmap]
  infer_instance

/-- This is the dimension direction required by the product lower bound. -/
theorem finrank_vacuum_grade_le (a' b' : ι → Module.End K W) (f : V →ₗ[K] W)
    (hfa : ∀ i v, f (G.annihilate i v) = a' i (f v))
    (hfb : ∀ i v, f (G.create i v) = b' i (f v))
    (d : ℤ) (T : Submodule K W) (hmap : (G.grade d).map f = T)
    [Module.Finite K (G.grade d ⊓ vacuum G.annihilate : Submodule K V)] :
    Module.finrank K (T ⊓ vacuum a' : Submodule K W) ≤
      Module.finrank K (G.grade d ⊓ vacuum G.annihilate : Submodule K V) := by
  rw [← G.vacuum_grade_map a' b' f hfa hfb d T hmap]
  exact Submodule.finrank_map_le f _

/-- Restrict to an oscillator-stable submodule, without changing degree conventions. -/
noncomputable def restrict (S : Submodule K V)
    (ha : ∀ i v, v ∈ S → G.annihilate i v ∈ S)
    (hb : ∀ i v, v ∈ S → G.create i v ∈ S) : GradedSystem K S ι where
  annihilate i := (G.annihilate i).restrict (ha i)
  create i := (G.create i).restrict (hb i)
  weight := G.weight
  weight_pos := G.weight_pos
  weight_finite := G.weight_finite
  grade d := (G.grade d).comap S.subtype
  negative d hd := by
    ext v
    simp only [Submodule.mem_comap, G.negative d hd, Submodule.mem_bot]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  lower i d v hv := G.lower i d v.val hv
  raise i d v hv := G.raise i d v.val hv
  pair i v := by apply Subtype.ext; exact G.pair i v.val
  positive_commute i j v := by apply Subtype.ext; exact G.positive_commute i j v.val
  cross_commute i j hij v := by apply Subtype.ext; exact G.cross_commute i j hij v.val

omit [CharZero K] in
theorem vacuum_restrict (S : Submodule K V)
    (ha : ∀ i v, v ∈ S → G.annihilate i v ∈ S)
    (hb : ∀ i v, v ∈ S → G.create i v ∈ S) :
    vacuum (G.restrict S ha hb).annihilate = (vacuum G.annihilate).comap S.subtype := by
  ext v
  simp only [mem_vacuum, Submodule.mem_comap]
  constructor
  · intro h i
    exact congrArg Subtype.val (h i)
  · intro h i
    apply Subtype.ext
    exact h i

end GradedSystem
end KanadeRussell.Heisenberg
