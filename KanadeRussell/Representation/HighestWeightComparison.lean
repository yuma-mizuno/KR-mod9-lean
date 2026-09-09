import KanadeRussell.Representation.ChevalleyIrreducibility
import KanadeRussell.Representation.PairedHighestWeightSpan

/-! Uniqueness of irreducible highest-weight modules with the same highest
weight, via their actual paired lowering words. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
attribute [local instance] LieRing.ofAssociativeRing
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

private theorem fst_injective_of_irreducible (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (S : Submodule K (V×W))
    (hN : N.action.IsIrreducible)
    (hE : ∀ i p, p∈S → (M.action.E i p.1,N.action.E i p.2)∈S)
    (hF : ∀ i p, p∈S → (M.action.F i p.1,N.action.F i p.2)∈S)
    (hhighest : (0,N.highestVector) ∉ S) :
    Function.Injective ((LinearMap.fst K V W).comp S.subtype) := by
  let T : Submodule K W := S.comap (LinearMap.inr K V W)
  have he : ∀ i y, y∈T → N.action.E i y∈T := by
    intro i y hy
    change (0,N.action.E i y)∈S
    have h := hE i (0,y) hy
    simpa only [map_zero] using h
  have hf : ∀ i y, y∈T → N.action.F i y∈T := by
    intro i y hy
    change (0,N.action.F i y)∈S
    have h := hF i (0,y) hy
    simpa only [map_zero] using h
  have ht : T=⊥ := by
    rcases hN.2 T he hf with h | h
    · exact h
    · exact False.elim (hhighest (show N.highestVector∈T from h ▸ Submodule.mem_top))
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext hxy
  have hd : (0,x.val.2-y.val.2)∈S := by
    have h := S.sub_mem x.property y.property
    have hfirst : x.val.1-y.val.1=0 := sub_eq_zero.mpr hxy
    change (x.val.1-y.val.1,x.val.2-y.val.2)∈S at h
    rwa [hfirst] at h
  have hdT : x.val.2-y.val.2∈T := hd
  rw [ht, Submodule.mem_bot] at hdT
  exact sub_eq_zero.mp hdT

private theorem zero_highest_not_mem_paired (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) :
    (0,N.highestVector) ∉ pairedHighestWeightSpan M N := by
  intro hp
  have h := pairedHighestWeightSpan_gradeProjection_zero M N (0,N.highestVector) hp
  simp only [map_zero, N.gradeProjection_of_mem 0 _ N.highestVector_grade] at h
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
  have h0 : c • M.highestVector = 0 := congrArg Prod.fst hc
  have hc0 : c=0 := (smul_eq_zero.mp h0).resolve_right M.highestVector_ne_zero
  have h1 := congrArg Prod.snd hc
  exact N.highestVector_ne_zero (by simpa [hc0] using h1.symm)

theorem pairedHighestWeightFst_injective (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hN : N.action.IsIrreducible) : Function.Injective (pairedHighestWeightFst M N) :=
  fst_injective_of_irreducible M N _ hN
    (pairedHighestWeightSpan_E_stable M N hweight)
    (pairedHighestWeightSpan_F_stable M N) (zero_highest_not_mem_paired M N)

private theorem paired_swap_mem (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (p : V×W) (hp : p∈pairedHighestWeightSpan M N) :
    p.swap ∈ pairedHighestWeightSpan N M := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,rfl⟩ := hp
    exact Submodule.subset_span ⟨u,rfl⟩
  | zero => exact Submodule.zero_mem _
  | add p q hp hq ihp ihq => exact Submodule.add_mem _ ihp ihq
  | smul c p hp ih => exact Submodule.smul_mem _ c ih

theorem pairedHighestWeightSnd_injective (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) : Function.Injective (pairedHighestWeightSnd M N) := by
  intro x y hxy
  have hswap := pairedHighestWeightFst_injective N M hweight.symm hM
    (a₁ := ⟨x.val.swap,paired_swap_mem M N x.val x.property⟩)
    (a₂ := ⟨y.val.swap,paired_swap_mem M N y.val y.property⟩) hxy
  apply Subtype.ext
  have hv := congrArg Subtype.val hswap
  exact Prod.swap_injective hv

noncomputable def highestWeightEquiv (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) : V ≃ₗ[K] W :=
  (LinearEquiv.ofBijective (pairedHighestWeightFst M N)
    ⟨pairedHighestWeightFst_injective M N hweight hN,pairedHighestWeightFst_surjective M N⟩).symm.trans
  (LinearEquiv.ofBijective (pairedHighestWeightSnd M N)
    ⟨pairedHighestWeightSnd_injective M N hweight hM,pairedHighestWeightSnd_surjective M N⟩)

theorem highestWeightEquiv_of_mem_paired (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible)
    (p : V×W) (hp : p∈pairedHighestWeightSpan M N) :
    highestWeightEquiv M N hweight hM hN p.1 = p.2 := by
  let x : pairedHighestWeightSpan M N := ⟨p,hp⟩
  change highestWeightEquiv M N hweight hM hN (pairedHighestWeightFst M N x) =
    pairedHighestWeightSnd M N x
  simp only [highestWeightEquiv, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    LinearEquiv.symm_apply_apply]
  apply congrArg (pairedHighestWeightSnd M N)
  exact (LinearEquiv.ofBijective (pairedHighestWeightFst M N)
    ⟨pairedHighestWeightFst_injective M N hweight hN,pairedHighestWeightFst_surjective M N⟩).symm_apply_apply x

theorem highestWeightEquiv_pair (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) (v : V) :
    (v,highestWeightEquiv M N hweight hM hN v)∈pairedHighestWeightSpan M N := by
  obtain ⟨x,hx⟩ := pairedHighestWeightFst_surjective M N v
  have hh := highestWeightEquiv_of_mem_paired M N hweight hM hN x.val x.property
  change x.val.1=v at hx
  rw [hx] at hh
  rw [hh, ←hx]
  exact x.property

theorem highestWeightEquiv_highest (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) :
    highestWeightEquiv M N hweight hM hN M.highestVector = N.highestVector :=
  highestWeightEquiv_of_mem_paired M N hweight hM hN _ (Submodule.subset_span ⟨[],rfl⟩)

theorem highestWeightEquiv_E (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) (i : Fin 3) (v : V) :
    highestWeightEquiv M N hweight hM hN (M.action.E i v) =
      N.action.E i (highestWeightEquiv M N hweight hM hN v) :=
  highestWeightEquiv_of_mem_paired M N hweight hM hN _
    (pairedHighestWeightSpan_E_stable M N hweight i _ (highestWeightEquiv_pair M N hweight hM hN v))

theorem highestWeightEquiv_F (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) (i : Fin 3) (v : V) :
    highestWeightEquiv M N hweight hM hN (M.action.F i v) =
      N.action.F i (highestWeightEquiv M N hweight hM hN v) :=
  highestWeightEquiv_of_mem_paired M N hweight hM hN _
    (pairedHighestWeightSpan_F_stable M N i _ (highestWeightEquiv_pair M N hweight hM hN v))

theorem highestWeightEquiv_H (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) (i : Fin 3) (v : V) :
    highestWeightEquiv M N hweight hM hN (M.action.H i v) =
      N.action.H i (highestWeightEquiv M N hweight hM hN v) :=
  highestWeightEquiv_of_mem_paired M N hweight hM hN _
    (pairedHighestWeightSpan_H_stable M N hweight i _ (highestWeightEquiv_pair M N hweight hM hN v))

theorem highestWeightEquiv_gradeProjection (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) (n : ℤ) (v : V) :
    highestWeightEquiv M N hweight hM hN (M.gradeProjection n v) =
      N.gradeProjection n (highestWeightEquiv M N hweight hM hN v) :=
  highestWeightEquiv_of_mem_paired M N hweight hM hN _
    (pairedHighestWeightSpan_gradeProjection M N n _ (highestWeightEquiv_pair M N hweight hM hN v))

theorem highestWeightEquiv_mem_grade (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) (n : ℤ) (v : V)
    (hv : v∈M.grade n) : highestWeightEquiv M N hweight hM hN v ∈ N.grade n := by
  have h := highestWeightEquiv_gradeProjection M N hweight hM hN n v
  rw [M.gradeProjection_of_mem n v hv] at h
  rw [h]
  exact N.gradeProjection_mem n _

theorem highestWeightEquiv_map_grade (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) (n : ℤ) :
    (M.grade n).map (highestWeightEquiv M N hweight hM hN).toLinearMap = N.grade n := by
  apply le_antisymm
  · rintro w ⟨v,hv,rfl⟩
    exact highestWeightEquiv_mem_grade M N hweight hM hN n v hv
  · intro w hw
    let e := highestWeightEquiv M N hweight hM hN
    have h := highestWeightEquiv_gradeProjection M N hweight hM hN n (e.symm w)
    change e (M.gradeProjection n (e.symm w)) = N.gradeProjection n (e (e.symm w)) at h
    rw [e.apply_symm_apply, N.gradeProjection_of_mem n w hw] at h
    have heq : M.gradeProjection n (e.symm w) = e.symm w := by
      apply e.injective
      rw [h, e.apply_symm_apply]
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    rw [← heq]
    exact M.gradeProjection_mem n _

theorem highestWeight_finrank_grade_eq (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) (n : ℤ) :
    Module.finrank K (M.grade n) = Module.finrank K (N.grade n) := by
  have h := (Submodule.equivMapOfInjective (highestWeightEquiv M N hweight hM hN).toLinearMap
    (highestWeightEquiv M N hweight hM hN).injective (M.grade n)).finrank_eq
  rw [highestWeightEquiv_map_grade M N hweight hM hN n] at h
  exact h

theorem highestWeight_character_eq (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) : M.character=N.character := by
  ext n
  simp only [M.coeff_character, N.coeff_character, highestWeight_finrank_grade_eq M N hweight hM hN]

theorem highestWeightEquiv_principalDerivation (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible) (v : V) :
    highestWeightEquiv M N hweight hM hN (M.principalDerivation v) =
      N.principalDerivation (highestWeightEquiv M N hweight hM hN v) := by
  let e := highestWeightEquiv M N hweight hM hN
  have h : e.toLinearMap.comp M.principalDerivation = N.principalDerivation.comp e.toLinearMap := by
    apply M.linearMap_ext_on_grade
    intro n x hx
    change e (M.principalDerivation x) = N.principalDerivation (e x)
    rw [M.principalDerivation_of_mem n x hx,
      N.principalDerivation_of_mem n (e x) (highestWeightEquiv_mem_grade M N hweight hM hN n x hx),
      map_smul]
  exact LinearMap.congr_fun h v
theorem highestWeightEquiv_unique (M : PrincipalHighestWeightModule K V)
    (N : PrincipalHighestWeightModule K W) (hweight : M.highestWeight=N.highestWeight)
    (hM : M.action.IsIrreducible) (hN : N.action.IsIrreducible)
    (f : V →ₗ[K] W) (hhighest : f M.highestVector=N.highestVector)
    (hF : ∀ i v, f (M.action.F i v)=N.action.F i (f v)) :
    f = (highestWeightEquiv M N hweight hM hN).toLinearMap := by
  apply LinearMap.ext
  intro v
  have hv : v∈M.negativeWordSpan := by rw [M.negativeWordSpan_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u,rfl⟩ := hv
    induction u with
    | nil => exact hhighest.trans (highestWeightEquiv_highest M N hweight hM hN).symm
    | cons i u ih =>
      change f (M.action.F i (M.negativeWordValue u)) =
        highestWeightEquiv M N hweight hM hN (M.action.F i (M.negativeWordValue u))
      rw [hF, highestWeightEquiv_F M N hweight hM hN]
      exact congrArg (N.action.F i) ih
  | zero => simp
  | add v w hv hw ihv ihw => simp only [map_add, ihv, ihw]
  | smul c v hv ih => simp only [map_smul, ih]

end KanadeRussell.Representation
