import KanadeRussell.Representation.AffineCyclicity

/-! The existing Serre presentation on vector spaces and its stable restrictions. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Exactly the Cartan, EF and Serre operator relations, with no representation-theoretic inputs. -/
abbrev ChevalleyAction (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  SerreSystem K (Fin 3) affineCartanMatrix (Module.End K V)

theorem intertwine_lie_apply (e : W →ₗ[K] V) (a b : Module.End K W) (a' b' : Module.End K V)
    (ha : ∀ v, e (a v) = a' (e v)) (hb : ∀ v, e (b v) = b' (e v)) (v : W) :
    e (⁅a,b⁆ v) = ⁅a',b'⁆ (e v) := by
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, map_sub, ha, hb]

theorem intertwine_ad_pow_apply (e : W →ₗ[K] V)
    (a b : Module.End K W) (a' b' : Module.End K V)
    (ha : ∀ v, e (a v) = a' (e v)) (hb : ∀ v, e (b v) = b' (e v)) (n : ℕ) (v : W) :
    e ((((LieAlgebra.ad K (Module.End K W) a)^n) b) v) =
      (((LieAlgebra.ad K (Module.End K V) a')^n) b') (e v) := by
  induction n generalizing v with
  | zero => simpa using hb v
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
    exact intertwine_lie_apply e a _ a' _ ha ih v

theorem submodule_val_zsmul (S : Submodule K V) (n : ℤ) (v : S) :
    (n • v).val = n • v.val := map_zsmul S.subtype.toAddMonoidHom n v

namespace ChevalleyAction
variable (A : ChevalleyAction K V)

/-- The conventional off-diagonal Serre exponent, expressed as a natural number. -/
theorem serreE (i j : Fin 3) (hij : i ≠ j) :
    ((LieAlgebra.ad K (Module.End K V) (A.E i))^((1-affineCartanMatrix i j).toNat)) (A.E j) = 0 := by
  have h := A.adE i j
  have hn : (1-affineCartanMatrix i j).toNat = (-affineCartanMatrix i j).toNat+1 := by
    fin_cases i <;> fin_cases j <;> first | contradiction | decide
  rw [hn, pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply]
  exact h

theorem serreF (i j : Fin 3) (hij : i ≠ j) :
    ((LieAlgebra.ad K (Module.End K V) (A.F i))^((1-affineCartanMatrix i j).toNat)) (A.F j) = 0 := by
  have h := A.adF i j
  have hn : (1-affineCartanMatrix i j).toNat = (-affineCartanMatrix i j).toNat+1 := by
    fin_cases i <;> fin_cases j <;> first | contradiction | decide
  rw [hn, pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply]
  exact h

noncomputable def restrict (S : Submodule K V)
    (hE : ∀ i v, v ∈ S → A.E i v ∈ S)
    (hF : ∀ i v, v ∈ S → A.F i v ∈ S)
    (hH : ∀ i v, v ∈ S → A.H i v ∈ S) : ChevalleyAction K S where
  E i := (A.E i).restrict (hE i)
  F i := (A.F i).restrict (hF i)
  H i := (A.H i).restrict (hH i)
  HH i j := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have h := congrArg (fun a : Module.End K V => a v.val) (A.HH i j)
    simpa only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_smul, Submodule.coe_neg, submodule_val_zsmul,
      LinearMap.restrict_apply, Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.zero_apply] using h
  EF i j := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have h := congrArg (fun a : Module.End K V => a v.val) (A.EF i j)
    by_cases hij : i=j <;> simpa only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_smul, Submodule.coe_neg, submodule_val_zsmul, LinearMap.restrict_apply, Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      hij, if_true, if_false, LinearMap.zero_apply] using h
  HE i j := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have h := congrArg (fun a : Module.End K V => a v.val) (A.HE i j)
    simpa only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_smul, Submodule.coe_neg, submodule_val_zsmul,
      LinearMap.restrict_apply, Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply] using h
  HF i j := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have h := congrArg (fun a : Module.End K V => a v.val) (A.HF i j)
    simpa only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_smul, Submodule.coe_neg, submodule_val_zsmul,
      LinearMap.restrict_apply, Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, LinearMap.neg_apply] using h
  adE i j := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have h := intertwine_ad_pow_apply S.subtype ((A.E i).restrict (hE i))
      ⁅(A.E i).restrict (hE i),(A.E j).restrict (hE j)⁆ (A.E i) ⁅A.E i,A.E j⁆
      (fun _ => rfl) (intertwine_lie_apply S.subtype _ _ _ _ (fun _ => rfl) (fun _ => rfl))
      (-affineCartanMatrix i j).toNat v
    rw [A.adE i j, LinearMap.zero_apply] at h
    exact h
  adF i j := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have h := intertwine_ad_pow_apply S.subtype ((A.F i).restrict (hF i))
      ⁅(A.F i).restrict (hF i),(A.F j).restrict (hF j)⁆ (A.F i) ⁅A.F i,A.F j⁆
      (fun _ => rfl) (intertwine_lie_apply S.subtype _ _ _ _ (fun _ => rfl) (fun _ => rfl))
      (-affineCartanMatrix i j).toNat v
    rw [A.adF i j, LinearMap.zero_apply] at h
    exact h

end ChevalleyAction

variable [CharZero K]
noncomputable def ambientChevalleyAction (w : K) (hw : w^4-w^2+1=0) : ChevalleyAction K (Space K) :=
  affineTensorSerreSystem w hw

noncomputable def tensorCyclicChevalleyAction (w : K) (hw : w^4-w^2+1=0) (seed : Space K) :
    ChevalleyAction K (tensorCyclicSpan w seed) :=
  (ambientChevalleyAction w hw).restrict (tensorCyclicSpan w seed)
    (fun i v hv => tensorCyclicSpan_algebra_mem w seed _
      (chevalleyOperatorAlgebra_le_tensor w (chevalleyE_mem_algebra w i)) v hv)
    (fun i v hv => tensorCyclicSpan_algebra_mem w seed _
      (chevalleyOperatorAlgebra_le_tensor w (chevalleyF_mem_algebra w i)) v hv)
    (fun i v hv => tensorCyclicSpan_algebra_mem w seed _
      (chevalleyOperatorAlgebra_le_tensor w (chevalleyH_mem_algebra w i)) v hv)

@[simp] theorem tensorCyclicChevalleyAction_E_val (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (i : Fin 3) (v : tensorCyclicSpan w seed) :
    ((tensorCyclicChevalleyAction w hw seed).E i v).val = chevalleyE w i v.val := rfl
@[simp] theorem tensorCyclicChevalleyAction_F_val (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (i : Fin 3) (v : tensorCyclicSpan w seed) :
    ((tensorCyclicChevalleyAction w hw seed).F i v).val = chevalleyF w i v.val := rfl
@[simp] theorem tensorCyclicChevalleyAction_H_val (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (i : Fin 3) (v : tensorCyclicSpan w seed) :
    ((tensorCyclicChevalleyAction w hw seed).H i v).val = chevalleyH w i v.val := rfl

/-- Every ambient Chevalley operator-algebra element has its actual restriction
in the algebra generated by the restricted Chevalley operators. -/
theorem tensorCyclicChevalleyAction_algebra_lift (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (a : Module.End K (Space K)) (ha : a ∈ chevalleyOperatorAlgebra w) :
    ∃ b ∈ Algebra.adjoin K
      (Set.range (tensorCyclicChevalleyAction w hw seed).E ∪
        (Set.range (tensorCyclicChevalleyAction w hw seed).F ∪
          Set.range (tensorCyclicChevalleyAction w hw seed).H)),
      ∀ v : tensorCyclicSpan w seed, (b v).val = a v.val := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩
    · exact ⟨_, Algebra.subset_adjoin (Or.inl ⟨i,rfl⟩), fun _ => rfl⟩
    · exact ⟨_, Algebra.subset_adjoin (Or.inr (Or.inl ⟨i,rfl⟩)), fun _ => rfl⟩
    · exact ⟨_, Algebra.subset_adjoin (Or.inr (Or.inr ⟨i,rfl⟩)), fun _ => rfl⟩
  | algebraMap c =>
    exact ⟨algebraMap K _ c, (Algebra.adjoin K _).algebraMap_mem c, fun _ => rfl⟩
  | add a b ha hb hia hib =>
    obtain ⟨a',ha',hea⟩ := hia
    obtain ⟨b',hb',heb⟩ := hib
    refine ⟨a'+b', (Algebra.adjoin K _).add_mem ha' hb', ?_⟩
    intro v
    simp only [LinearMap.add_apply, Submodule.coe_add, hea, heb]
  | mul a b ha hb hia hib =>
    obtain ⟨a',ha',hea⟩ := hia
    obtain ⟨b',hb',heb⟩ := hib
    refine ⟨a'*b', (Algebra.adjoin K _).mul_mem ha' hb', ?_⟩
    intro v
    simp only [Module.End.mul_apply, hea, heb]

/-- A homogeneous seed is cyclic for the actual restricted Chevalley action. -/
theorem tensorCyclicChevalleyAction_cyclic (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (hd : seed ∈ grade d) :
    Submodule.span K ((fun a : Module.End K (tensorCyclicSpan w seed) =>
      a ⟨seed,tensorCyclicSpan_seed w seed⟩) ''
      (Algebra.adjoin K (Set.range (tensorCyclicChevalleyAction w hw seed).E ∪
        (Set.range (tensorCyclicChevalleyAction w hw seed).F ∪
          Set.range (tensorCyclicChevalleyAction w hw seed).H)) :
        Set (Module.End K (tensorCyclicSpan w seed)))) = ⊤ := by
  let R := Submodule.span K ((fun a : Module.End K (tensorCyclicSpan w seed) =>
      a ⟨seed,tensorCyclicSpan_seed w seed⟩) ''
      (Algebra.adjoin K (Set.range (tensorCyclicChevalleyAction w hw seed).E ∪
        (Set.range (tensorCyclicChevalleyAction w hw seed).F ∪
          Set.range (tensorCyclicChevalleyAction w hw seed).H)) :
        Set (Module.End K (tensorCyclicSpan w seed))))
  have hle : chevalleyCyclicSpan w seed ≤ R.map (tensorCyclicSpan w seed).subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨b,hb,he⟩ := tensorCyclicChevalleyAction_algebra_lift w hw seed a ha
    exact ⟨b ⟨seed,tensorCyclicSpan_seed w seed⟩,
      Submodule.subset_span ⟨b,hb,rfl⟩, he _⟩
  rw [chevalleyCyclicSpan_eq_tensor w hw seed d hd] at hle
  change R = ⊤
  apply Submodule.map_injective_of_injective (tensorCyclicSpan w seed).subtype_injective
  rw [Submodule.map_top, Submodule.range_subtype]
  exact le_antisymm (by intro v hv; obtain ⟨x,hx,rfl⟩ := hv; exact x.property) hle

end KanadeRussell.Representation
