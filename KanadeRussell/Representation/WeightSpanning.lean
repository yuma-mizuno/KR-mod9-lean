import KanadeRussell.Representation.AffineCyclicity
import KanadeRussell.Tsuchioka.AffineSkewHighestWeight
import KanadeRussell.Tsuchioka.AffineAlternatingHighestWeight

/-! Actual joint Cartan eigenspaces span the three concrete cyclic modules.
The statement is a supremum equality, without an internal-direct-sum claim. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

noncomputable def jointWeightSpace (w : K) (mu : Fin 3 → K) : Submodule K (Space K) :=
  ⨅ i, LinearMap.ker (chevalleyH w i - mu i • 1)

@[simp] theorem mem_jointWeightSpace (w : K) (mu : Fin 3 → K) (v : Space K) :
    v ∈ jointWeightSpace w mu ↔ ∀ i, chevalleyH w i v = mu i • v := by
  simp [jointWeightSpace, sub_eq_zero]

theorem chevalleyE_jointWeightSpace (w : K) (hw : w^4-w^2+1=0)
    (mu : Fin 3 → K) (j : Fin 3) (v : Space K) (hv : v ∈ jointWeightSpace w mu) :
    chevalleyE w j v ∈ jointWeightSpace w (fun i => mu i + (affineCartanMatrix i j : K)) := by
  rw [mem_jointWeightSpace] at hv ⊢
  intro i
  have h := congrArg (fun a : Module.End K (Space K) => a v) (chevalley_HE w hw i j)
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, hv i, map_smul] at h
  rw [add_smul]
  simpa only [add_comm, neg_smul, sub_eq_add_neg] using (sub_eq_iff_eq_add.mp h)

theorem chevalleyF_jointWeightSpace (w : K) (hw : w^4-w^2+1=0)
    (mu : Fin 3 → K) (j : Fin 3) (v : Space K) (hv : v ∈ jointWeightSpace w mu) :
    chevalleyF w j v ∈ jointWeightSpace w (fun i => mu i - (affineCartanMatrix i j : K)) := by
  rw [mem_jointWeightSpace] at hv ⊢
  intro i
  have h := congrArg (fun a : Module.End K (Space K) => a v) (chevalley_HF w hw i j)
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, hv i, map_smul] at h
  rw [sub_smul]
  simpa only [add_comm, neg_smul, sub_eq_add_neg] using (sub_eq_iff_eq_add.mp h)

theorem chevalleyH_jointWeightSpace (w : K) (mu : Fin 3 → K) (j : Fin 3)
    (v : Space K) (hv : v ∈ jointWeightSpace w mu) :
    chevalleyH w j v ∈ jointWeightSpace w mu := by
  rw [(mem_jointWeightSpace w mu v).mp hv j]
  exact (jointWeightSpace w mu).smul_mem _ hv

noncomputable def jointWeightSpan (w : K) (S : Submodule K (Space K)) : Submodule K (Space K) :=
  ⨆ mu : Fin 3 → K, S ⊓ jointWeightSpace w mu

theorem jointWeightSpan_le (w : K) (S : Submodule K (Space K)) : jointWeightSpan w S ≤ S :=
  iSup_le fun _ => inf_le_left

theorem jointWeightSpan_stable_of_shift (w : K) (S : Submodule K (Space K))
    (a : Module.End K (Space K)) (ha : ∀ v ∈ S, a v ∈ S)
    (shift : (Fin 3 → K) → (Fin 3 → K))
    (hshift : ∀ mu v, v ∈ jointWeightSpace w mu → a v ∈ jointWeightSpace w (shift mu)) :
    ∀ v ∈ jointWeightSpan w S, a v ∈ jointWeightSpan w S := by
  intro v hv
  refine Submodule.iSup_induction (fun mu => S ⊓ jointWeightSpace w mu)
    (motive := fun v => a v ∈ jointWeightSpan w S) hv ?_ ?_ ?_
  · intro mu v hv
    exact Submodule.mem_iSup_of_mem (shift mu) ⟨ha v hv.1, hshift mu v hv.2⟩
  · simp
  · intro v u hv hu
    simpa only [map_add] using (jointWeightSpan w S).add_mem hv hu

theorem jointWeightSpan_chevalley_algebra_stable (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (a : Module.End K (Space K)) (ha : a ∈ chevalleyOperatorAlgebra w) :
    ∀ v ∈ jointWeightSpan w (chevalleyCyclicSpan w seed),
      a v ∈ jointWeightSpan w (chevalleyCyclicSpan w seed) := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with ⟨j,rfl⟩ | ⟨j,rfl⟩ | ⟨j,rfl⟩
    · exact jointWeightSpan_stable_of_shift w _ _
        (chevalleyCyclicSpan_algebra_mem w seed _ (chevalleyE_mem_algebra w j))
        (fun mu i => mu i + (affineCartanMatrix i j : K))
        (fun mu v hv => chevalleyE_jointWeightSpace w hw mu j v hv)
    · exact jointWeightSpan_stable_of_shift w _ _
        (chevalleyCyclicSpan_algebra_mem w seed _ (chevalleyF_mem_algebra w j))
        (fun mu i => mu i - (affineCartanMatrix i j : K))
        (fun mu v hv => chevalleyF_jointWeightSpace w hw mu j v hv)
    · exact jointWeightSpan_stable_of_shift w _ _
        (chevalleyCyclicSpan_algebra_mem w seed _ (chevalleyH_mem_algebra w j))
        id (fun mu v hv => chevalleyH_jointWeightSpace w mu j v hv)
  | algebraMap c =>
    intro v hv
    exact (jointWeightSpan w (chevalleyCyclicSpan w seed)).smul_mem c hv
  | add a b ha hb hia hib =>
    intro v hv
    exact (jointWeightSpan w (chevalleyCyclicSpan w seed)).add_mem (hia v hv) (hib v hv)
  | mul a b ha hb hia hib =>
    intro v hv
    exact hia _ (hib v hv)

theorem chevalleyCyclicSpan_eq_iSup_jointWeightSpace (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (mu : Fin 3 → K) (hseed : ∀ i, chevalleyH w i seed = mu i • seed) :
    chevalleyCyclicSpan w seed = ⨆ nu : Fin 3 → K,
      chevalleyCyclicSpan w seed ⊓ jointWeightSpace w nu := by
  apply le_antisymm _ (jointWeightSpan_le w _)
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,rfl⟩
  apply jointWeightSpan_chevalley_algebra_stable w hw seed a ha seed
  exact Submodule.mem_iSup_of_mem mu ⟨chevalleyCyclicSpan_seed w seed,
    (mem_jointWeightSpace w mu seed).mpr hseed⟩

theorem tensorCyclicSpan_eq_iSup_jointWeightSpace (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (hd : seed ∈ grade d)
    (mu : Fin 3 → K) (hseed : ∀ i, chevalleyH w i seed = mu i • seed) :
    tensorCyclicSpan w seed = ⨆ nu : Fin 3 → K,
      tensorCyclicSpan w seed ⊓ jointWeightSpace w nu := by
  rw [← chevalleyCyclicSpan_eq_tensor w hw seed d hd]
  exact chevalleyCyclicSpan_eq_iSup_jointWeightSpace w hw seed mu hseed

theorem vacuum_tensor_jointWeightSpace_spanning (w : K) (hw : w^4-w^2+1=0) :
    tensorCyclicSpan w (1 : Space K) = ⨆ nu : Fin 3 → K,
      tensorCyclicSpan w 1 ⊓ jointWeightSpace w nu :=
  tensorCyclicSpan_eq_iSup_jointWeightSpace w hw 1 0
    (MvPolynomial.isWeightedHomogeneous_one K variableWeight)
    (fun i => if i=0 then 3 else 0) (chevalleyH_vacuum w)

theorem skew_tensor_jointWeightSpace_spanning (w : K) (hw : w^4-w^2+1=0) :
    tensorCyclicSpan w (Sectors.skewSeed : Space K) = ⨆ nu : Fin 3 → K,
      tensorCyclicSpan w Sectors.skewSeed ⊓ jointWeightSpace w nu :=
  tensorCyclicSpan_eq_iSup_jointWeightSpace w hw Sectors.skewSeed 1 Sectors.skewSeed_grade
    (fun i => if i=2 then 0 else 1) (chevalleyH_skewSeed w hw)

theorem alternating_tensor_jointWeightSpace_spanning (w : K) (hw : w^4-w^2+1=0) :
    tensorCyclicSpan w (alternatingSeed : Space K) = ⨆ nu : Fin 3 → K,
      tensorCyclicSpan w alternatingSeed ⊓ jointWeightSpace w nu :=
  tensorCyclicSpan_eq_iSup_jointWeightSpace w hw alternatingSeed 3 alternatingSeed_grade
    (fun i => if i=2 then 1 else 0) (chevalleyH_alternatingSeed w hw)

end KanadeRussell.Tsuchioka.Fock
