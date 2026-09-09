import KanadeRussell.Representation.NegativeWords

/-! Irreducibility for the actual Chevalley generators. Stability under E and
F already implies H-stability by the proved EF relation. -/

set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace ChevalleyAction

/-- A nonzero action with no proper nonzero subspace invariant under its
raising and lowering generators. No grading condition is imposed on a subspace. -/
def IsIrreducible (A : ChevalleyAction K V) : Prop :=
  Nontrivial V ∧ ∀ S : Submodule K V,
    (∀ i v, v ∈ S → A.E i v ∈ S) →
    (∀ i v, v ∈ S → A.F i v ∈ S) → S = ⊥ ∨ S = ⊤

theorem H_stable_of_EF_stable (A : ChevalleyAction K V) (S : Submodule K V)
    (hE : ∀ i v, v ∈ S → A.E i v ∈ S)
    (hF : ∀ i v, v ∈ S → A.F i v ∈ S)
    (i : Fin 3) (v : V) (hv : v ∈ S) : A.H i v ∈ S := by
  have h := congrArg (fun a : Module.End K V => a v) (A.EF i i)
  simp [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [← h]
  exact S.sub_mem (hE i _ (hF i v hv)) (hF i _ (hE i v hv))

end ChevalleyAction

namespace PrincipalHighestWeightModule
variable (M : PrincipalHighestWeightModule K V)

theorem eq_top_of_highestVector_mem (S : Submodule K V)
    (hhighest : M.highestVector ∈ S)
    (hF : ∀ i v, v ∈ S → M.action.F i v ∈ S) : S = ⊤ := by
  apply top_unique
  rw [← M.negativeWordSpan_eq_top]
  apply Submodule.span_le.mpr
  rintro v ⟨u, rfl⟩
  induction u with
  | nil => exact hhighest
  | cons i u ih => exact hF i _ ih

theorem highestVector_mem_of_nonzero_highestLine (S : Submodule K V)
    (v : V) (hvS : v ∈ S) (hv : v ≠ 0)
    (hline : v ∈ Submodule.span K {M.highestVector}) : M.highestVector ∈ S := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hline
  have hc0 : c ≠ 0 := by
    intro hz
    apply hv
    simpa only [hz, zero_smul] using hc.symm
  have h := S.smul_mem c⁻¹ hvS
  rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h
  exact h

theorem eq_top_of_nonzero_primitive
    (hprimitive : ∀ v, (∀ i, M.action.E i v = 0) →
      v ∈ Submodule.span K {M.highestVector})
    (S : Submodule K V) (v : V) (hvS : v ∈ S) (hv : v ≠ 0)
    (hvE : ∀ i, M.action.E i v = 0)
    (hF : ∀ i v, v ∈ S → M.action.F i v ∈ S) : S = ⊤ :=
  M.eq_top_of_highestVector_mem S
    (M.highestVector_mem_of_nonzero_highestLine S v hvS hv (hprimitive v hvE)) hF

end PrincipalHighestWeightModule
end KanadeRussell.Representation
