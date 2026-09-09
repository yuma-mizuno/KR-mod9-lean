import KanadeRussell.Representation.ChevalleyIrreducibility
import KanadeRussell.Representation.PrincipalFiltration
import KanadeRussell.Representation.PrimitiveKernel

/-! Primitive uniqueness forces ordinary irreducibility. The submodule in
the argument is arbitrary apart from stability under raising and lowering. -/

namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

theorem eq_top_of_nonzero_EF_stable
    (hprimitive : ∀ v, (∀ i, M.action.E i v = 0) →
      v ∈ Submodule.span K {M.highestVector})
    (S : Submodule K V) (hS : S ≠ ⊥)
    (hE : ∀ i v, v ∈ S → M.action.E i v ∈ S)
    (hF : ∀ i v, v ∈ S → M.action.F i v ∈ S) : S = ⊤ := by
  obtain ⟨v, hvS, hv, hvE⟩ := M.exists_primitive_of_nonzero_E_stable S hS hE
  exact M.eq_top_of_nonzero_primitive hprimitive S v hvS hv hvE hF

theorem action_isIrreducible_of_primitiveLine
    (hprimitive : ∀ v, (∀ i, M.action.E i v = 0) →
      v ∈ Submodule.span K {M.highestVector}) : M.action.IsIrreducible := by
  refine ⟨⟨⟨M.highestVector, 0, M.highestVector_ne_zero⟩⟩, ?_⟩
  intro S hE hF
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · exact Or.inr (M.eq_top_of_nonzero_EF_stable hprimitive S hS hE hF)

variable [CharZero K]

theorem action_isIrreducible_of_root_primitive_uniqueness
    (hprimitive : ∀ beta v, v ∈ M.rootGrade beta →
      (∀ i, M.action.E i v = 0) → v ∈ Submodule.span K {M.highestVector}) :
    M.action.IsIrreducible :=
  M.action_isIrreducible_of_primitiveLine
    (M.primitive_mem_highestLine_of_rootGrades hprimitive)

end KanadeRussell.Representation.PrincipalHighestWeightModule
