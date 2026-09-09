import KanadeRussell.Representation.HighestWeightIrreducibility
import KanadeRussell.Representation.ConcretePrimitiveUniqueness

/-! The three original cyclic tensor actions are irreducible. Primitive
uniqueness applies to all vectors, with no homogeneous-vector restriction. -/

namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock Sectors
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem tensorPrincipalModule_primitive_mem_highestLine_global
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed)
    (v : tensorCyclicSpan w seed) (hE : ∀ i, M.action.E i v = 0) :
    v ∈ Submodule.span K {M.highestVector} :=
  M.primitive_mem_highestLine_of_rootGrades
    (tensorPrincipalModule_primitive_mem_highestLine w hw seed M haction) v hE

theorem tensorPrincipalModule_isIrreducible
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) : M.action.IsIrreducible :=
  M.action_isIrreducible_of_root_primitive_uniqueness
    (tensorPrincipalModule_primitive_mem_highestLine w hw seed M haction)

theorem skewPrincipalModule_primitive_mem_highestLine_global
    (w : K) (hw : w^4-w^2+1=0) (v : tensorCyclicSpan w (skewSeed : Space K))
    (hE : ∀ i, (skewPrincipalModule w hw).action.E i v = 0) :
    v ∈ Submodule.span K {(skewPrincipalModule w hw).highestVector} :=
  tensorPrincipalModule_primitive_mem_highestLine_global w hw skewSeed
    (skewPrincipalModule w hw) rfl v hE

theorem vacuumPrincipalModule_primitive_mem_highestLine_global
    (w : K) (hw : w^4-w^2+1=0) (v : tensorCyclicSpan w (1 : Space K))
    (hE : ∀ i, (vacuumPrincipalModule w hw).action.E i v = 0) :
    v ∈ Submodule.span K {(vacuumPrincipalModule w hw).highestVector} :=
  tensorPrincipalModule_primitive_mem_highestLine_global w hw 1
    (vacuumPrincipalModule w hw) rfl v hE

theorem alternatingPrincipalModule_primitive_mem_highestLine_global
    (w : K) (hw : w^4-w^2+1=0) (v : tensorCyclicSpan w (alternatingSeed : Space K))
    (hE : ∀ i, (alternatingPrincipalModule w hw).action.E i v = 0) :
    v ∈ Submodule.span K {(alternatingPrincipalModule w hw).highestVector} :=
  tensorPrincipalModule_primitive_mem_highestLine_global w hw alternatingSeed
    (alternatingPrincipalModule w hw) rfl v hE

theorem skewPrincipalModule_isIrreducible (w : K) (hw : w^4-w^2+1=0) :
    (skewPrincipalModule w hw).action.IsIrreducible :=
  tensorPrincipalModule_isIrreducible w hw skewSeed (skewPrincipalModule w hw) rfl

theorem vacuumPrincipalModule_isIrreducible (w : K) (hw : w^4-w^2+1=0) :
    (vacuumPrincipalModule w hw).action.IsIrreducible :=
  tensorPrincipalModule_isIrreducible w hw 1 (vacuumPrincipalModule w hw) rfl

theorem alternatingPrincipalModule_isIrreducible (w : K) (hw : w^4-w^2+1=0) :
    (alternatingPrincipalModule w hw).action.IsIrreducible :=
  tensorPrincipalModule_isIrreducible w hw alternatingSeed (alternatingPrincipalModule w hw) rfl

end KanadeRussell.Representation
