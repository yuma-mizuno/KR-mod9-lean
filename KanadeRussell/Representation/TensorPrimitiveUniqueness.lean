import KanadeRussell.Representation.TensorModeCasimirCommutator
import KanadeRussell.Representation.CasimirWordRecurrence
import KanadeRussell.Representation.ConcreteHighestWeight

/-! The actual Fock Casimir transfers to the cyclic highest-weight modules.
The scalar recurrence and primitive annihilation then force primitive vectors
in a root grade into the highest line. -/

set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem tensorCyclicModeCasimir_lie_of_operator_equation
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K) (i : Fin 3)
    (hcomm : ⁅tensorModeCasimir w, chevalleyF w i⁆ =
      (2 * (symmetrizer i : K)) • (chevalleyF w i * chevalleyH w i)) :
    ⁅tensorCyclicModeCasimir w seed, (tensorCyclicChevalleyAction w hw seed).F i⁆ =
      (2 * (symmetrizer i : K)) •
        ((tensorCyclicChevalleyAction w hw seed).F i *
          (tensorCyclicChevalleyAction w hw seed).H i) := by
  apply LinearMap.ext
  intro v
  change tensorCyclicModeCasimir w seed ((tensorCyclicChevalleyAction w hw seed).F i v) -
    (tensorCyclicChevalleyAction w hw seed).F i (tensorCyclicModeCasimir w seed v) =
      (2 * (symmetrizer i : K)) •
        (tensorCyclicChevalleyAction w hw seed).F i ((tensorCyclicChevalleyAction w hw seed).H i v)
  apply Subtype.ext
  have h := congrArg (fun a : Module.End K (Space K) => a v.val) hcomm
  simpa only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Submodule.coe_sub, Submodule.coe_smul,
    tensorCyclicModeCasimir_val, tensorCyclicChevalleyAction_F_val,
    tensorCyclicChevalleyAction_H_val] using h

theorem tensorPrincipalModule_primitive_mem_highestLine_of_operator_equations
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed)
    (hcomm : ∀ i, ⁅tensorModeCasimir w, chevalleyF w i⁆ =
      (2 * (symmetrizer i : K)) • (chevalleyF w i * chevalleyH w i))
    (beta : RootCoefficients) (v : tensorCyclicSpan w seed) (hv : v ≠ 0)
    (hgrade : v ∈ M.rootGrade beta) (hE : ∀ i, M.action.E i v = 0) :
    v ∈ Submodule.span K {M.highestVector} := by
  have hkill (p : tensorCyclicSpan w seed) (hp : ∀ i, M.action.E i p = 0) :
      tensorCyclicModeCasimir w seed p = 0 := by
    apply Subtype.ext
    change tensorModeCasimir w p.val = 0
    apply tensorModeCasimir_kills_primitive w hw
    intro i
    have h := congrArg Subtype.val (hp i)
    simpa only [haction, tensorCyclicChevalleyAction_E_val, ZeroMemClass.coe_zero] using h
  have hrestricted : ∀ i,
      ⁅tensorCyclicModeCasimir w seed, M.action.F i⁆ =
        (2 * (symmetrizer i : K)) • (M.action.F i * M.action.H i) := by
    intro i
    rw [haction]
    exact tensorCyclicModeCasimir_lie_of_operator_equation w hw seed i (hcomm i)
  exact M.primitive_mem_highestLine_of_casimir_operator (tensorCyclicModeCasimir w seed)
    (hkill M.highestVector M.E_highestVector) hrestricted beta v hv hgrade hE (hkill v hE)

end KanadeRussell.Representation
