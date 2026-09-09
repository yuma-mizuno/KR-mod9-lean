import KanadeRussell.Representation.PrincipalModeCartan
import KanadeRussell.Representation.RootGradeOperator
import KanadeRussell.Representation.ConcretePrincipalDerivation
import KanadeRussell.Representation.TensorModeCasimir

/-! Concrete Cartan eigenmodes act between the actual finite root grades.
The shift uses the normalized principal derivation of each cyclic module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem principalModeCombination_mem_tensorOperatorAlgebra (w : K) (n : ℤ)
    (v : Fin 3 → K) : principalModeCombination w n v ∈ tensorOperatorAlgebra w := by
  rw [principalModeCombination_apply]
  exact (tensorOperatorAlgebra w).sum_mem (fun r _ =>
    (tensorOperatorAlgebra w).smul_mem (principalMode_mem_tensorOperatorAlgebra w n r) _)

theorem principalModeCombination_mem_tensorCyclicSpan (w : K) (seed : Space K)
    (n : ℤ) (v : Fin 3 → K) (p : Space K) (hp : p ∈ tensorCyclicSpan w seed) :
    principalModeCombination w n v p ∈ tensorCyclicSpan w seed :=
  tensorCyclicSpan_algebra_mem w seed _
    (principalModeCombination_mem_tensorOperatorAlgebra w n v) p hp

noncomputable def tensorCyclicPrincipalModeCombination (w : K) (seed : Space K)
    (n : ℤ) (v : Fin 3 → K) : Module.End K (tensorCyclicSpan w seed) :=
  (principalModeCombination w n v).restrict
    (principalModeCombination_mem_tensorCyclicSpan w seed n v)

@[simp] theorem tensorCyclicPrincipalModeCombination_val (w : K) (seed : Space K)
    (n : ℤ) (v : Fin 3 → K) (p : tensorCyclicSpan w seed) :
    (tensorCyclicPrincipalModeCombination w seed n v p).val =
      principalModeCombination w n v p.val := rfl

theorem tensorCyclicPrincipalModeCombination_H (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (n : ℤ) (hn : n ≠ 0) (v : Fin 3 → K) (i : Fin 3) (c : K)
    (hv : (principalCartanMatrix w n i).mulVec v = c • v) :
    ⁅(tensorCyclicChevalleyAction w hw seed).H i,
      tensorCyclicPrincipalModeCombination w seed n v⁆ =
      c • tensorCyclicPrincipalModeCombination w seed n v := by
  apply LinearMap.ext
  intro p
  change (tensorCyclicChevalleyAction w hw seed).H i (tensorCyclicPrincipalModeCombination w seed n v p) -
    tensorCyclicPrincipalModeCombination w seed n v ((tensorCyclicChevalleyAction w hw seed).H i p) =
      c • tensorCyclicPrincipalModeCombination w seed n v p
  apply Subtype.ext
  have h := congrArg (fun a : Module.End K (Space K) => a p.val)
    (principalModeCombination_eigenoperator w hw n hn i v c hv)
  simpa only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Submodule.coe_sub, Submodule.coe_smul,
    tensorCyclicPrincipalModeCombination_val, tensorCyclicChevalleyAction_H_val] using h

theorem tensorPrincipalModule_modeCombination_D (w : K) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed)) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (n : ℤ) (v : Fin 3 → K) :
    ⁅M.principalDerivation, tensorCyclicPrincipalModeCombination w seed n v⁆ =
      (n : K) • tensorCyclicPrincipalModeCombination w seed n v := by
  apply LinearMap.ext
  intro p
  change M.principalDerivation (tensorCyclicPrincipalModeCombination w seed n v p) -
    tensorCyclicPrincipalModeCombination w seed n v (M.principalDerivation p) =
      (n : K) • tensorCyclicPrincipalModeCombination w seed n v p
  apply Subtype.ext
  have h := congrArg (fun a : Module.End K (Space K) => a p.val)
    (principalDerivation_lie_principalModeCombination w n v)
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply] at h
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Submodule.coe_sub, Submodule.coe_smul,
    tensorCyclicPrincipalModeCombination_val, hD, map_add, map_smul]
  rw [← h]
  module

theorem tensorPrincipalModule_modeCombination_mem_rootGrade (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (gamma : RootCoefficients) (hn : totalDegree gamma ≠ 0) (v : Fin 3 → K)
    (hH : ∀ i, (principalCartanMatrix w (totalDegree gamma) i).mulVec v =
      (∑ j : Fin 3, (affineCartanMatrix i j : K) * (gamma j : K)) • v)
    (beta : RootCoefficients) (p : tensorCyclicSpan w seed) (hp : p ∈ M.rootGrade beta) :
    tensorCyclicPrincipalModeCombination w seed (totalDegree gamma) v p ∈
      M.rootGrade (beta-gamma) := by
  apply M.operator_mem_rootGrade_sub _ gamma
    (tensorPrincipalModule_modeCombination_D w seed M d hD _ v) ?_ beta p hp
  intro i
  rw [haction]
  exact tensorCyclicPrincipalModeCombination_H w hw seed _ hn v i _ (hH i)

end KanadeRussell.Representation
