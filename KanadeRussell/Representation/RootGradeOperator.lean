import KanadeRussell.Representation.RootGradeShifts
import KanadeRussell.Representation.PrimitiveUniqueness

/-! Cartan eigenoperators transport the actual finite root grades. In particular,
the raising and lowering maps restrict to adjacent grades, with the original
EF relation preserved after the necessary index identifications. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

omit [CharZero K] in
theorem occupationWeight_sub (lambda beta gamma : RootCoefficients) (j : Fin 4) :
    occupationWeight (K := K) lambda (beta-gamma) j =
      occupationWeight lambda beta j - occupationWeight 0 gamma j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [occupationWeight, Fin.cases_zero, totalDegree, Pi.sub_apply,
      Finset.sum_sub_distrib, Int.cast_sub]
    ring
  · simp only [occupationWeight, Fin.cases_succ, weightLabels, Pi.sub_apply,
      Pi.zero_apply, mul_sub, Finset.sum_sub_distrib, Int.cast_sub]
    ring

theorem occupationWeight_add_simple (lambda beta : RootCoefficients) (i : Fin 3) (j : Fin 4) :
    occupationWeight (K := K) lambda (beta+Pi.single i 1) j =
      occupationWeight lambda beta j - (rootCartanCoefficient i j : K) := by
  have h := occupationWeight_sub_simple (K := K) lambda (beta+Pi.single i 1) i j
  rw [add_sub_cancel_right] at h
  exact eq_sub_of_add_eq h.symm

omit [CharZero K] in
/-- An eigenoperator for the full Cartan action sends each root grade to the
grade with the shifted eigenvalues. Both the principal derivation and H labels
are included; there is no ambiguity from the null root. -/
theorem operator_mem_rootGrade (T : Module.End K V) (c : Fin 4 → K)
    (hcomm : ∀ j, ⁅M.extendedCartan j, T⁆ = c j • T)
    (beta gamma : RootCoefficients)
    (hweight : ∀ j, occupationWeight M.highestWeightLabels gamma j =
      occupationWeight M.highestWeightLabels beta j + c j)
    (v : V) (hv : v ∈ M.rootGrade beta) : T v ∈ M.rootGrade gamma := by
  apply (M.mem_extendedWeightSpace _ _).mpr
  intro j
  have hvj := (M.mem_extendedWeightSpace _ _).mp hv j
  have h := congrArg (fun a : Module.End K V => a v) (hcomm j)
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, hvj, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, hweight]
  module

omit [CharZero K] in
/-- A positive-root eigenoperator of occupation gamma lowers occupation by
gamma. Its principal commutator is positive totalDegree(gamma). -/
theorem operator_mem_rootGrade_sub (T : Module.End K V) (gamma : RootCoefficients)
    (hD : ⁅M.principalDerivation, T⁆ = (totalDegree gamma : K) • T)
    (hH : ∀ i, ⁅M.action.H i, T⁆ =
      (∑ j : Fin 3, (affineCartanMatrix i j : K) * (gamma j : K)) • T)
    (beta : RootCoefficients) (v : V) (hv : v ∈ M.rootGrade beta) :
    T v ∈ M.rootGrade (beta-gamma) := by
  apply M.operator_mem_rootGrade T (fun j => -occupationWeight (K := K) 0 gamma j)
    ?_ beta (beta-gamma) ?_ v hv
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa only [extendedCartan, occupationWeight, Fin.cases_zero, neg_neg] using hD
    · simpa only [extendedCartan, occupationWeight, Fin.cases_succ, weightLabels,
        Pi.zero_apply, zero_sub, Int.cast_neg, neg_neg, Int.cast_sum, Int.cast_mul] using hH i
  · intro j
    simpa only [sub_eq_add_neg] using
      occupationWeight_sub (K := K) M.highestWeightLabels beta gamma j

theorem F_mem_rootGrade (i : Fin 3) (beta : RootCoefficients) (v : V)
    (hv : v ∈ M.rootGrade beta) :
    M.action.F i v ∈ M.rootGrade (beta+Pi.single i 1) := by
  apply M.operator_mem_rootGrade (M.action.F i)
    (fun j => -(rootCartanCoefficient i j : K)) (M.extendedCartan_F i)
    beta (beta+Pi.single i 1) ?_ v hv
  intro j
  simpa only [sub_eq_add_neg] using
    occupationWeight_add_simple (K := K) M.highestWeightLabels beta i j

omit [CharZero K] in
theorem H_mem_rootGrade (i : Fin 3) (beta : RootCoefficients) (v : V)
    (hv : v ∈ M.rootGrade beta) : M.action.H i v ∈ M.rootGrade beta := by
  rw [M.rootGrade_H beta v hv i]
  exact (M.rootGrade beta).smul_mem _ hv

noncomputable def rootGradeE (i : Fin 3) (beta : RootCoefficients) :
    M.rootGrade beta →ₗ[K] M.rootGrade (beta-Pi.single i 1) :=
  (M.action.E i).restrict (M.E_mem_rootGrade i beta)

noncomputable def rootGradeF (i : Fin 3) (beta : RootCoefficients) :
    M.rootGrade beta →ₗ[K] M.rootGrade (beta+Pi.single i 1) :=
  (M.action.F i).restrict (M.F_mem_rootGrade i beta)

noncomputable def rootGradeH (i : Fin 3) (beta : RootCoefficients) :
    Module.End K (M.rootGrade beta) :=
  (M.action.H i).restrict (M.H_mem_rootGrade i beta)

@[simp] theorem rootGradeE_val (i : Fin 3) (beta : RootCoefficients) (v : M.rootGrade beta) :
    (M.rootGradeE i beta v).val = M.action.E i v.val := rfl

@[simp] theorem rootGradeF_val (i : Fin 3) (beta : RootCoefficients) (v : M.rootGrade beta) :
    (M.rootGradeF i beta v).val = M.action.F i v.val := rfl

omit [CharZero K] in
@[simp] theorem rootGradeH_val (i : Fin 3) (beta : RootCoefficients) (v : M.rootGrade beta) :
    (M.rootGradeH i beta v).val = M.action.H i v.val := rfl

omit [CharZero K] in
theorem rootGradeH_eq_smul_id (i : Fin 3) (beta : RootCoefficients) :
    M.rootGradeH i beta = (weightLabels M.highestWeightLabels beta i : K) •
      (LinearMap.id : Module.End K (M.rootGrade beta)) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact M.rootGrade_H beta v.val v.property i

/-- The reverse raising map after a lowering step, with the codomain index
already identified with beta. -/
noncomputable def rootGradeEAfterF (i : Fin 3) (beta : RootCoefficients) :
    M.rootGrade (beta+Pi.single i 1) →ₗ[K] M.rootGrade beta :=
  (M.action.E i).restrict (fun v hv => by
    simpa only [add_sub_cancel_right] using M.E_mem_rootGrade i (beta+Pi.single i 1) v hv)

/-- The reverse lowering map after a raising step, with the codomain index
already identified with beta. -/
noncomputable def rootGradeFAfterE (i : Fin 3) (beta : RootCoefficients) :
    M.rootGrade (beta-Pi.single i 1) →ₗ[K] M.rootGrade beta :=
  (M.action.F i).restrict (fun v hv => by
    simpa only [sub_add_cancel] using M.F_mem_rootGrade i (beta-Pi.single i 1) v hv)

@[simp] theorem rootGradeEAfterF_val (i : Fin 3) (beta : RootCoefficients)
    (v : M.rootGrade (beta+Pi.single i 1)) :
    (M.rootGradeEAfterF i beta v).val = M.action.E i v.val := rfl

@[simp] theorem rootGradeFAfterE_val (i : Fin 3) (beta : RootCoefficients)
    (v : M.rootGrade (beta-Pi.single i 1)) :
    (M.rootGradeFAfterE i beta v).val = M.action.F i v.val := rfl

/-- The original EF relation on a fixed finite root grade, expressed through
the actual maps to adjacent grades and back. -/
theorem rootGrade_EF_sub_FE (i : Fin 3) (beta : RootCoefficients) :
    (M.rootGradeEAfterF i beta).comp (M.rootGradeF i beta) -
      (M.rootGradeFAfterE i beta).comp (M.rootGradeE i beta) = M.rootGradeH i beta := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have h := congrArg (fun a : Module.End K V => a v.val) (M.simpleRoot_EF i)
  simpa only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.comp_apply, Submodule.coe_sub, rootGradeEAfterF_val, rootGradeF_val,
    rootGradeFAfterE_val, rootGradeE_val, rootGradeH_val] using h

end KanadeRussell.Representation.PrincipalHighestWeightModule
