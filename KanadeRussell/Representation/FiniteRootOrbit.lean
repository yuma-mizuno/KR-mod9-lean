import KanadeRussell.Representation.CartanRankOneFiniteness

/-! Actual finite simple-root orbits, stable under the full Cartan action. -/
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

def rootCartanCoefficient (i : Fin 3) : Fin 4 → ℤ :=
  Fin.cases 1 (fun j => affineCartanMatrix j i)

theorem extendedCartan_E (i : Fin 3) (j : Fin 4) :
    ⁅M.extendedCartan j, M.action.E i⁆ = (rootCartanCoefficient i j : K) • M.action.E i := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa [extendedCartan, rootCartanCoefficient] using M.principalDerivation_E i
  · simpa only [extendedCartan, rootCartanCoefficient, Fin.cases_succ,
      Int.cast_smul_eq_zsmul] using M.action.HE k i

theorem extendedCartan_F (i : Fin 3) (j : Fin 4) :
    ⁅M.extendedCartan j, M.action.F i⁆ = (-(rootCartanCoefficient i j : K)) • M.action.F i := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa [extendedCartan, rootCartanCoefficient] using M.principalDerivation_F i
  · simpa only [extendedCartan, rootCartanCoefficient, Fin.cases_succ,
      neg_smul, Int.cast_smul_eq_zsmul] using M.action.HF k i

theorem simpleRoot_EF (i : Fin 3) : ⁅M.action.E i, M.action.F i⁆ = M.action.H i := by
  simpa using M.action.EF i i

theorem simpleRoot_HE (i : Fin 3) : ⁅M.action.H i, M.action.E i⁆ = (2:K) • M.action.E i := by
  have h := M.extendedCartan_E i i.succ
  have hii : affineCartanMatrix i i = 2 := by fin_cases i <;> rfl
  simpa only [extendedCartan, rootCartanCoefficient, Fin.cases_succ, hii, Int.cast_ofNat] using h

theorem simpleRoot_HF (i : Fin 3) : ⁅M.action.H i, M.action.F i⁆ = (-2:K) • M.action.F i := by
  have h := M.extendedCartan_F i i.succ
  have hii : affineCartanMatrix i i = 2 := by fin_cases i <;> rfl
  simpa only [extendedCartan, rootCartanCoefficient, Fin.cases_succ, hii, Int.cast_ofNat] using h

noncomputable def simpleRootOrbit (i : Fin 3) (v : V) : Submodule K V :=
  rankOneOrbit (M.action.E i) (M.action.F i) v

theorem self_mem_simpleRootOrbit (i : Fin 3) (v : V) : v ∈ M.simpleRootOrbit i v :=
  self_mem_rankOneOrbit _ _ _

theorem simpleRootOrbit_F_stable (i : Fin 3) (v : V) :
    ∀ x ∈ M.simpleRootOrbit i v, M.action.F i x ∈ M.simpleRootOrbit i v :=
  rankOneOrbit_F_stable _ _ _

theorem simpleRootOrbit_E_stable (i : Fin 3) (v : V) (mu : Fin 4 → K)
    (hv : v ∈ M.extendedWeightSpace mu) :
    ∀ x ∈ M.simpleRootOrbit i v, M.action.E i x ∈ M.simpleRootOrbit i v :=
  rankOneOrbit_E_stable _ _ _ v (mu i.succ) (M.simpleRoot_EF i)
    (M.simpleRoot_HE i) (M.simpleRoot_HF i) ((M.mem_extendedWeightSpace mu v).mp hv i.succ)

theorem simpleRootOrbit_Cartan_stable (i : Fin 3) (v : V) (mu : Fin 4 → K)
    (hv : v ∈ M.extendedWeightSpace mu) (j : Fin 4) :
    ∀ x ∈ M.simpleRootOrbit i v, M.extendedCartan j x ∈ M.simpleRootOrbit i v :=
  rankOneOrbit_Cartan_stable _ _ _ v (rootCartanCoefficient i j : K) (mu j)
    (M.extendedCartan_E i j) (M.extendedCartan_F i j) ((M.mem_extendedWeightSpace mu v).mp hv j)

theorem simpleRootOrbit_finite (i : Fin 3) (v : V) (mu : Fin 4 → K)
    (hv : v ∈ M.extendedWeightSpace mu) : Module.Finite K (M.simpleRootOrbit i v) :=
  rankOneOrbit_finite _ _ _ v (mu i.succ) (M.simpleRoot_EF i)
    (M.simpleRoot_HE i) (M.simpleRoot_HF i) ((M.mem_extendedWeightSpace mu v).mp hv i.succ)
    (M.E_locally_nilpotent i) (M.F_locally_nilpotent i)

end KanadeRussell.Representation.PrincipalHighestWeightModule
