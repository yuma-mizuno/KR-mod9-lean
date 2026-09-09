import KanadeRussell.Representation.RankOneLocalFiniteness
import KanadeRussell.Representation.HighestWeightSupport

/-! Rank-one consequences for arbitrary weight vectors in an integrable
highest-weight module. No finite-dimensionality of the ambient module is used. -/
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

private theorem root_EF (i : Fin 3) : ⁅M.action.E i, M.action.F i⁆ = M.action.H i := by
  simpa using M.action.EF i i

private theorem root_HE (i : Fin 3) : ⁅M.action.H i, M.action.E i⁆ = (2:K) • M.action.E i := by
  rw [M.action.HE]
  have hii : affineCartanMatrix i i = 2 := by fin_cases i <;> rfl
  rw [hii]
  simp [← Int.cast_smul_eq_zsmul K]

private theorem root_HF (i : Fin 3) : ⁅M.action.H i, M.action.F i⁆ = (-2:K) • M.action.F i := by
  rw [M.action.HF]
  have hii : affineCartanMatrix i i = 2 := by fin_cases i <;> rfl
  rw [hii]
  simp [neg_smul, ← Int.cast_smul_eq_zsmul K]

/-- Every nonzero primitive joint weight vector has dominant integral weight,
with the exact root-string endpoints specified by its Dynkin labels. -/
theorem primitive_weight_strings (mu : Fin 3 → K) (v : V) (hv : v ≠ 0)
    (hH : ∀ i, M.action.H i v = mu i • v) (hE : ∀ i, M.action.E i v = 0) :
    ∃ lambda : Fin 3 → ℕ, ∀ i,
      mu i = (lambda i : K) ∧ ((M.action.F i)^(lambda i+1)) v = 0 ∧
      ∀ j ≤ lambda i, ((M.action.F i)^j) v ≠ 0 := by
  classical
  have h (i : Fin 3) := rankOne_string_endpoint (M.action.E i) (M.action.F i)
    (M.action.H i) (mu i) v (M.root_EF i) (M.root_HF i) hv (hE i) (hH i)
    (M.F_locally_nilpotent i v)
  exact ⟨fun i => Classical.choose (h i), fun i => Classical.choose_spec (h i)⟩

theorem primitive_weight_dominant (mu : Fin 3 → K) (v : V) (hv : v ≠ 0)
    (hH : ∀ i, M.action.H i v = mu i • v) (hE : ∀ i, M.action.E i v = 0) :
    ∃ lambda : Fin 3 → ℕ, ∀ i, mu i = (lambda i : K) := by
  obtain ⟨lambda, hlambda⟩ := M.primitive_weight_strings mu v hv hH hE
  exact ⟨lambda, fun i => (hlambda i).1⟩

/-- A joint Cartan weight vector is contained in a finite-dimensional stable
submodule for each individual simple-root rank-one action. -/
theorem weight_vector_rankOne_finite (mu : Fin 3 → K) (v : V)
    (hH : ∀ i, M.action.H i v = mu i • v) (i : Fin 3) :
    ∃ S : Submodule K V, v ∈ S ∧ Module.Finite K S ∧
      (∀ x ∈ S, M.action.E i x ∈ S) ∧
      (∀ x ∈ S, M.action.F i x ∈ S) ∧
      (∀ x ∈ S, M.action.H i x ∈ S) :=
  rankOne_locally_finite (M.action.E i) (M.action.F i) (M.action.H i)
    (mu i) v (M.root_EF i) (M.root_HE i) (M.root_HF i) (hH i)
    (M.E_locally_nilpotent i) (M.F_locally_nilpotent i)

end KanadeRussell.Representation.PrincipalHighestWeightModule
