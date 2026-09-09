import KanadeRussell.Representation.PrincipalModeLocalFiniteness
import KanadeRussell.Representation.LocallyFiniteOperatorSum
import KanadeRussell.Representation.AffineCyclicity

/-! The normal-ordered Casimir sum is an actual endomorphism of the polynomial
Fock space. Its definition is a locally finite sum of the original modes. -/

set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
open KanadeRussell.Representation
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

noncomputable def tensorModeCasimir (w : K) : Module.End K (Space K) :=
  (2 : K) • locallyFiniteOperatorSum
    (fun n : ℕ => normalOrderedMode w ((n : ℤ)+1)) (normalOrderedMode_eventually_zero w)

theorem tensorModeCasimir_apply_eq_sum (w : K) (p : Space K) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → normalOrderedMode w ((n : ℤ)+1) p = 0) :
    tensorModeCasimir w p = (2 : K) •
      ∑ n ∈ Finset.range N, normalOrderedMode w ((n : ℤ)+1) p := by
  rw [tensorModeCasimir, LinearMap.smul_apply,
    locallyFiniteOperatorSum_apply_eq_sum _ _ p N hN]

theorem tensorModeCasimir_kills_primitive (w : K) (hw : w^4-w^2+1=0)
    (p : Space K) (hp : ∀ i, chevalleyE w i p = 0) : tensorModeCasimir w p = 0 := by
  rw [tensorModeCasimir, LinearMap.smul_apply,
    locallyFiniteOperatorSum_apply_eq_zero]
  · exact smul_zero _
  · intro n
    exact normalOrderedMode_kills_primitive w hw p hp ((n:ℤ)+1) (by omega)

theorem normalOrderedMode_mem_grade (w : K) (n d : ℤ) (p : Space K)
    (hp : p ∈ grade d) : normalOrderedMode w n p ∈ grade d := by
  classical
  simp only [normalOrderedMode, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply]
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.smul_mem
  have h := principalMode_mem_grade w (-n) r (d-n) _
    (principalMode_mem_grade w n r d p hp)
  simpa only [sub_neg_eq_add, sub_add_cancel] using h

theorem tensorModeCasimir_mem_grade (w : K) (d : ℤ) (p : Space K)
    (hp : p ∈ grade d) : tensorModeCasimir w p ∈ grade d := by
  obtain ⟨N, hN⟩ := normalOrderedMode_eventually_zero w p
  rw [tensorModeCasimir_apply_eq_sum w p N hN]
  exact (grade d).smul_mem _ ((grade d).sum_mem
    (fun n _ => normalOrderedMode_mem_grade w _ d p hp))

theorem principalMode_mem_tensorOperatorAlgebra (w : K) (n : ℤ) (r : Fin 3) :
    principalMode w n r ∈ tensorOperatorAlgebra w := by
  fin_cases r
  · exact tensorRootMode_mem_tensorOperatorAlgebra w RootData.firstRoot n
  · exact tensorRootMode_mem_tensorOperatorAlgebra w RootData.secondRoot n
  · exact heisenbergMode_mem_tensorOperatorAlgebra w n

theorem normalOrderedMode_mem_tensorOperatorAlgebra (w : K) (n : ℤ) :
    normalOrderedMode w n ∈ tensorOperatorAlgebra w := by
  classical
  exact (tensorOperatorAlgebra w).sum_mem (fun r _ =>
    (tensorOperatorAlgebra w).smul_mem ((tensorOperatorAlgebra w).mul_mem
      (principalMode_mem_tensorOperatorAlgebra w (-n) r)
      (principalMode_mem_tensorOperatorAlgebra w n r)) _)

theorem tensorModeCasimir_mem_tensorCyclicSpan (w : K) (seed p : Space K)
    (hp : p ∈ tensorCyclicSpan w seed) : tensorModeCasimir w p ∈ tensorCyclicSpan w seed := by
  obtain ⟨N, hN⟩ := normalOrderedMode_eventually_zero w p
  rw [tensorModeCasimir_apply_eq_sum w p N hN]
  exact (tensorCyclicSpan w seed).smul_mem _ ((tensorCyclicSpan w seed).sum_mem
    (fun n _ => tensorCyclicSpan_algebra_mem w seed _
      (normalOrderedMode_mem_tensorOperatorAlgebra w _) p hp))

noncomputable def tensorCyclicModeCasimir (w : K) (seed : Space K) :
    Module.End K (tensorCyclicSpan w seed) :=
  (tensorModeCasimir w).restrict (tensorModeCasimir_mem_tensorCyclicSpan w seed)

@[simp] theorem tensorCyclicModeCasimir_val (w : K) (seed : Space K)
    (p : tensorCyclicSpan w seed) :
    (tensorCyclicModeCasimir w seed p).val = tensorModeCasimir w p.val := rfl

end KanadeRussell.Tsuchioka.Fock
