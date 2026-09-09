import KanadeRussell.Tsuchioka.TensorLieDerivation
import KanadeRussell.Representation.ModeCasimirOperatorCancellation
import KanadeRussell.Representation.PrincipalModeLocalFiniteness

/-! Cartan action on the three principal-mode coordinates. An inactive
Heisenberg coordinate evaluates to zero; no independence is assumed here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

noncomputable def principalModeCombination (w : K) (n : ℤ) :
    (Fin 3 → K) →ₗ[K] Module.End K (Space K) where
  toFun v := ∑ r, v r • principalMode w n r
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [mul_smul, Finset.smul_sum]

theorem principalModeCombination_apply (w : K) (n : ℤ) (v : Fin 3 → K) :
    principalModeCombination w n v = ∑ r, v r • principalMode w n r := rfl

noncomputable def principalCartanMatrix (w : K) (n : ℤ) (i : Fin 3) :
    Matrix (Fin 3) (Fin 3) K := fun t r =>
  ∑ s : Fin 3, chevalleyHCoordinates w i s.castSucc *
    tensorModeStructure w 0 n s.castSucc r.castSucc t.castSucc

theorem chevalleyH_eq_sum_principalMode (w : K) (i : Fin 3) :
    chevalleyH w i = principalModeCombination w 0
      (fun r => chevalleyHCoordinates w i r.castSucc) +
        chevalleyHCoordinates w i 3 • (1 : Module.End K (Space K)) := by
  rw [chevalleyH, tensorModeEvaluate_apply]
  simp [principalModeCombination_apply, Fin.sum_univ_three, principalMode,
    tensorModeBasis, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, add_assoc]

theorem chevalleyH_lie_principalMode (w : K) (hw : w^4-w^2+1=0)
    (n : ℤ) (hn : n ≠ 0) (i r : Fin 3) :
    ⁅chevalleyH w i, principalMode w n r⁆ =
      ∑ t : Fin 3, principalCartanMatrix w n i t r • principalMode w n t := by
  rw [chevalleyH_eq_sum_principalMode, add_lie]
  have hcentral : ⁅chevalleyHCoordinates w i 3 • (1 : Module.End K (Space K)),
      principalMode w n r⁆ = 0 := by
    simp [Ring.lie_def, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  rw [hcentral, add_zero, principalModeCombination_apply, sum_lie]
  have hsmul (c : K) (A B : Module.End K (Space K)) :
      ⁅c • A, B⁆ = c • ⁅A, B⁆ := by
    simp only [Ring.lie_def, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  simp only [hsmul, principalMode_lie_noncentral w hw 0 n (by simpa using hn),
    zero_add, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [principalCartanMatrix, Finset.sum_smul]

theorem chevalleyH_lie_principalModeCombination (w : K) (hw : w^4-w^2+1=0)
    (n : ℤ) (hn : n ≠ 0) (i : Fin 3) (v : Fin 3 → K) :
    ⁅chevalleyH w i, principalModeCombination w n v⁆ =
      principalModeCombination w n ((principalCartanMatrix w n i).mulVec v) := by
  rw [principalModeCombination_apply, lie_sum]
  have hsmul (c : K) (A B : Module.End K (Space K)) :
      ⁅A, c • B⁆ = c • ⁅A, B⁆ := by
    simp only [Ring.lie_def, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  simp only [hsmul, chevalleyH_lie_principalMode w hw n hn,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, principalModeCombination_apply]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_comm]

theorem principalModeCombination_eigenoperator (w : K) (hw : w^4-w^2+1=0)
    (n : ℤ) (hn : n ≠ 0) (i : Fin 3) (v : Fin 3 → K) (c : K)
    (hv : (principalCartanMatrix w n i).mulVec v = c • v) :
    ⁅chevalleyH w i, principalModeCombination w n v⁆ =
      c • principalModeCombination w n v := by
  rw [chevalleyH_lie_principalModeCombination w hw n hn, hv, map_smul]

theorem principalModeCombination_mem_grade (w : K) (n : ℤ) (v : Fin 3 → K)
    (d : ℤ) (p : Space K) (hp : p ∈ Tsuchioka.Fock.grade d) :
    principalModeCombination w n v p ∈ Tsuchioka.Fock.grade (d-n) := by
  simp only [principalModeCombination_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ (fun r _ => Submodule.smul_mem _ _
    (principalMode_mem_grade w n r d p hp))

theorem principalCartanMatrix_eq_of_mod (w : K) (hw : w^4-w^2+1=0)
    (n m : ℤ) (hnm : n % 12 = m % 12) (i : Fin 3) :
    principalCartanMatrix w n i = principalCartanMatrix w m i := by
  funext t r
  apply Finset.sum_congr rfl
  intro s hs
  rw [tensorModeStructure_noncentral_eq_of_mod w hw 0 n 0 m rfl hnm]

theorem principalModeCombination_eq_evaluate (w : K) (n : ℤ) (v : Fin 3 → K) :
    principalModeCombination w n v = tensorModeEvaluate w n ![v 0, v 1, v 2, 0] := by
  rw [tensorModeEvaluate_apply]
  simp [principalModeCombination_apply, Fin.sum_univ_three, principalMode,
    tensorModeBasis, Matrix.cons_val_two, Matrix.cons_val_succ,
    Matrix.vecHead, Matrix.vecTail, add_assoc]

theorem principalModeCombination_eq_of_inactive (w : K) (n : ℤ)
    (hn : ¬ IsMode n.natAbs) (v : Fin 3 → K) :
    principalModeCombination w n v = principalModeCombination w n ![v 0, v 1, 0] := by
  rw [principalModeCombination_eq_evaluate, principalModeCombination_eq_evaluate]
  simp [tensorModeEvaluate_apply, heisenbergMode_not_mode w n hn]

theorem principalDerivation_lie_principalModeCombination (w : K) (n : ℤ)
    (v : Fin 3 → K) :
    ⁅Fock.principalDerivation (K := K), principalModeCombination w n v⁆ =
      (n : K) • principalModeCombination w n v := by
  rw [principalModeCombination_eq_evaluate, principalDerivation_tensorModeEvaluate_lie]
  simp

end KanadeRussell.Representation
