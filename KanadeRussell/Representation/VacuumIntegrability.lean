import KanadeRussell.Representation.CyclicIntegrability
import KanadeRussell.Tsuchioka.AffineVacuumIntegrability
import KanadeRussell.Heisenberg.PolynomialGrading

/-! Integrability of the actual vacuum cyclic tensor representation. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
open KanadeRussell.Representation KanadeRussell.Heisenberg
variable {K : Type*} [Field K] [CharZero K]

theorem chevalleyE_mem_grade (w : K) (i : Fin 3) (d : ℤ) (p : Space K)
    (hp : p ∈ grade d) : chevalleyE w i p ∈ grade (d-1) := by
  have hc : chevalleyECoordinates w i 3 = 0 := by
    fin_cases i <;> norm_num [chevalleyECoordinates, Matrix.cons_val_two, Matrix.cons_val_three]
  have hh : heisenbergMode w 1 p ∈ grade (d-1) := by
    have he := heisenbergMode_positive w firstMode
    change heisenbergMode w 1 = heisenbergPositive w firstMode at he
    rw [he, heisenbergPositive_apply]
    exact (grade (d-1)).smul_mem _ (diagonalDerivative_mem_grade firstMode d p hp)
  simp only [chevalleyE, tensorModeEvaluate_apply, LinearMap.add_apply, LinearMap.smul_apply,
    hc, zero_smul, add_zero]
  exact (grade (d-1)).add_mem
    ((grade (d-1)).add_mem
      ((grade (d-1)).smul_mem _ (tensorRootMode_mem_grade w _ 1 d p hp))
      ((grade (d-1)).smul_mem _ (tensorRootMode_mem_grade w _ 1 d p hp)))
    ((grade (d-1)).smul_mem _ hh)

theorem chevalleyE_pow_mem_grade (w : K) (i : Fin 3) (n : ℕ) (d : ℤ) (p : Space K)
    (hp : p ∈ grade d) : ((chevalleyE w i)^n) p ∈ grade (d-n) := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := chevalleyE_mem_grade w i (d-n) _ ih
    simpa only [Nat.cast_add, Nat.cast_one, sub_sub] using h

theorem chevalleyE_locally_nilpotent_of_grade (w : K) (i : Fin 3) (d : ℤ)
    (p : Space K) (hp : p ∈ grade d) : ∃ n : ℕ, ((chevalleyE w i)^n) p = 0 := by
  refine ⟨d.toNat+1, ?_⟩
  have h := chevalleyE_pow_mem_grade w i (d.toNat+1) d p hp
  rw [grade_negative _ (by omega), Submodule.mem_bot] at h
  exact h

/-- Raising operators are locally nilpotent on every polynomial, with no phase relation needed. -/
theorem chevalleyE_locally_nilpotent (w : K) (i : Fin 3) (p : Space K) :
    ∃ n : ℕ, ((chevalleyE w i)^n) p = 0 := by
  apply (mem_locallyNilpotentVectors (chevalleyE w i) p).mp
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    apply (mem_locallyNilpotentVectors _ _).mpr
    exact chevalleyE_locally_nilpotent_of_grade w i (Finsupp.weight variableWeight m) _
      (MvPolynomial.isWeightedHomogeneous_monomial variableWeight m c rfl)
  | add p q hp hq => exact (locallyNilpotentVectors (chevalleyE w i)).add_mem hp hq

theorem chevalleyF_locally_nilpotent_on_vacuum_tensor (w : K) (hw : w^4-w^2+1=0)
    (i : Fin 3) (p : Space K) (hp : p ∈ tensorCyclicSpan w 1) :
    ∃ n : ℕ, ((chevalleyF w i)^n) p = 0 :=
  chevalleyF_locally_nilpotent_on_tensorCyclicSpan w hw 1 0
    (MvPolynomial.isWeightedHomogeneous_one K variableWeight) i
    ⟨_, chevalleyF_vacuum_integrability w hw i⟩ p hp

/-- Integrability here means local nilpotence of all six concrete simple-root
operators on the actual cyclic space; no standard-module identification is claimed. -/
theorem vacuum_tensor_integrable (w : K) (hw : w^4-w^2+1=0) :
    ∀ i : Fin 3, ∀ p ∈ tensorCyclicSpan w (1 : Space K),
      (∃ n : ℕ, ((chevalleyE w i)^n) p = 0) ∧
      (∃ n : ℕ, ((chevalleyF w i)^n) p = 0) := by
  intro i p hp
  exact ⟨chevalleyE_locally_nilpotent w i p,
    chevalleyF_locally_nilpotent_on_vacuum_tensor w hw i p hp⟩

end KanadeRussell.Tsuchioka.Fock
