import KanadeRussell.Representation.ShiftedChevalleyQuotient
import Mathlib.Data.Finsupp.Interval

/-! Finite-dimensional absolute polynomial grades and their cyclic quotient images. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

theorem finite_monomials_weight_le (n : ℕ) :
    {f : (Fin 3 × Mode) →₀ ℕ | Finsupp.weight (fun s => s.2.val) f ≤ n}.Finite := by
  classical
  have hs : {s : Fin 3 × Mode | s.2.val ≤ n}.Finite := by
    have hm : {m : Mode | m.val ≤ n}.Finite :=
      (Set.finite_Iic n).preimage (Set.injOn_of_injective Subtype.val_injective)
    exact (Set.finite_univ.prod hm).subset (by intro s h; exact ⟨Set.mem_univ _, h⟩)
  let bound : (Fin 3 × Mode) →₀ ℕ := ∑ s ∈ hs.toFinset, Finsupp.single s n
  apply (Set.finite_Iic bound).subset
  intro f hf s
  by_cases h : s.2.val ≤ n
  · have he : bound s = n := by simp [bound, Finsupp.single_apply, hs.mem_toFinset, h]
    rw [he]
    exact (Finsupp.le_weight (fun s : Fin 3 × Mode => s.2.val)
      (Nat.ne_of_gt (mode_pos s.2)) f).trans hf
  · have hz : f s = 0 := by
      by_contra hn
      exact h ((Finsupp.le_weight_of_ne_zero' (fun s : Fin 3 × Mode => s.2.val) hn).trans hf)
    rw [hz]
    exact Nat.zero_le _

theorem finite_monomials_weight_eq (d : ℤ) :
    {f : (Fin 3 × Mode) →₀ ℕ | Finsupp.weight variableWeight f = d}.Finite := by
  apply (finite_monomials_weight_le d.toNat).subset
  intro f hf
  have he : (Finsupp.weight (fun s : Fin 3 × Mode => s.2.val) f : ℤ) =
      Finsupp.weight variableWeight f := by
    simp [Finsupp.weight_apply, Finsupp.sum, variableWeight, Nat.cast_sum, Nat.cast_mul]
  have hle : (Finsupp.weight (fun s : Fin 3 × Mode => s.2.val) f : ℤ) ≤ (d.toNat:ℤ) := by
    rw [he, hf]
    omega
  exact_mod_cast hle

omit [CharZero K] in
theorem grade_finite (d : ℤ) : Module.Finite K (grade (K := K) d) := by
  classical
  rw [grade, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  letI : Finite {f : (Fin 3 × Mode) →₀ ℕ | Finsupp.weight variableWeight f = d} :=
    (finite_monomials_weight_eq d).to_subtype
  exact Module.Finite.of_injective
    (Finsupp.supportedEquivFinsupp (R := K)
      {f : (Fin 3 × Mode) →₀ ℕ | Finsupp.weight variableWeight f = d}).toLinearMap
    (Finsupp.supportedEquivFinsupp (R := K)
      {f : (Fin 3 × Mode) →₀ ℕ | Finsupp.weight variableWeight f = d}).injective

theorem shiftedQuotientCyclicGrade_finite (w : K) (seed : Space K) (d : ℤ)
    (S : Submodule K (Space K)) (n : ℕ) :
    Module.Finite K (shiftedQuotientCyclicGrade w seed d S n) := by
  letI := grade_finite (K := K) (d+n)
  letI : Module.Finite K (tensorCyclicSpan w seed ⊓ grade (d+n) : Submodule K (Space K)) :=
    Submodule.finiteDimensional_of_le inf_le_right
  unfold shiftedQuotientCyclicGrade
  infer_instance

end KanadeRussell.Tsuchioka.Fock
