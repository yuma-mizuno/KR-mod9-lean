import KanadeRussell.Tsuchioka.DiagonalHeisenberg
import KanadeRussell.Tsuchioka.ZCyclicGrading

/-! The root modes commute with both halves of the diagonal Heisenberg
action. The concrete Z algebra preserves its vacuum space. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open RootData (Lattice rootWeight)

variable {K : Type*} [Field K] [CharZero K]

theorem rootAnnihilation_diagonalCoordinate (w : K) (β : Lattice)
    (j : Fin 3) (n : Mode) :
    rootAnnihilation w β j (diagonalCoordinate n) =
      HahnSeries.C (diagonalCoordinate n) := by
  have hs : ∑ i : Fin 3,
      tensorExponent (K := K) i j * contraction w n.val / 3 *
        rootWeight (w ^ (n.val : ℤ)) β = 0 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, sum_tensorExponent_left, zero_mul]
  simp only [diagonalCoordinate, map_sum, rootAnnihilation,
    MvPolynomial.eval₂Hom_X', Finset.sum_add_distrib]
  rw [← map_sum]
  have hsingle := map_sum (HahnSeries.single.addMonoidHom (R := Space K) (-(n.val : ℤ)))
    (fun i : Fin 3 => MvPolynomial.C
      (tensorExponent (K := K) i j * contraction w n.val / 3 *
        rootWeight (w ^ (n.val : ℤ)) β)) Finset.univ
  change HahnSeries.single (-(n.val : ℤ))
      (∑ i : Fin 3, MvPolynomial.C
        (tensorExponent (K := K) i j * contraction w n.val / 3 *
          rootWeight (w ^ (n.val : ℤ)) β)) =
    ∑ i : Fin 3, HahnSeries.single (-(n.val : ℤ))
      (MvPolynomial.C
        (tensorExponent (K := K) i j * contraction w n.val / 3 *
          rootWeight (w ^ (n.val : ℤ)) β)) at hsingle
  rw [← hsingle, ← map_sum, hs]
  simp

theorem rootSummand_diagonalCoordinate_mul (w : K) (β : Lattice)
    (j : Fin 3) (n : Mode) (f : Space K) :
    rootSummand w β j (diagonalCoordinate n * f) =
      HahnSeries.C (diagonalCoordinate n) * rootSummand w β j f := by
  change (rootCreation w β j : LaurentSeries (Space K)) *
    rootAnnihilation w β j (diagonalCoordinate n * f) = _
  rw [map_mul, rootAnnihilation_diagonalCoordinate]
  exact mul_left_comm _ _ _

theorem rootField_diagonalCoordinate_mul (w : K) (β : Lattice)
    (n : Mode) (f : Space K) :
    rootField w β (diagonalCoordinate n * f) =
      HahnSeries.C (diagonalCoordinate n) * rootField w β f := by
  simp only [rootField, LinearMap.smul_apply, LinearMap.sum_apply,
    rootSummand_diagonalCoordinate_mul, ← Finset.mul_sum]
  apply HahnSeries.ext
  funext k
  simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
  exact smul_comm _ _ _

theorem rootMode_diagonalCoordinate_mul (w : K) (β : Lattice)
    (n : Mode) (i : ℤ) (f : Space K) :
    rootMode w β i (diagonalCoordinate n * f) =
      diagonalCoordinate n * rootMode w β i f := by
  have h := congrArg (fun g : LaurentSeries (Space K) => g.coeff (-i))
    (rootField_diagonalCoordinate_mul w β n f)
  change (rootField w β (diagonalCoordinate n * f)).coeff (-i) =
    diagonalCoordinate n * (rootField w β f).coeff (-i)
  simpa only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] using h

theorem heisenbergNegative_rootMode (w : K) (n : Mode) (β : Lattice)
    (i : ℤ) (f : Space K) :
    heisenbergNegative n (rootMode w β i f) =
      rootMode w β i (heisenbergNegative n f) :=
  (rootMode_diagonalCoordinate_mul w β n i f).symm

theorem principalDerivation_mem_heisenbergVacuum (w : K)
    (f : Space K) (hf : f ∈ heisenbergVacuum w) :
    principalDerivation f ∈ heisenbergVacuum w :=
  (heisenbergVacuum w).neg_mem (degreeOperator_mem_heisenbergVacuum w f hf)

theorem centralOperator_mem_heisenbergVacuum (w : K)
    (f : Space K) (hf : f ∈ heisenbergVacuum w) :
    centralOperator f ∈ heisenbergVacuum w :=
  (heisenbergVacuum w).smul_mem 3 hf

theorem zOperatorAlgebra_preserves_heisenbergVacuum (w : K)
    (a : Module.End K (Space K)) (ha : a ∈ zOperatorAlgebra w) :
    ∀ f ∈ heisenbergVacuum w, a f ∈ heisenbergVacuum w := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    intro f hf
    rcases ha with ha | ha
    · obtain ⟨⟨β, i⟩, rfl⟩ := ha
      exact rootMode_mem_heisenbergVacuum w β.val i f hf
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact centralOperator_mem_heisenbergVacuum w f hf
      · exact principalDerivation_mem_heisenbergVacuum w f hf
  | algebraMap c =>
    intro f hf
    exact (heisenbergVacuum w).smul_mem c hf
  | add a b ha hb hia hib =>
    intro f hf
    exact (heisenbergVacuum w).add_mem (hia f hf) (hib f hf)
  | mul a b ha hb hia hib =>
    intro f hf
    exact hia _ (hib f hf)

theorem zCyclicSpan_le_heisenbergVacuum (w : K) (seed : Space K)
    (hseed : seed ∈ heisenbergVacuum w) :
    zCyclicSpan w seed ≤ heisenbergVacuum w := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  exact zOperatorAlgebra_preserves_heisenbergVacuum w a ha seed hseed

theorem firstCyclicSpan_le_heisenbergVacuum (w : K) (seed : Space K)
    (hseed : seed ∈ heisenbergVacuum w) :
    firstCyclicSpan w seed ≤ heisenbergVacuum w := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u, rfl⟩
  induction u with
  | nil => exact hseed
  | cons i u ih => exact mode_mem_heisenbergVacuum w i _ ih

/-- The already bounded cyclic degree is contained in the actual positive
Heisenberg kernel. Equality with an affine standard-module vacuum is not an input. -/
theorem cyclicGrade_le_heisenbergVacuum (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : ℕ) :
    Partitions.cyclicGrade (highestWeightAction w) n ≤ heisenbergVacuum w := by
  rw [← zCyclicSpan_vacuum_inf_grade_eq_cyclicGrade w hw n]
  exact le_trans inf_le_left
    (zCyclicSpan_le_heisenbergVacuum w 1 (one_mem_heisenbergVacuum w))

end KanadeRussell.Tsuchioka.Fock
