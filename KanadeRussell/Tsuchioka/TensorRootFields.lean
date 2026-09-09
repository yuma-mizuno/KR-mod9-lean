import KanadeRussell.Tsuchioka.VacuumPolynomialModel
import KanadeRussell.Tsuchioka.RootFock

/-! The tensor root fields from the source's basic-representation formula
with trivial lattice character. Their affine Lie relations are not assumed. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open PowerSeries
open RootData (Lattice rootWeight)

variable {K : Type*} [Field K] [CharZero K]

noncomputable def tensorRootCreationLog (w : K) (β : Lattice) (j : Fin 3) :
    PowerSeries (Space K) :=
  PowerSeries.mk fun n => if h : IsMode n then
    MvPolynomial.C (12 * rootWeight (w ^ (-(n : ℤ))) β / (n : K)) *
      MvPolynomial.X (j, (⟨n, h⟩ : Mode))
    else 0

noncomputable def diagonalRootCreationLog (w : K) (β : Lattice) :
    PowerSeries (Space K) :=
  PowerSeries.mk fun n => if h : IsMode n then
    MvPolynomial.C (4 * rootWeight (w ^ (-(n : ℤ))) β / (n : K)) *
      diagonalCoordinate (⟨n, h⟩ : Mode)
    else 0

@[simp] theorem constantCoeff_tensorRootCreationLog (w : K) (β : Lattice) (j : Fin 3) :
    constantCoeff (tensorRootCreationLog w β j) = 0 := by
  simp [tensorRootCreationLog, IsMode]

@[simp] theorem constantCoeff_diagonalRootCreationLog (w : K) (β : Lattice) :
    constantCoeff (diagonalRootCreationLog w β) = 0 := by
  simp [diagonalRootCreationLog, IsMode]

theorem tensorRootCreationLog_eq_diagonal_add_root (w : K) (β : Lattice) (j : Fin 3) :
    tensorRootCreationLog w β j = diagonalRootCreationLog w β + rootCreationLog w β j := by
  apply PowerSeries.ext
  intro n
  simp only [tensorRootCreationLog, diagonalRootCreationLog, rootCreationLog,
    coeff_mk, map_add, creationLog]
  by_cases hn : IsMode n
  · simp only [dif_pos hn, coeff_mk]
    fin_cases j <;>
      simp [Fin.sum_univ_three, tensorExponent, diagonalCoordinate, MvPolynomial.C_mul'] <;>
      module
  · simp [hn]

noncomputable def tensorRootCreation (w : K) (β : Lattice) (j : Fin 3) :
    PowerSeries (Space K) :=
  FormalSeries.exponential (tensorRootCreationLog w β j)

noncomputable def diagonalRootCreation (w : K) (β : Lattice) : PowerSeries (Space K) :=
  FormalSeries.exponential (diagonalRootCreationLog w β)

theorem tensorRootCreation_eq_diagonal_mul_root (w : K) (β : Lattice) (j : Fin 3) :
    tensorRootCreation w β j = diagonalRootCreation w β * rootCreation w β j := by
  rw [tensorRootCreation, tensorRootCreationLog_eq_diagonal_add_root,
    FormalSeries.exponential_add (constantCoeff_diagonalRootCreationLog w β)
      (constantCoeff_rootCreationLog w β j)]
  rfl

/-- The level-one annihilation substitution in the j-th tensor factor. -/
noncomputable def tensorRootAnnihilation (w : K) (β : Lattice) (j : Fin 3) :
    Space K →+* LaurentSeries (Space K) :=
  MvPolynomial.eval₂Hom (HahnSeries.C.comp MvPolynomial.C) fun s =>
    HahnSeries.C (MvPolynomial.X s) +
      HahnSeries.single (-(s.2.val : ℤ)) (MvPolynomial.C
        (if s.1 = j then -contraction w s.2.val * rootWeight (w ^ (s.2.val : ℤ)) β else 0))

theorem tensorRootAnnihilation_X_eq_root (w : K) (β : Lattice) (j : Fin 3)
    (s : Fin 3 × Mode) :
    tensorRootAnnihilation w β j (MvPolynomial.X s) =
      rootAnnihilation w β j (MvPolynomial.X s) -
        HahnSeries.single (-(s.2.val : ℤ)) (MvPolynomial.C
          (contraction w s.2.val / 3 * rootWeight (w ^ (s.2.val : ℤ)) β)) := by
  have hs : (if s.1 = j then -contraction w s.2.val *
      rootWeight (w ^ (s.2.val : ℤ)) β else 0) =
      tensorExponent (K := K) s.1 j * contraction w s.2.val / 3 *
        rootWeight (w ^ (s.2.val : ℤ)) β -
      contraction w s.2.val / 3 * rootWeight (w ^ (s.2.val : ℤ)) β := by
    by_cases h : s.1 = j <;> simp [tensorExponent, Fin.val_inj, h] <;> ring
  simp only [tensorRootAnnihilation, rootAnnihilation, MvPolynomial.eval₂Hom_X']
  rw [hs, map_sub, HahnSeries.single_sub]
  abel

theorem tensorRootAnnihilation_relativeEmbedding_X (w : K) (β : Lattice) (j : Fin 3)
    (s : Fin 2 × Mode) :
    tensorRootAnnihilation w β j (relativeEmbedding (MvPolynomial.X s)) =
      rootAnnihilation w β j (relativeEmbedding (MvPolynomial.X s)) := by
  rw [relativeEmbedding_X, map_sub, map_sub,
    tensorRootAnnihilation_X_eq_root, tensorRootAnnihilation_X_eq_root]
  abel

theorem tensorRootAnnihilation_relativeEmbedding (w : K) (β : Lattice) (j : Fin 3)
    (f : RelativeSpace K) :
    tensorRootAnnihilation w β j (relativeEmbedding f) =
      rootAnnihilation w β j (relativeEmbedding f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [relativeEmbedding, tensorRootAnnihilation, rootAnnihilation]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f s hf =>
    simp only [map_mul, hf, tensorRootAnnihilation_relativeEmbedding_X]

theorem tensorRootAnnihilation_eq_on_vacuum (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (f : Space K) (hf : f ∈ heisenbergVacuum w) :
    tensorRootAnnihilation w β j f = rootAnnihilation w β j f := by
  have he : relativeEmbedding (relativeExtraction f) = f := by
    rw [relativeEmbedding_relativeExtraction,
      (mem_heisenbergVacuum_iff_relativeProjection w hw f).mp hf]
  calc
    tensorRootAnnihilation w β j f =
        tensorRootAnnihilation w β j (relativeEmbedding (relativeExtraction f)) :=
      congrArg (tensorRootAnnihilation w β j) he.symm
    _ = rootAnnihilation w β j (relativeEmbedding (relativeExtraction f)) :=
      tensorRootAnnihilation_relativeEmbedding w β j _
    _ = rootAnnihilation w β j f := congrArg (rootAnnihilation w β j) he

noncomputable def tensorRootSummand (w : K) (β : Lattice) (j : Fin 3) :
    Space K →ₗ[K] LaurentSeries (Space K) where
  toFun p := (tensorRootCreation w β j : LaurentSeries (Space K)) * tensorRootAnnihilation w β j p
  map_add' p q := by simp [map_add, mul_add]
  map_smul' c p := by
    change (tensorRootCreation w β j : LaurentSeries (Space K)) *
      tensorRootAnnihilation w β j (c • p) =
        c • ((tensorRootCreation w β j : LaurentSeries (Space K)) * tensorRootAnnihilation w β j p)
    rw [Algebra.smul_def c p, MvPolynomial.algebraMap_eq, map_mul]
    have hc : tensorRootAnnihilation w β j (MvPolynomial.C c) =
        HahnSeries.C (MvPolynomial.C c) := by
      simp [tensorRootAnnihilation]
    rw [hc, mul_left_comm]
    apply HahnSeries.ext
    funext n
    simp [HahnSeries.coeff_smul, Algebra.smul_def]

noncomputable def tensorRootField (w : K) (β : Lattice) :
    Space K →ₗ[K] LaurentSeries (Space K) :=
  (1 / 12 : K) • ∑ j : Fin 3, tensorRootSummand w β j

noncomputable def tensorRootMode (w : K) (β : Lattice) (i : ℤ) : Module.End K (Space K) where
  toFun p := (tensorRootField w β p).coeff (-i)
  map_add' p q := by simp [HahnSeries.coeff_add]
  map_smul' c p := by simp [HahnSeries.coeff_smul]

theorem tensorRootSummand_on_vacuum (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (f : Space K) (hf : f ∈ heisenbergVacuum w) :
    tensorRootSummand w β j f =
      (diagonalRootCreation w β : LaurentSeries (Space K)) * rootSummand w β j f := by
  change (tensorRootCreation w β j : LaurentSeries (Space K)) * tensorRootAnnihilation w β j f =
    (diagonalRootCreation w β : LaurentSeries (Space K)) *
      ((rootCreation w β j : LaurentSeries (Space K)) * rootAnnihilation w β j f)
  rw [tensorRootCreation_eq_diagonal_mul_root, PowerSeries.coe_mul,
    tensorRootAnnihilation_eq_on_vacuum w hw β j f hf, mul_assoc]

theorem laurent_smul_eq_coefficient_smul (c : K) (f : LaurentSeries (Space K)) :
    c • f = (MvPolynomial.C c : Space K) • f := by
  apply HahnSeries.ext
  funext n
  simp [HahnSeries.coeff_smul, Algebra.smul_def]

/-- On every vacuum input, X is the diagonal creation factor times Z. -/
theorem tensorRootField_on_vacuum (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (f : Space K) (hf : f ∈ heisenbergVacuum w) :
    tensorRootField w β f =
      (diagonalRootCreation w β : LaurentSeries (Space K)) * rootField w β f := by
  simp only [tensorRootField, rootField, LinearMap.smul_apply, LinearMap.sum_apply,
    tensorRootSummand_on_vacuum w hw β _ f hf, ← Finset.mul_sum]
  simp_rw [laurent_smul_eq_coefficient_smul, ← HahnSeries.C_mul_eq_smul]
  exact mul_left_comm _ _ _

noncomputable def inverseDiagonalRootCreation (w : K) (β : Lattice) :
    PowerSeries (Space K) :=
  FormalSeries.exponential (-diagonalRootCreationLog w β)

theorem inverseDiagonalRootCreation_mul (w : K) (β : Lattice) :
    inverseDiagonalRootCreation w β * diagonalRootCreation w β = 1 := by
  rw [inverseDiagonalRootCreation, diagonalRootCreation, mul_comm]
  exact FormalSeries.exponential_mul_neg (constantCoeff_diagonalRootCreationLog w β)

/-- Inverse dressing also holds as an equality of full Laurent fields. -/
theorem rootField_eq_inverse_tensorRootField_on_vacuum (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (β : Lattice)
    (f : Space K) (hf : f ∈ heisenbergVacuum w) :
    rootField w β f =
      (inverseDiagonalRootCreation w β : LaurentSeries (Space K)) * tensorRootField w β f := by
  rw [tensorRootField_on_vacuum w hw β f hf, ← mul_assoc, ← PowerSeries.coe_mul,
    inverseDiagonalRootCreation_mul, PowerSeries.coe_one, one_mul]

theorem tensorRootMode_locally_finite (w : K) (β : Lattice) (f : Space K) :
    ∃ N : ℕ, ∀ i : ℤ, (N : ℤ) < i → tensorRootMode w β i f = 0 := by
  refine ⟨(-(tensorRootField w β f).order).toNat, ?_⟩
  intro i hi
  change (tensorRootField w β f).coeff (-i) = 0
  apply HahnSeries.coeff_eq_zero_of_lt_order
  omega

end KanadeRussell.Tsuchioka.Fock
