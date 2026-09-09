import KanadeRussell.Tsuchioka.TensorRootFields
import KanadeRussell.Tsuchioka.AnnihilationCovariance

/-! Root addition and Coxeter covariance for the source tensor fields,
including the annihilation substitutions and every integer mode. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open PowerSeries
open RootData (Lattice simpleRoot coxeter rootWeight)
open FormalSeries (laurentRescale)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorRootCreationLog_add (w : K) (β γ : Lattice) (j : Fin 3) :
    tensorRootCreationLog w (β + γ) j =
      tensorRootCreationLog w β j + tensorRootCreationLog w γ j := by
  ext n
  simp only [tensorRootCreationLog, coeff_mk, map_add, RootData.rootWeight_add]
  split_ifs <;> simp [mul_add, add_div, map_add, add_mul]

theorem tensorRootCreation_add (w : K) (β γ : Lattice) (j : Fin 3) :
    tensorRootCreation w (β + γ) j = tensorRootCreation w β j * tensorRootCreation w γ j := by
  rw [tensorRootCreation, tensorRootCreationLog_add,
    FormalSeries.exponential_add (constantCoeff_tensorRootCreationLog w β j)
      (constantCoeff_tensorRootCreationLog w γ j)]
  rfl

theorem tensorRootCreationLog_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (p : ℕ) :
    tensorRootCreationLog w ((coxeter^[p]) β) j =
      rescale (MvPolynomial.C (w ^ (-(p : ℤ)))) (tensorRootCreationLog w β j) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_rescale]
  simp only [tensorRootCreationLog, coeff_mk]
  by_cases hn : IsMode n
  · simp only [dif_pos hn]
    have ht := mode_inverse_cyclotomic w hw (⟨n, hn⟩ : Mode)
    have hp : (w ^ (-(n : ℤ))) ^ p = (w ^ (-(p : ℤ))) ^ n := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
      congr 1
      ring
    rw [RootData.rootWeight_iterate _ ht, hp]
    have hc : 12 * ((w ^ (-(p : ℤ))) ^ n * rootWeight (w ^ (-(n : ℤ))) β) / (n : K) =
        (w ^ (-(p : ℤ))) ^ n * (12 * rootWeight (w ^ (-(n : ℤ))) β / (n : K)) := by ring
    rw [hc, map_mul, map_pow]
    ring
  · simp [hn]

theorem tensorRootCreation_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (p : ℕ) :
    tensorRootCreation w ((coxeter^[p]) β) j =
      rescale (MvPolynomial.C (w ^ (-(p : ℤ)))) (tensorRootCreation w β j) := by
  change FormalSeries.exponential (tensorRootCreationLog w ((coxeter^[p]) β) j) =
    rescale _ (FormalSeries.exponential (tensorRootCreationLog w β j))
  rw [tensorRootCreationLog_iterate w hw]
  exact (FormalSeries.rescale_exponential _ _ (constantCoeff_tensorRootCreationLog w β j)).symm

theorem tensorRootAnnihilation_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (p : ℕ) :
    tensorRootAnnihilation w ((coxeter^[p]) β) j =
      (laurentRescale (phaseUnit w hw p)).comp (tensorRootAnnihilation w β j) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [tensorRootAnnihilation, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
      FormalSeries.laurentRescale_C]
  · intro s
    simp only [tensorRootAnnihilation, MvPolynomial.eval₂Hom_X', RingHom.comp_apply,
      map_add, FormalSeries.laurentRescale_C, FormalSeries.laurentRescale_single,
      phaseUnit_zpow]
    have hp : w ^ (-(p : ℤ) * -(s.2.val : ℤ)) = (w ^ (s.2.val : ℤ)) ^ p := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    have ht : (w ^ (s.2.val : ℤ)) ^ 4 - (w ^ (s.2.val : ℤ)) ^ 2 + 1 = 0 := by
      simpa only [zpow_natCast] using mode_cyclotomic w hw s.2
    rw [RootData.rootWeight_iterate _ ht, hp]
    by_cases hs : s.1 = j
    · simp only [if_pos hs, ← map_mul]
      congr 2
      ring
    · simp [hs]

theorem tensorRootAnnihilation_iterate_apply (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (p : ℕ) (f : Space K) :
    tensorRootAnnihilation w ((coxeter^[p]) β) j f =
      laurentRescale (phaseUnit w hw p) (tensorRootAnnihilation w β j f) := by
  rw [tensorRootAnnihilation_iterate w hw]
  rfl

theorem tensorRootSummand_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (p : ℕ) (f : Space K) :
    tensorRootSummand w ((coxeter^[p]) β) j f =
      laurentRescale (phaseUnit w hw p) (tensorRootSummand w β j f) := by
  change (tensorRootCreation w ((coxeter^[p]) β) j : LaurentSeries (Space K)) *
    tensorRootAnnihilation w ((coxeter^[p]) β) j f =
    laurentRescale _ ((tensorRootCreation w β j : LaurentSeries (Space K)) *
      tensorRootAnnihilation w β j f)
  rw [tensorRootCreation_iterate w hw, tensorRootAnnihilation_iterate_apply w hw,
    map_mul, FormalSeries.laurentRescale_powerSeries, phaseUnit_val]

theorem tensorRootField_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (p : ℕ) (f : Space K) :
    tensorRootField w ((coxeter^[p]) β) f =
      laurentRescale (phaseUnit w hw p) (tensorRootField w β f) := by
  simp only [tensorRootField, LinearMap.smul_apply, LinearMap.sum_apply,
    laurentRescale_smul, map_sum, tensorRootSummand_iterate w hw]

theorem tensorRootMode_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (p : ℕ) (i : ℤ) (f : Space K) :
    tensorRootMode w ((coxeter^[p]) β) i f =
      w ^ ((p : ℤ) * i) • tensorRootMode w β i f := by
  change (tensorRootField w ((coxeter^[p]) β) f).coeff (-i) =
    w ^ ((p : ℤ) * i) • (tensorRootField w β f).coeff (-i)
  rw [tensorRootField_iterate w hw, FormalSeries.coeff_laurentRescale, phaseUnit_zpow]
  simp only [neg_mul_neg, Algebra.smul_def, MvPolynomial.algebraMap_eq]

@[simp] theorem tensorRootCreation_zero (w : K) (j : Fin 3) :
    tensorRootCreation w 0 j = 1 := by
  have hz : tensorRootCreationLog w 0 j = 0 := by
    ext n
    simp [tensorRootCreationLog]
  rw [tensorRootCreation, hz, FormalSeries.exponential_zero]

theorem tensorRootAnnihilation_zero (w : K) (j : Fin 3) :
    tensorRootAnnihilation w 0 j = HahnSeries.C := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [tensorRootAnnihilation]
  · intro s
    simp [tensorRootAnnihilation]

theorem tensorRootSummand_zero (w : K) (j : Fin 3) (f : Space K) :
    tensorRootSummand w 0 j f = HahnSeries.C f := by
  change (tensorRootCreation w 0 j : LaurentSeries (Space K)) * tensorRootAnnihilation w 0 j f = _
  rw [tensorRootCreation_zero, tensorRootAnnihilation_zero, map_one, one_mul]

end KanadeRussell.Tsuchioka.Fock
