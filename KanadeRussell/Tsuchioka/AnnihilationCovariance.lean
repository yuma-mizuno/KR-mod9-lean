import KanadeRussell.Tsuchioka.LaurentRescaling

/-! Coxeter covariance of the full root fields, including annihilation and modes. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open PowerSeries
open RootData (Lattice simpleRoot coxeter rootWeight)
open FormalSeries (laurentRescale)

variable {K : Type*} [Field K] [CharZero K]

/-- The unit implementing t -> w^(-p)*t in the polynomial coefficient ring. -/
noncomputable def phaseUnit (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (p : ℤ) :
    (Space K)ˣ :=
  Units.map MvPolynomial.C.toMonoidHom
    ((Units.mk0 w (Coefficients.root_ne_zero w hw)) ^ (-p))

@[simp] theorem phaseUnit_val (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (p : ℤ) :
    (phaseUnit w hw p : Space K) = MvPolynomial.C (w ^ (-p)) := by
  change MvPolynomial.C (((Units.mk0 w (Coefficients.root_ne_zero w hw)) ^ (-p) : Kˣ) : K) = _
  rw [Units.val_zpow_eq_zpow_val]
  rfl

theorem phaseUnit_zpow (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (p n : ℤ) :
    ((phaseUnit w hw p ^ n : (Space K)ˣ) : Space K) =
      MvPolynomial.C (w ^ ((-p) * n)) := by
  simp only [phaseUnit, ← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val,
    Units.val_mk0, ← zpow_mul]
  rfl

theorem rootAnnihilation_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (p : ℕ) :
    rootAnnihilation w ((coxeter^[p]) β) j =
      (laurentRescale (phaseUnit w hw p)).comp (rootAnnihilation w β j) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [rootAnnihilation, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
      FormalSeries.laurentRescale_C]
  · intro s
    simp only [rootAnnihilation, MvPolynomial.eval₂Hom_X', RingHom.comp_apply,
      map_add, FormalSeries.laurentRescale_C, FormalSeries.laurentRescale_single,
      phaseUnit_zpow]
    have ht := mode_cyclotomic w hw s.2
    have hp : w ^ (-(p : ℤ) * -(s.2.val : ℤ)) =
        (w ^ (s.2.val : ℤ)) ^ p := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    have ht' : (w ^ (s.2.val : ℤ)) ^ 4 - (w ^ (s.2.val : ℤ)) ^ 2 + 1 = 0 := by
      simpa only [zpow_natCast] using ht
    rw [RootData.rootWeight_iterate _ ht', hp, ← map_mul]
    congr 2
    ring

theorem rootAnnihilation_iterate_apply (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (p : ℕ) (f : Space K) :
    rootAnnihilation w ((coxeter^[p]) β) j f =
      laurentRescale (phaseUnit w hw p) (rootAnnihilation w β j f) := by
  rw [rootAnnihilation_iterate w hw]
  rfl

theorem rootSummand_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (p : ℕ) (f : Space K) :
    rootSummand w ((coxeter^[p]) β) j f =
      laurentRescale (phaseUnit w hw p) (rootSummand w β j f) := by
  change (rootCreation w ((coxeter^[p]) β) j : LaurentSeries (Space K)) *
    rootAnnihilation w ((coxeter^[p]) β) j f =
    laurentRescale _ ((rootCreation w β j : LaurentSeries (Space K)) *
      rootAnnihilation w β j f)
  rw [rootCreation_iterate w hw, rootAnnihilation_iterate_apply w hw,
    map_mul, FormalSeries.laurentRescale_powerSeries, phaseUnit_val]

theorem laurentRescale_smul (u : (Space K)ˣ) (c : K) (f : LaurentSeries (Space K)) :
    laurentRescale u (c • f) = c • laurentRescale u f := by
  apply HahnSeries.ext
  funext n
  simp only [FormalSeries.coeff_laurentRescale, HahnSeries.coeff_smul,
    Algebra.smul_def]
  ring

theorem rootField_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (p : ℕ) (f : Space K) :
    rootField w ((coxeter^[p]) β) f =
      laurentRescale (phaseUnit w hw p) (rootField w β f) := by
  simp only [rootField, LinearMap.smul_apply, LinearMap.sum_apply,
    laurentRescale_smul, map_sum, rootSummand_iterate w hw]

/-- Full integer-mode covariance; no truncation of the fields is used. -/
theorem rootMode_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (p : ℕ) (i : ℤ) (f : Space K) :
    rootMode w ((coxeter^[p]) β) i f =
      w ^ ((p : ℤ) * i) • rootMode w β i f := by
  change (rootField w ((coxeter^[p]) β) f).coeff (-i) =
    w ^ ((p : ℤ) * i) • (rootField w β f).coeff (-i)
  rw [rootField_iterate w hw, FormalSeries.coeff_laurentRescale, phaseUnit_zpow]
  simp only [neg_mul_neg, Algebra.smul_def, MvPolynomial.algebraMap_eq]

end KanadeRussell.Tsuchioka.Fock
