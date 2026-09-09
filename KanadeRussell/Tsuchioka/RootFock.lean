import KanadeRussell.Tsuchioka.Fock
import KanadeRussell.Tsuchioka.RootFunctional

/-!
Fock fields for lattice elements using the normalized Coxeter eigenfunctional.
The first-root field is proved equal to the existing construction.
Affine-standard-module identification is not assumed here.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open PowerSeries
open RootData (Lattice rootWeight simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

/-- The creation coordinate uses the negative-mode Coxeter eigenfunctional. -/
noncomputable def rootCreationLog (w : K) (β : Lattice) (j : Fin 3) :
    PowerSeries (Space K) :=
  PowerSeries.mk fun n =>
    MvPolynomial.C (rootWeight (w ^ (-(n : ℤ))) β) * coeff n (creationLog j)

@[simp] theorem constantCoeff_rootCreationLog (w : K) (β : Lattice) (j : Fin 3) :
    constantCoeff (rootCreationLog w β j) = 0 := by
  simp [rootCreationLog]

theorem rootCreationLog_add (w : K) (β γ : Lattice) (j : Fin 3) :
    rootCreationLog w (β + γ) j = rootCreationLog w β j + rootCreationLog w γ j := by
  apply PowerSeries.ext
  intro n
  simp only [rootCreationLog, coeff_mk, map_add, RootData.rootWeight_add, add_mul]

theorem rootCreationLog_neg (w : K) (β : Lattice) (j : Fin 3) :
    rootCreationLog w (-β) j = -rootCreationLog w β j := by
  apply PowerSeries.ext
  intro n
  simp only [rootCreationLog, coeff_mk, map_neg, RootData.rootWeight_neg, neg_mul]

theorem rootCreationLog_first (w : K) (j : Fin 3) :
    rootCreationLog w (simpleRoot 0) j = creationLog (K := K) j := by
  apply PowerSeries.ext
  intro n
  simp [rootCreationLog]

noncomputable def rootCreation (w : K) (β : Lattice) (j : Fin 3) :
    PowerSeries (Space K) :=
  FormalSeries.exponential (rootCreationLog w β j)

@[simp] theorem constantCoeff_rootCreation (w : K) (β : Lattice) (j : Fin 3) :
    constantCoeff (rootCreation w β j) = 1 :=
  FormalSeries.constantCoeff_exponential (constantCoeff_rootCreationLog w β j)

theorem rootCreation_first (w : K) (j : Fin 3) :
    rootCreation w (simpleRoot 0) j = creation (K := K) j := by
  rw [rootCreation, rootCreationLog_first, creation]

/-- At a common variable, the creation parts fuse by root addition. -/
theorem rootCreation_add (w : K) (β γ : Lattice) (j : Fin 3) :
    rootCreation w (β + γ) j = rootCreation w β j * rootCreation w γ j := by
  rw [rootCreation, rootCreationLog_add,
    FormalSeries.exponential_add (constantCoeff_rootCreationLog w β j)
      (constantCoeff_rootCreationLog w γ j)]
  rfl

/-- The annihilation coordinate uses the positive-mode eigenfunctional. -/
noncomputable def rootAnnihilation (w : K) (β : Lattice) (j : Fin 3) :
    Space K →+* LaurentSeries (Space K) :=
  MvPolynomial.eval₂Hom (HahnSeries.C.comp MvPolynomial.C) fun s =>
    HahnSeries.C (MvPolynomial.X s) +
      HahnSeries.single (-(s.2.val : ℤ))
        (MvPolynomial.C (tensorExponent s.1 j * contraction w s.2.val / 3 *
          rootWeight (w ^ (s.2.val : ℤ)) β))

theorem rootAnnihilation_first (w : K) (j : Fin 3) :
    rootAnnihilation w (simpleRoot 0) j = annihilation w j := by
  simp only [rootAnnihilation, annihilation, RootData.rootWeight_first, mul_one]

noncomputable def rootSummand (w : K) (β : Lattice) (j : Fin 3) :
    Space K →ₗ[K] LaurentSeries (Space K) where
  toFun p := (rootCreation w β j : LaurentSeries (Space K)) * rootAnnihilation w β j p
  map_add' p q := by simp [map_add, mul_add]
  map_smul' c p := by
    change (rootCreation w β j : LaurentSeries (Space K)) * rootAnnihilation w β j (c • p) =
      c • ((rootCreation w β j : LaurentSeries (Space K)) * rootAnnihilation w β j p)
    rw [Algebra.smul_def c p, MvPolynomial.algebraMap_eq, map_mul]
    have hc : rootAnnihilation w β j (MvPolynomial.C c) =
        HahnSeries.C (MvPolynomial.C c) := by
      simp [rootAnnihilation]
    rw [hc, mul_left_comm]
    apply HahnSeries.ext
    funext n
    simp [HahnSeries.coeff_smul, Algebra.smul_def]

theorem rootSummand_first (w : K) (j : Fin 3) :
    rootSummand w (simpleRoot 0) j = summand w j := by
  apply LinearMap.ext
  intro p
  change (rootCreation w (simpleRoot 0) j : LaurentSeries (Space K)) *
    rootAnnihilation w (simpleRoot 0) j p = _
  rw [rootCreation_first, rootAnnihilation_first]
  rfl

/-- The root field has the same three-tensor normalization as the source. -/
noncomputable def rootField (w : K) (β : Lattice) :
    Space K →ₗ[K] LaurentSeries (Space K) :=
  (1 / 12 : K) • ∑ j : Fin 3, rootSummand w β j

theorem rootField_first (w : K) :
    rootField w (simpleRoot 0) = field w := by
  simp [rootField, field, rootSummand_first]

noncomputable def rootMode (w : K) (β : Lattice) (i : ℤ) : Module.End K (Space K) where
  toFun p := (rootField w β p).coeff (-i)
  map_add' p q := by simp [HahnSeries.coeff_add]
  map_smul' c p := by simp [HahnSeries.coeff_smul]

theorem rootMode_first (w : K) (i : ℤ) :
    rootMode w (simpleRoot 0) i = mode w i := by
  apply LinearMap.ext
  intro p
  change (rootField w (simpleRoot 0) p).coeff (-i) = _
  rw [rootField_first]
  rfl

/-- The second-root operators are defined on the same polynomial space. -/
noncomputable def secondRootMode (w : K) (i : ℤ) : Module.End K (Space K) :=
  rootMode w (simpleRoot 1) i

theorem rootField_vacuum (w : K) (β : Lattice) :
    rootField w β 1 =
      ((1 / 12 : K) • ∑ j : Fin 3, rootCreation w β j : PowerSeries (Space K)) := by
  simp [rootField, rootSummand, PowerSeries.coe_smul, ← map_sum]

theorem rootMode_vacuum_pos (w : K) (β : Lattice) (i : ℤ) (hi : 0 < i) :
    rootMode w β i 1 = 0 := by
  change (rootField w β 1).coeff (-i) = 0
  rw [rootField_vacuum, PowerSeries.coeff_coe, if_pos (by omega)]

end KanadeRussell.Tsuchioka.Fock
