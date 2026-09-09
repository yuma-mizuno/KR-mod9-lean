import KanadeRussell.Tsuchioka.AnnihilationCovariance

/-!
Normal-ordered products specialized at the commutator poles.
Creation and both finite annihilation shifts are included. The relation between
these specializations and the two-variable field product is a separate step.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open PowerSeries
open RootData (Lattice simpleRoot coxeter rootWeight)
open FormalSeries (laurentRescale)

variable {K : Type*} [Field K] [CharZero K]

/-- Both annihilation shifts after t1 = w^(-p)*t2. This is a finite
polynomial substitution on every input, for arbitrary tensor positions. -/
noncomputable def poleAnnihilation (w : K) (β γ : Lattice)
    (j k : Fin 3) (p : ℤ) : Space K →+* LaurentSeries (Space K) :=
  MvPolynomial.eval₂Hom (HahnSeries.C.comp MvPolynomial.C) fun s =>
    HahnSeries.C (MvPolynomial.X s) +
      HahnSeries.single (-(s.2.val : ℤ))
        (MvPolynomial.C (contraction w s.2.val / 3 *
          (tensorExponent s.1 j * w ^ (p * s.2.val) *
             rootWeight (w ^ (s.2.val : ℤ)) β +
           tensorExponent s.1 k * rootWeight (w ^ (s.2.val : ℤ)) γ)))

theorem poleAnnihilation_same (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β γ : Lattice) (j : Fin 3) (p : ℕ) :
    poleAnnihilation w β γ j j p =
      rootAnnihilation w ((coxeter^[p]) β + γ) j := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [poleAnnihilation, rootAnnihilation, MvPolynomial.eval₂Hom_C]
  · intro s
    simp only [poleAnnihilation, rootAnnihilation, MvPolynomial.eval₂Hom_X']
    have ht : (w ^ (s.2.val : ℤ)) ^ 4 - (w ^ (s.2.val : ℤ)) ^ 2 + 1 = 0 := by
      simpa only [zpow_natCast] using mode_cyclotomic w hw s.2
    have hp : (w ^ (s.2.val : ℤ)) ^ p = w ^ ((p : ℤ) * s.2.val) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    rw [RootData.rootWeight_add, RootData.rootWeight_iterate _ ht, hp]
    congr 2
    ring

/-- The actual normal-ordered expression at a fixed ratio, with both
creation factors and the sum of the two annihilation shifts. -/
noncomputable def poleNormalProduct (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β γ : Lattice) (j k : Fin 3) (p : ℤ) (f : Space K) :
    LaurentSeries (Space K) :=
  laurentRescale (phaseUnit w hw p) (rootCreation w β j : LaurentSeries (Space K)) *
    (rootCreation w γ k : LaurentSeries (Space K)) * poleAnnihilation w β γ j k p f

/-- At a common tensor position, the full normal product fuses by root addition. -/
theorem poleNormalProduct_same (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β γ : Lattice) (j : Fin 3) (p : ℕ) (f : Space K) :
    poleNormalProduct w hw β γ j j p f =
      rootSummand w ((coxeter^[p]) β + γ) j f := by
  change laurentRescale _ (rootCreation w β j : LaurentSeries (Space K)) *
    (rootCreation w γ j : LaurentSeries (Space K)) * poleAnnihilation w β γ j j p f =
    (rootCreation w ((coxeter^[p]) β + γ) j : LaurentSeries (Space K)) *
      rootAnnihilation w ((coxeter^[p]) β + γ) j f
  rw [poleAnnihilation_same w hw, rootCreation_add, rootCreation_iterate w hw,
    FormalSeries.laurentRescale_powerSeries, phaseUnit_val, map_mul]

theorem poleNormalProduct_four (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) :
    poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) j j 4 f =
      laurentRescale (phaseUnit w hw 2) (summand w j f) := by
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, poleNormalProduct_same,
    RootData.first_fusion_four, rootSummand_iterate w hw, rootSummand_first]
  norm_num

theorem poleNormalProduct_eight (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) :
    poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) j j 8 f =
      laurentRescale (phaseUnit w hw 10) (summand w j f) := by
  rw [show (8 : ℤ) = ((8 : ℕ) : ℤ) from rfl, poleNormalProduct_same,
    RootData.first_fusion_eight, rootSummand_iterate w hw, rootSummand_first]
  norm_num

theorem poleNormalProduct_five (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) :
    poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) j j 5 f =
      laurentRescale (phaseUnit w hw 9) (rootSummand w (simpleRoot 1) j f) := by
  rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, poleNormalProduct_same,
    RootData.first_fusion_five, rootSummand_iterate w hw]
  norm_num

theorem poleNormalProduct_seven (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) :
    poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) j j 7 f =
      laurentRescale (phaseUnit w hw 4) (rootSummand w (simpleRoot 1) j f) := by
  rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) from rfl, poleNormalProduct_same,
    RootData.first_fusion_seven, rootSummand_iterate w hw]
  norm_num

@[simp] theorem rootCreation_zero (w : K) (j : Fin 3) :
    rootCreation w 0 j = 1 := by
  have hz : rootCreationLog w 0 j = 0 := by
    apply PowerSeries.ext
    intro n
    simp [rootCreationLog]
  rw [rootCreation, hz, FormalSeries.exponential_zero]

theorem rootAnnihilation_zero (w : K) (j : Fin 3) :
    rootAnnihilation w 0 j = HahnSeries.C := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [rootAnnihilation]
  · intro s
    simp [rootAnnihilation]

theorem rootSummand_zero (w : K) (j : Fin 3) (f : Space K) :
    rootSummand w 0 j f = HahnSeries.C f := by
  change (rootCreation w 0 j : LaurentSeries (Space K)) * rootAnnihilation w 0 j f = _
  rw [rootCreation_zero, rootAnnihilation_zero, map_one, one_mul]

/-- The central-pole normal product is the identity on every polynomial input. -/
theorem poleNormalProduct_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (f : Space K) :
    poleNormalProduct w hw β β j j 6 f = HahnSeries.C f := by
  rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, poleNormalProduct_same,
    RootData.coxeter_six, neg_add_cancel, rootSummand_zero]

end KanadeRussell.Tsuchioka.Fock
