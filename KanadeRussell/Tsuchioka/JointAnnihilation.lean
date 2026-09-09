import KanadeRussell.Tsuchioka.PoleFusion

/-!
The two annihilation shifts form one polynomial in two inverse field variables.
Its Laurent embedding is the composition of the original annihilation maps,
and its pole evaluation is the finite substitution used in PoleFusion.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Coefficientwise change of ring for Laurent series. -/
noncomputable def mapLaurent (f : A →+* B) : LaurentSeries A →+* LaurentSeries B where
  toFun x := x.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom

@[simp] theorem coeff_mapLaurent (f : A →+* B) (x : LaurentSeries A) (n : ℤ) :
    (mapLaurent f x).coeff n = f (x.coeff n) := rfl

@[simp] theorem mapLaurent_single (f : A →+* B) (n : ℤ) (a : A) :
    mapLaurent f (HahnSeries.single n a) = HahnSeries.single n (f a) := by
  apply HahnSeries.ext
  funext k
  simp only [coeff_mapLaurent, HahnSeries.coeff_single]
  split_ifs <;> simp

@[simp] theorem mapLaurent_C (f : A →+* B) (a : A) :
    mapLaurent f (HahnSeries.C a) = HahnSeries.C (f a) :=
  mapLaurent_single f 0 a

end KanadeRussell.Tsuchioka.FormalSeries

namespace KanadeRussell.Tsuchioka.Fock

open RootData (Lattice rootWeight)
open FormalSeries (mapLaurent)

variable {K : Type*} [Field K] [CharZero K]

/-- The annihilation part before either inverse field variable is evaluated. -/
noncomputable def jointAnnihilationPolynomial (w : K) (β γ : Lattice) (j k : Fin 3) :
    Space K →+* MvPolynomial (Fin 2) (Space K) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) fun s =>
    MvPolynomial.C (MvPolynomial.X s) +
      MvPolynomial.C (MvPolynomial.C (tensorExponent s.1 j * contraction w s.2.val / 3 *
        rootWeight (w ^ (s.2.val : ℤ)) β)) * MvPolynomial.X 0 ^ s.2.val +
      MvPolynomial.C (MvPolynomial.C (tensorExponent s.1 k * contraction w s.2.val / 3 *
        rootWeight (w ^ (s.2.val : ℤ)) γ)) * MvPolynomial.X 1 ^ s.2.val

/-- Evaluate the two inverse variables at w^p*t^(-1), t^(-1). -/
noncomputable def poleEvaluation (w : K) (p : ℤ) :
    MvPolynomial (Fin 2) (Space K) →+* LaurentSeries (Space K) :=
  MvPolynomial.eval₂Hom HahnSeries.C fun v =>
    if v = 0 then HahnSeries.single (-1) (MvPolynomial.C (w ^ p))
    else HahnSeries.single (-1) 1

theorem inverseVariable_pow {A : Type*} [CommRing A] (a : A) (n : ℕ) :
    (HahnSeries.single (-1 : ℤ) a : LaurentSeries A) ^ n =
      HahnSeries.single (-(n : ℤ)) (a ^ n) := by
  rw [HahnSeries.single_pow]
  simp

theorem scalar_inverseVariable_mul (a c : K) (n : ℕ) :
    HahnSeries.C (MvPolynomial.C a) *
      (HahnSeries.single (-1) (MvPolynomial.C c) : LaurentSeries (Space K)) ^ n =
      HahnSeries.single (-(n : ℤ)) (MvPolynomial.C (a * c ^ n)) := by
  rw [inverseVariable_pow, HahnSeries.C_apply, HahnSeries.single_mul_single,
    zero_add, ← map_pow, ← map_mul]

/-- Pole specialization of the universal polynomial gives the actual two-shift substitution. -/
theorem poleEvaluation_jointAnnihilation (w : K) (β γ : Lattice) (j k : Fin 3) (p : ℤ) :
    (poleEvaluation w p).comp (jointAnnihilationPolynomial w β γ j k) =
      poleAnnihilation w β γ j k p := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, jointAnnihilationPolynomial, poleAnnihilation,
      poleEvaluation, MvPolynomial.eval₂Hom_C]
  · intro s
    simp only [RingHom.comp_apply, jointAnnihilationPolynomial, MvPolynomial.eval₂Hom_X',
      map_add, map_mul, map_pow, poleEvaluation, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', ite_true,
      if_neg (by decide : (1 : Fin 2) ≠ 0)]
    simp only [ite_true, ← map_mul]
    rw [scalar_inverseVariable_mul]
    have h1 : (1 : Space K) = MvPolynomial.C (1 : K) := (map_one MvPolynomial.C).symm
    rw [h1, scalar_inverseVariable_mul]
    simp only [one_pow, mul_one, poleAnnihilation, MvPolynomial.eval₂Hom_X']
    rw [add_assoc, ← HahnSeries.single_add, ← map_add]
    congr 2
    rw [← zpow_natCast, ← zpow_mul]
    ring

/-- Embed the two inverse variables in iterated Laurent series.
The first variable is inner and the second is outer. -/
noncomputable def jointLaurentEmbedding :
    MvPolynomial (Fin 2) (Space K) →+* LaurentSeries (LaurentSeries (Space K)) :=
  MvPolynomial.eval₂Hom (HahnSeries.C.comp HahnSeries.C) fun v =>
    if v = 0 then HahnSeries.C (HahnSeries.single (-1) 1)
    else HahnSeries.single (-1) (HahnSeries.C 1)

theorem constant_inverseVariable_mul {A : Type*} [CommRing A] (a : A) (n : ℕ) :
    HahnSeries.C a * (HahnSeries.single (-1) 1 : LaurentSeries A) ^ n =
      HahnSeries.single (-(n : ℤ)) a := by
  rw [inverseVariable_pow, one_pow, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]

theorem doubleC_inverseVariable_mul {A : Type*} [CommRing A] (a : A) (n : ℕ) :
    HahnSeries.C (HahnSeries.C a) *
      (HahnSeries.C (HahnSeries.single (-1) 1) : LaurentSeries (LaurentSeries A)) ^ n =
      HahnSeries.C (HahnSeries.single (-(n : ℤ)) a) := by
  rw [← map_pow (HahnSeries.C : LaurentSeries A →+* LaurentSeries (LaurentSeries A)),
    ← map_mul, constant_inverseVariable_mul]

/-- The finite polynomial represents the exact composition of annihilation substitutions. -/
theorem jointLaurentEmbedding_annihilation (w : K) (β γ : Lattice) (j k : Fin 3) :
    jointLaurentEmbedding.comp (jointAnnihilationPolynomial w β γ j k) =
      (mapLaurent (rootAnnihilation w β j)).comp (rootAnnihilation w γ k) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, jointAnnihilationPolynomial, rootAnnihilation,
      jointLaurentEmbedding, MvPolynomial.eval₂Hom_C, FormalSeries.mapLaurent_C]
  · intro s
    simp only [RingHom.comp_apply, jointAnnihilationPolynomial, MvPolynomial.eval₂Hom_X',
      jointLaurentEmbedding, map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', ite_true,
      if_neg (by decide : (1 : Fin 2) ≠ 0), rootAnnihilation,
      FormalSeries.mapLaurent_C, FormalSeries.mapLaurent_single]
    simp only [ite_true, ← map_mul, map_one]
    rw [doubleC_inverseVariable_mul, constant_inverseVariable_mul]


end KanadeRussell.Tsuchioka.Fock
