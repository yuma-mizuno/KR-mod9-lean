import KanadeRussell.Tsuchioka.FormalExponential
import KanadeRussell.Tsuchioka.Phases
import KanadeRussell.Tsuchioka.RootData

/-!
The normal-ordered three-tensor Fock field for the first root.
The formal variable is t = zeta^(-1), so mode i is the coefficient at -i.
This file constructs polynomial operators; identifying the resulting representation
and its vacuum character remains a separate theorem.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open PowerSeries

/-- The four positive principal Heisenberg residue classes for D4^(3). -/
def IsMode (n : ℕ) : Prop :=
  n % 12 = 1 ∨ n % 12 = 5 ∨ n % 12 = 7 ∨ n % 12 = 11

instance (n : ℕ) : Decidable (IsMode n) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

abbrev Mode := {n : ℕ // IsMode n}

theorem mode_pos (n : Mode) : 0 < n.val := by
  have := n.property
  dsimp [IsMode] at this
  omega

/-- Three independent basic Fock factors. -/
abbrev Space (K : Type*) [CommSemiring K] :=
  MvPolynomial (Fin 3 × Mode) K

variable {K : Type*} [Field K]

/-- Exponents of the three factors in m Z^(j): -2 on j, +1 elsewhere. -/
def tensorExponent (i j : Fin 3) : K := if i.val = j.val then -2 else 1

theorem sum_tensorExponent (i : Fin 3) :
    ∑ j : Fin 3, tensorExponent (K := K) i j = 0 := by
  have he (j : Fin 3) : tensorExponent (K := K) i j =
      1 - 3 * (if j = i then 1 else 0) := by
    by_cases h : i = j
    · subst j
      simp [tensorExponent]
      ring
    · have hv : i.val ≠ j.val := fun he => h (Fin.ext he)
      simp [tensorExponent, hv, Ne.symm h]
  simp only [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

/-- The root pairings <nu^p beta_1, beta_1> for 0 <= p < 12. -/
def orbitPairing (p : Fin 12) : ℤ :=
  RootData.pairing ((RootData.coxeter^[p.val]) (RootData.simpleRoot 0))
    (RootData.simpleRoot 0)

theorem orbitPairing_eq (p : Fin 12) :
    orbitPairing p = ![2, 1, 1, 0, -1, -1, -2, -1, -1, 0, 1, 1] p :=
  RootData.first_root_orbit_pairing p

/-- The Fourier coefficient of the first-root pairing.
The variable x_(i,n) represents beta_1(-n) in factor i. -/
noncomputable def contraction (w : K) (n : ℕ) : K :=
  (1 / 12 : K) * ∑ p : Fin 12, (orbitPairing p : K) * w ^ (-((n : ℤ) * p.val))

/-- Logarithm of the creation part, with t = zeta^(-1). -/
noncomputable def creationLog (j : Fin 3) : PowerSeries (Space K) :=
  PowerSeries.mk fun n =>
    if h : IsMode n then
      ∑ i : Fin 3,
        MvPolynomial.C (-4 * tensorExponent i j / (n : K)) *
          MvPolynomial.X (i, (⟨n, h⟩ : Mode))
    else 0

@[simp] theorem constantCoeff_creationLog (j : Fin 3) :
    constantCoeff (creationLog (K := K) j) = 0 := by
  simp [creationLog, IsMode]

variable [CharZero K]

noncomputable def creation (j : Fin 3) : PowerSeries (Space K) :=
  FormalSeries.exponential (creationLog j)

@[simp] theorem constantCoeff_creation (j : Fin 3) :
    constantCoeff (creation (K := K) j) = 1 :=
  FormalSeries.constantCoeff_exponential (constantCoeff_creationLog j)

/-- Annihilation acts by the finite polynomial substitution
x_(i,n) -> x_(i,n) + lambda_(i,j) kappa_n t^(-n)/3. -/
noncomputable def annihilation (w : K) (j : Fin 3) :
    Space K →+* LaurentSeries (Space K) :=
  MvPolynomial.eval₂Hom (HahnSeries.C.comp MvPolynomial.C) fun s =>
    HahnSeries.C (MvPolynomial.X s) +
      HahnSeries.single (-(s.2.val : ℤ))
        (MvPolynomial.C (tensorExponent s.1 j * contraction w s.2.val / 3))

/-- Each tensor summand acts on a polynomial by a Laurent series. -/
noncomputable def summand (w : K) (j : Fin 3) :
    Space K →ₗ[K] LaurentSeries (Space K) where
  toFun p := (creation (K := K) j : LaurentSeries (Space K)) * annihilation w j p
  map_add' p q := by simp [map_add, mul_add]
  map_smul' c p := by
    change (creation (K := K) j : LaurentSeries (Space K)) * annihilation w j (c • p) =
      c • ((creation (K := K) j : LaurentSeries (Space K)) * annihilation w j p)
    rw [Algebra.smul_def c p, MvPolynomial.algebraMap_eq, map_mul]
    have hc : annihilation w j (MvPolynomial.C c) = HahnSeries.C (MvPolynomial.C c) := by
      simp [annihilation]
    rw [hc]
    rw [mul_left_comm]
    apply HahnSeries.ext
    funext n
    simp [HahnSeries.coeff_smul, Algebra.smul_def]

/-- The first-root Z field with the source normalization m=12. -/
noncomputable def field (w : K) : Space K →ₗ[K] LaurentSeries (Space K) :=
  (1 / 12 : K) • ∑ j : Fin 3, summand w j

/-- The actual polynomial mode, with the source's zeta indexing. -/
noncomputable def mode (w : K) (i : ℤ) : Module.End K (Space K) where
  toFun p := (field w p).coeff (-i)
  map_add' p q := by simp [HahnSeries.coeff_add]
  map_smul' c p := by simp [HahnSeries.coeff_smul]

theorem field_vacuum (w : K) :
    field w 1 = ((1 / 12 : K) • ∑ j : Fin 3, creation j : PowerSeries (Space K)) := by
  simp [field, summand, PowerSeries.coe_smul, ← map_sum]

theorem mode_vacuum_nonpos (w : K) (n : ℕ) :
    mode w (-(n : ℤ)) 1 =
      (1 / 12 : K) • ∑ j : Fin 3, coeff n (creation (K := K) j) := by
  change (field w 1).coeff (-(-(n : ℤ))) = _
  rw [field_vacuum]
  simp [LaurentSeries.coeff_coe_powerSeries]

theorem mode_vacuum_pos (w : K) (i : ℤ) (hi : 0 < i) :
    mode w i 1 = 0 := by
  change (field w 1).coeff (-i) = 0
  rw [field_vacuum, PowerSeries.coeff_coe, if_pos (by omega)]

theorem mode_zero_vacuum (w : K) :
    mode w 0 1 = MvPolynomial.C (1 / 4 : K) := by
  have h := mode_vacuum_nonpos w 0
  norm_num [coeff_zero_eq_constantCoeff, Fin.sum_univ_succ] at h
  rw [h, Algebra.smul_def]
  change MvPolynomial.C (1 / 12 : K) * 3 = MvPolynomial.C (1 / 4 : K)
  rw [show (3 : Space K) = MvPolynomial.C (3 : K) from (map_ofNat _ 3).symm, ← map_mul]
  congr 1
  norm_num

/-- Every polynomial is killed by all sufficiently large positive modes.
The cutoff comes from the Laurent-series support proved during construction. -/
theorem mode_locally_finite (w : K) (p : Space K) :
    ∃ N : ℕ, ∀ i : ℤ, (N : ℤ) < i → mode w i p = 0 := by
  refine ⟨(-(field w p).order).toNat, ?_⟩
  intro i hi
  change (field w p).coeff (-i) = 0
  apply HahnSeries.coeff_eq_zero_of_lt_order
  omega

def firstMode : Mode := ⟨1, by decide⟩

noncomputable def degreeOneVariable (i : Fin 3) : Space K :=
  MvPolynomial.X (i, firstMode)

theorem coeff_one_creation (j : Fin 3) :
    coeff 1 (creation (K := K) j) =
      ∑ i : Fin 3, MvPolynomial.C (-4 * tensorExponent i j) * degreeOneVariable i := by
  rw [creation, FormalSeries.coeff_one_exponential (constantCoeff_creationLog j)]
  rw [creationLog, coeff_mk, dif_pos (show IsMode 1 from by decide)]
  simp only [Nat.cast_one, div_one]
  rfl

theorem mode_neg_one_vacuum (w : K) : mode w (-1) 1 = 0 := by
  have h := mode_vacuum_nonpos w 1
  norm_num only [Nat.cast_one] at h
  rw [h]
  simp only [coeff_one_creation]
  rw [Finset.sum_comm]
  have he (i : Fin 3) :
      ∑ j : Fin 3, MvPolynomial.C (-4 * tensorExponent (K := K) i j) *
        degreeOneVariable i = 0 := by
    rw [← Finset.sum_mul, ← map_sum, ← Finset.mul_sum, sum_tensorExponent]
    simp
  simp_rw [he]
  simp

theorem coeff_two_creation (j : Fin 3) :
    coeff 2 (creation (K := K) j) =
      algebraMap ℚ (Space K) (1 / 2) *
        (∑ i : Fin 3, MvPolynomial.C (-4 * tensorExponent i j) * degreeOneVariable i) ^ 2 := by
  rw [creation, FormalSeries.coeff_two_exponential (constantCoeff_creationLog j)]
  have h1 := coeff_one_creation (K := K) j
  rw [creation, FormalSeries.coeff_one_exponential (constantCoeff_creationLog j)] at h1
  rw [h1]
  simp [creationLog, IsMode]

theorem mode_neg_two_vacuum (w : K) :
    mode w (-2) 1 = 4 * (degreeOneVariable 0 ^ 2 + degreeOneVariable 1 ^ 2 +
      degreeOneVariable 2 ^ 2 - degreeOneVariable 0 * degreeOneVariable 1 -
      degreeOneVariable 0 * degreeOneVariable 2 - degreeOneVariable 1 * degreeOneVariable 2) := by
  have h := mode_vacuum_nonpos w 2
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  simp only [coeff_two_creation, Fin.sum_univ_three, tensorExponent]
  norm_num [Algebra.smul_def, map_ofNat]
  have hc : MvPolynomial.C (1 / 12 : K) * MvPolynomial.C (1 / 2 : K) * 96 =
      (4 : Space K) := by
    rw [show (96 : Space K) = MvPolynomial.C (96 : K) from (map_ofNat _ 96).symm,
      ← map_mul, ← map_mul]
    norm_num [map_ofNat]
  linear_combination
    (degreeOneVariable 0 ^ 2 + degreeOneVariable 1 ^ 2 + degreeOneVariable 2 ^ 2 -
      degreeOneVariable 0 * degreeOneVariable 1 - degreeOneVariable 0 * degreeOneVariable 2 -
      degreeOneVariable 1 * degreeOneVariable 2) * hc

theorem mode_neg_two_vacuum_ne_zero (w : K) : mode w (-2) 1 ≠ 0 := by
  rw [mode_neg_two_vacuum]
  intro hz
  have he := congrArg
    (MvPolynomial.eval fun s : Fin 3 × Mode => if s.1.val = 0 then (1 : K) else 0) hz
  norm_num [degreeOneVariable] at he

end KanadeRussell.Tsuchioka.Fock
