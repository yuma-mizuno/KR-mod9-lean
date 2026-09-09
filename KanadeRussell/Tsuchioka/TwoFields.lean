import KanadeRussell.Tsuchioka.JointAnnihilation
import KanadeRussell.Tsuchioka.ScalarFactors

/-!
Exact two-field composition in iterated Laurent series. The outer variable
belongs to the right-hand operator; the inner variable belongs to the left.
The reverse expansion and bilateral coefficient extraction remain separate.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

variable {A B : Type*} [CommRing A] [CommRing B]

theorem mapLaurent_powerSeries (f : A →+* B) (g : PowerSeries A) :
    mapLaurent f (g : LaurentSeries A) = (PowerSeries.map f g : PowerSeries B) := by
  apply HahnSeries.ext
  funext n
  simp only [coeff_mapLaurent, PowerSeries.coeff_coe, PowerSeries.coeff_map]
  split_ifs <;> simp

end KanadeRussell.Tsuchioka.FormalSeries

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open RootData (simpleRoot)
open FormalSeries (mapLaurent)

variable {K : Type*} [Field K] [CharZero K]

/-- Actual successive action of two tensor summands, with separate variables. -/
noncomputable def twoSummands (w : K) (s t : Fin 3) (f : Space K) :
    LaurentSeries (LaurentSeries (Space K)) :=
  (summand w t f).map (summand w s).toAddMonoidHom

theorem summand_coefficientMap (w : K) (s : Fin 3) (g : LaurentSeries (Space K)) :
    g.map (summand w s).toAddMonoidHom =
      HahnSeries.C (creation (K := K) s : LaurentSeries (Space K)) *
        mapLaurent (annihilation w s) g := by
  apply HahnSeries.ext
  funext n
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rfl

/-- Extracting the inner and outer coefficients gives the genuine operator composition. -/
theorem twoSummands_coeff (w : K) (s t : Fin 3) (f : Space K) (a b : ℤ) :
    ((twoSummands w s t f).coeff (-b)).coeff (-a) =
      (summand w s ((summand w t f).coeff (-b))).coeff (-a) := rfl

/-- The common normal-ordered expression before either variable is specialized. -/
noncomputable def normalProduct (w : K) (s t : Fin 3) (f : Space K) :
    LaurentSeries (LaurentSeries (Space K)) :=
  HahnSeries.C (creation (K := K) s : LaurentSeries (Space K)) *
    ((PowerSeries.map (HahnSeries.C : Space K →+* LaurentSeries (Space K))
      (creation (K := K) t) : PowerSeries (LaurentSeries (Space K))) :
        LaurentSeries (LaurentSeries (Space K))) *
    jointLaurentEmbedding (jointAnnihilationPolynomial w (simpleRoot 0) (simpleRoot 0) s t f)

theorem jointAnnihilation_first (w : K) (s t : Fin 3) (f : Space K) :
    jointLaurentEmbedding (jointAnnihilationPolynomial w (simpleRoot 0) (simpleRoot 0) s t f) =
      mapLaurent (annihilation w s) (annihilation w t f) := by
  have h := RingHom.congr_fun
    (jointLaurentEmbedding_annihilation w (simpleRoot 0) (simpleRoot 0) s t) f
  simpa only [RingHom.comp_apply, rootAnnihilation_first] using h

/-- Wick factorization of the actual sequential operators on every input polynomial. -/
theorem twoSummands_normalOrdered (w : K) (s t : Fin 3) (f : Space K) :
    twoSummands w s t f =
      normalProduct w s t f *
        (FormalSeries.exponential (wickLog w s t) :
          LaurentSeries (LaurentSeries (Space K))) := by
  rw [twoSummands, summand_coefficientMap]
  change HahnSeries.C (creation (K := K) s : LaurentSeries (Space K)) *
    mapLaurent (annihilation w s)
      ((creation (K := K) t : LaurentSeries (Space K)) * annihilation w t f) = _
  rw [map_mul, FormalSeries.mapLaurent_powerSeries, annihilation_creation,
    PowerSeries.coe_mul, normalProduct, jointAnnihilation_first]
  ring

/-- Equal tensor positions produce the source's complete G1 squared factor. -/
theorem twoSummands_same_source (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (s : Fin 3) (f : Space K) :
    twoSummands w s s f = normalProduct w s s f *
      ((sourceG1 w ^ 2 : PowerSeries (LaurentSeries (Space K))) :
        LaurentSeries (LaurentSeries (Space K))) := by
  rw [twoSummands_normalOrdered, wickLog_same,
    FormalSeries.exponential_add (constantCoeff_rootFactorLog w)
      (constantCoeff_rootFactorLog w)]
  change normalProduct w s s f *
    ((rootFactor w * rootFactor w : PowerSeries (LaurentSeries (Space K))) :
      LaurentSeries (LaurentSeries (Space K))) = _
  rw [rootFactor_eq_sourceG1 w hw, pow_two]

/-- Distinct tensor positions produce the inverse G1 factor as a product identity. -/
theorem twoSummands_distinct_source (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (s t : Fin 3) (hst : s ≠ t) (f : Space K) :
    twoSummands w s t f * (sourceG1 w : LaurentSeries (LaurentSeries (Space K))) =
      normalProduct w s t f := by
  rw [twoSummands_normalOrdered, wickLog_distinct w s t hst, mul_assoc,
    ← rootFactor_eq_sourceG1 w hw, rootFactor, ← PowerSeries.coe_mul,
    mul_comm (FormalSeries.exponential (-rootFactorLog w)),
    FormalSeries.exponential_mul_neg (constantCoeff_rootFactorLog w),
    PowerSeries.coe_one, mul_one]

/-- Successive action of the normalized complete first-root fields. -/
noncomputable def twoFields (w : K) (f : Space K) :
    LaurentSeries (LaurentSeries (Space K)) :=
  (field w f).map (field w).toAddMonoidHom

theorem twoFields_coeff (w : K) (f : Space K) (a b : ℤ) :
    ((twoFields w f).coeff (-b)).coeff (-a) = mode w a (mode w b f) := rfl

theorem twoFields_eq_sum (w : K) (f : Space K) :
    twoFields w f = (1 / 144 : K) • ∑ s : Fin 3, ∑ t : Fin 3, twoSummands w s t f := by
  apply HahnSeries.ext
  funext b
  apply HahnSeries.ext
  funext a
  simp only [twoFields, twoSummands, HahnSeries.map_coeff,
    field, LinearMap.smul_apply, LinearMap.sum_apply, HahnSeries.coeff_smul,
    HahnSeries.coeff_sum]
  simp [← Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  congr 1
  norm_num [← mul_inv]

end KanadeRussell.Tsuchioka.Fock
