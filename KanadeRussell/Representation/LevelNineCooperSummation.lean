import KanadeRussell.Representation.LevelNineCooperReindexing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Representation.LevelNineCooperReindexing
open LevelNineNumeratorMasks
open Product.CubicScalarExtension (L p eval)

/-- The twelve signed monomials are precisely the finite G2 alternant factor. -/
theorem cooper_polynomial {R : Type*} [CommRing R] (x y : R) :
    (∑ h : Fin 12, (cooperSign h : R)*x^(cooperPowers h).1*y^(cooperPowers h).2) =
      (1-x)*(1-y)*(1-x*y)*(1-x^2*y)*(1-x^3*y)*(1-x^3*y^2) := by
  norm_num [Fin.sum_univ_succ, cooperSign, cooperPowers]
  ring

/-- Every signed Cooper exponent lies in the original nonnegative principal grading. -/
theorem cooperExponent_nonneg (k : Fin 3) (h : Fin 12) (z : ℤ × ℤ) :
    0 ≤ cooperExponent k h z := by
  rw [← cooper_exponent]
  exact cosetExponent_nonneg k (cooperCosetEquiv k (h,z))

abbrev CooperDegree (k : Fin 3) (n : ℕ) :=
  {z : Fin 12 × (ℤ × ℤ) // cooperExponent k z.1 z.2 = n}

private def flattenDegree (k : Fin 3) (n : ℕ) :
    {c : ActiveCoset k // cosetExponent k c.val = n} ≃ CosetDegree k n where
  toFun c := ⟨c.val.val, c.val.property, c.property⟩
  invFun c := ⟨⟨c.val,c.property.1⟩,c.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def cooperDegreeEquiv (k : Fin 3) (n : ℕ) : CooperDegree k n ≃ CosetDegree k n :=
  (Equiv.subtypeEquiv (cooperCosetEquiv k) (by
    intro z
    rw [cooper_exponent])).trans (flattenDegree k n)

instance cooperDegreeFintype (k : Fin 3) (n : ℕ) : Fintype (CooperDegree k n) :=
  Fintype.ofEquiv (CosetDegree k n) (cooperDegreeEquiv k n).symm

theorem coeff_principalNumerator_cooper (k : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (principalNumerator k) =
      ∑ z : CooperDegree k n, cooperSign z.val.1 := by
  rw [coeff_principalNumerator_cosets]
  symm
  apply Fintype.sum_equiv (cooperDegreeEquiv k n)
  intro z
  exact (cooper_sign k z.val.1).symm

private theorem eval_monomial (k : Fin 3) (c : ActiveCoset k) :
    eval (cosetMonomial k c) = (mask k c.val.r c.val.s : L)*
      (((p^2)^cosetExponent k c.val : Lˣ) : L) := by
  have hnonneg := cosetExponent_nonneg k c
  simp only [cosetMonomial, PowerSeries.monomial_eq_C_mul_X_pow,
    Product.CubicScalarExtension.eval, map_mul, map_pow, PowerSeries.intEval_C,
    PowerSeries.intEval_X (Product.CubicScalarExtension.p_nilpotent.pow (by decide : 2 ≠ 0))]
  congr 1
  have he : ((cosetExponent k c.val).toNat : ℤ) = cosetExponent k c.val := Int.toNat_of_nonneg hnonneg
  rw [← he, zpow_natCast, Units.val_pow_eq_pow_val]
  simp only [Int.toNat_natCast, Units.val_pow_eq_pow_val]

/-- The actual numerator is the convergent signed Cooper lattice sum, with
`Q=q^9` and the substitution `n=m+l` built into `cooperExponent`. -/
theorem hasSum_cooper_principalNumerator (k : Fin 3) :
    HasSum (fun z : Fin 12 × (ℤ × ℤ) => (cooperSign z.1 : L)*
      (((p^2)^cooperExponent k z.1 z.2 : Lˣ) : L)) (eval (principalNumerator k)) := by
  have hs := (hasSum_cosetMonomial k).map eval Product.CubicScalarExtension.eval_continuous
  have ht := (cooperCosetEquiv k).hasSum_iff.mpr hs
  convert ht using 1
  funext z
  rcases z with ⟨h,z⟩
  simp only [Function.comp_apply, eval_monomial, cooper_exponent]
  change (cooperSign h : L)*_ = (mask k (residue k h).1 (residue k h).2 : L)*_
  rw [cooper_sign]

end KanadeRussell.Representation.LevelNineCooperReindexing
