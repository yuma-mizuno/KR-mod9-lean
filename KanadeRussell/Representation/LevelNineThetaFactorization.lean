import KanadeRussell.Representation.LevelNineThetaSummation
import KanadeRussell.Infra.A2ThetaFactorization
import KanadeRussell.Product.CubicScalarExtension
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Representation.LevelNineNumeratorMasks
open KanadeRussell.Infra
open Product.CubicScalarExtension (L p eval)

abbrev ActiveResidue (k : Fin 3) := {r : Fin 9 × Fin 9 // mask k r.1 r.2 ≠ 0}

def residueCosetEquiv (k : Fin 3) : ActiveResidue k × (ℤ × ℤ) ≃ ActiveCoset k where
  toFun z := ⟨⟨z.1.val.1,z.1.val.2,z.2.1,z.2.2⟩,z.1.property⟩
  invFun c := (⟨(c.val.r,c.val.s),c.property⟩,(c.val.m,c.val.l))
  left_inv := by rintro ⟨⟨⟨r,s⟩,hr⟩,m,l⟩; rfl
  right_inv := by rintro ⟨⟨r,s,m,l⟩,hc⟩; rfl

def cosetLinearA (k : Fin 3) (r s : Fin 9) : ℤ := 8*(r : ℤ)-4*s+9-4*labels k 0
def cosetLinearB (k : Fin 3) (r s : Fin 9) : ℤ := 8*(s : ℤ)-4*r+9-4*labels k 1
def cosetConstant (k : Fin 3) (r s : Fin 9) : ℤ := (r : ℤ)+s+4*(quadratic k r s/9)

/-- The two unary-theta products furnished by the parity decomposition of one coset. -/
def unaryCoset (q : Lˣ) (k : Fin 3) (r s : Fin 9) : L :=
  (q^cosetConstant k r s : Lˣ) *
    (ThetaAddition.theta (q^36) (q^cosetLinearA k r s) *
      ThetaAddition.theta ((q^36)^3) ((q^cosetLinearA k r s)*(q^cosetLinearB k r s)^2) +
      (q^cosetLinearA k r s : Lˣ)*(q^cosetLinearB k r s : Lˣ)*(q^36 : Lˣ)*
        (ThetaAddition.theta (q^36) ((q^cosetLinearA k r s)*(q^36)) *
          ThetaAddition.theta ((q^36)^3)
            ((q^cosetLinearA k r s)*(q^cosetLinearB k r s)^2*(q^36)^3)))

private theorem coset_power_term (q : Lˣ) (k : Fin 3) (r s : Fin 9) (mn : ℤ × ℤ) :
    (q^cosetConstant k r s : Lˣ) *
      A2ThetaFactorization.term (q^36) (q^cosetLinearA k r s) (q^cosetLinearB k r s) mn =
      ((q^cosetExponent k ⟨r,s,mn.1,mn.2⟩ : Lˣ) : L) := by
  simp only [A2ThetaFactorization.term, ← Units.val_mul]
  congr 1
  simp only [← zpow_natCast, ← zpow_mul, ← zpow_add]
  congr 1
  rw [cosetExponent_expanded]
  simp only [cosetConstant, cosetLinearA, cosetLinearB]
  ring

theorem hasSum_unaryCoset (q : Lˣ) (hq : IsTopologicallyNilpotent (q : L))
    (k : Fin 3) (r s : Fin 9) :
    HasSum (fun mn : ℤ × ℤ => ((q^cosetExponent k ⟨r,s,mn.1,mn.2⟩ : Lˣ) : L))
      (unaryCoset q k r s) := by
  have hp36 : IsTopologicallyNilpotent ((q^36 : Lˣ) : L) := by
    simpa only [Units.val_pow_eq_pow_val] using hq.pow (by decide : 36 ≠ 0)
  have h := (A2ThetaFactorization.hasSum_factorization (q^36)
    (q^cosetLinearA k r s) (q^cosetLinearB k r s) hp36).mul_left
      ((q^cosetConstant k r s : Lˣ) : L)
  simpa only [coset_power_term, unaryCoset] using h

private theorem eval_cosetMonomial (k : Fin 3) (c : ActiveCoset k) :
    eval (cosetMonomial k c) = (mask k c.val.r c.val.s : L)*
      (((p^2)^cosetExponent k c.val : Lˣ) : L) := by
  have hnonneg := cosetExponent_nonneg k c
  simp only [cosetMonomial, monomial_eq_C_mul_X_pow, Product.CubicScalarExtension.eval,
    map_mul, map_pow, intEval_C, intEval_X (Product.CubicScalarExtension.p_nilpotent.pow (by decide : 2 ≠ 0))]
  congr 1
  have he : ((cosetExponent k c.val).toNat : ℤ) = cosetExponent k c.val := Int.toNat_of_nonneg hnonneg
  rw [← he, zpow_natCast, Units.val_pow_eq_pow_val]
  simp only [Int.toNat_natCast, Units.val_pow_eq_pow_val]

/-- Faithful evaluation of the actual integer numerator as twenty-four unary
Jacobi theta products, grouped in its twelve signed residue classes. -/
theorem eval_principalNumerator_unary (k : Fin 3) :
    eval (principalNumerator k) =
      ∑ r : ActiveResidue k, (mask k r.val.1 r.val.2 : L)*unaryCoset (p^2) k r.val.1 r.val.2 := by
  have hs := (hasSum_cosetMonomial k).map eval Product.CubicScalarExtension.eval_continuous
  have hq : IsTopologicallyNilpotent ((p^2 : Lˣ) : L) := by
    simpa only [Units.val_pow_eq_pow_val] using Product.CubicScalarExtension.p_nilpotent.pow (by decide : 2 ≠ 0)
  have hr := (residueCosetEquiv k).hasSum_iff.mpr hs
  have hf (r : ActiveResidue k) : HasSum
      (fun mn : ℤ × ℤ => (eval ∘ cosetMonomial k) (residueCosetEquiv k (r,mn)))
      ((mask k r.val.1 r.val.2 : L)*unaryCoset (p^2) k r.val.1 r.val.2) := by
    have h := (hasSum_unaryCoset (p^2) hq k r.val.1 r.val.2).mul_left (mask k r.val.1 r.val.2 : L)
    simpa only [Function.comp_apply, eval_cosetMonomial, residueCosetEquiv, Equiv.coe_fn_mk] using h
  have hsum := hr.prod_fiberwise hf
  exact hsum.unique (hasSum_fintype _)

end KanadeRussell.Representation.LevelNineNumeratorMasks
