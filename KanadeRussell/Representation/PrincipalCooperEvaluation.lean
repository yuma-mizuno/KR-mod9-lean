import KanadeRussell.Infra.G2DenominatorIdentity
import KanadeRussell.Infra.G2JacobiFunctionalEquations
import KanadeRussell.Infra.A2CoefficientResidues
import KanadeRussell.Representation.LevelNineCooperSummation
import KanadeRussell.Representation.LevelNineSmallProductTarget
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Representation.PrincipalCooperEvaluation
open LevelNineNumeratorMasks LevelNineCooperReindexing
open Product.CubicScalarExtension (L p eval)

def cooperShear : (Fin 12 × (ℤ × ℤ)) ≃ (Fin 12 × (ℤ × ℤ)) where
  toFun z := (z.1,z.2.1,z.2.1+z.2.2)
  invFun z := (z.1,z.2.1,z.2.2-z.2.1)
  left_inv := by rintro ⟨h,m,l⟩; dsimp; congr 2; omega
  right_inv := by rintro ⟨h,m,l⟩; dsimp; congr 2; omega

theorem specialized_monomial {R : Type*} [CommRing R] (q : Rˣ) (k : Fin 3)
    (h : Fin 12) (m l : ℤ) :
    (q^9)^(2*(12*m^2-12*m*(m+l)+4*(m+l)^2-m-(m+l)+
      (2*m-(m+l))*(cooperPowers h).1+(2*(m+l)-3*m)*(cooperPowers h).2)) *
      (q^(2*labels k 2))^(12*m+(cooperPowers h).1) *
      (q^(2*labels k 1))^(4*(m+l)+(cooperPowers h).2) =
    (q^2)^cooperExponent k h (m,l) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul,ofMul_zpow,ofMul_pow,cooperExponent]
  module

theorem euler_nine : Infra.A2CoefficientResidues.euler (p^9) = eval (E 9) := by
  rw [LevelNineSmallProductTarget.eval_E 9 (by decide)]
  simp only [Infra.A2CoefficientResidues.euler,Units.val_pow_eq_pow_val,← pow_mul]

theorem isUnit_two : IsUnit (2:L) := by
  simpa only [map_ofNat] using
    (isUnit_iff_ne_zero.mpr (by norm_num : (2:ℂ) ≠ 0)).map Product.CubicScalarExtension.scalar

open Infra.G2DenominatorIdentity

theorem flattened_specialization (k : Fin 3) (z : Fin 12 × (ℤ × ℤ)) :
    flattenedTerm (p^9) (p^(2*labels k 2)) (p^(2*labels k 1)) (cooperShear z) =
      (cooperSign z.1:L)*(↑((p^2)^cooperExponent k z.1 z.2):L) := by
  rcases z with ⟨h,m,l⟩
  change (cooperSign h:L)*(↑((p^9)^(2*(12*m*m-12*m*(m+l)+4*(m+l)*(m+l)-m-(m+l)+
      (2*m-(m+l))*(cooperPowers h).1+(2*(m+l)-3*m)*(cooperPowers h).2)) *
      (p^(2*labels k 2))^(12*m+(cooperPowers h).1) *
      (p^(2*labels k 1))^(4*(m+l)+(cooperPowers h).2)):L) = _
  congr 1
  exact congrArg Units.val (by simpa only [pow_two,mul_assoc] using specialized_monomial p k h m l)

/-- The actual principal numerator evaluates to the specialized six-Jacobi
product, with the exact fourth Euler factor. -/
theorem eval_principalNumerator_g2 (k : Fin 3) :
    eval (E 9)^4*eval (principalNumerator k) =
      Infra.G2JacobiFunctionalEquations.g2Product (p^9) (p^(2*labels k 2)) (p^(2*labels k 1)) := by
  have hp9 : IsTopologicallyNilpotent ((p^9:Lˣ):L) := by
    simpa only [Units.val_pow_eq_pow_val] using
      Product.CubicScalarExtension.p_nilpotent.pow (by decide : 9 ≠ 0)
  have hg := cooperShear.hasSum_iff.mpr
    (hasSum_euler_mul_flattened (p^9) (p^(2*labels k 2)) (p^(2*labels k 1)) hp9 isUnit_two)
  have hn := (hasSum_cooper_principalNumerator k).mul_left (eval (E 9)^4)
  apply hn.unique
  apply hg.congr_fun
  intro z
  change _ = Infra.A2CoefficientResidues.euler (p^9)^4*
    flattenedTerm (p^9) (p^(2*labels k 2)) (p^(2*labels k 1)) (cooperShear z)
  rw [euler_nine,flattened_specialization]
end KanadeRussell.Representation.PrincipalCooperEvaluation
