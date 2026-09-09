import KanadeRussell.Representation.LevelNineThetaFactorization
import KanadeRussell.Representation.LevelNineThetaCompression

/-! The finite theta compression is an identity for the actual first principal
numerator under the faithful Laurent substitution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Representation
open LevelNineNumeratorMasks LevelNineThetaCompression
open Product.CubicScalarExtension (L p eval)

private theorem active_sum_221 (f : ℤ → ℤ → L) :
    (∑ r : ActiveResidue 0, (mask 0 r.val.1 r.val.2 : L)*f r.val.1 r.val.2) =
      ((positiveResidues 0).map (fun ab => f ab.1 ab.2)).sum-
        ((negativeResidues 0).map (fun ab => f ab.1 ab.2)).sum := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun r : Fin 9 × Fin 9 => mask 0 r.1 r.2 ≠ 0)
    (fun r => (mask 0 r.1 r.2 : L)*f r.1 r.2)
  have hz : (∑ r : {r : Fin 9 × Fin 9 // ¬ mask 0 r.1 r.2 ≠ 0},
      (mask 0 r.val.1 r.val.2 : L)*f r.val.1 r.val.2) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp [not_ne_iff.mp r.property]
  rw [hz, add_zero] at hs
  rw [hs]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, mask, positiveResidues, negativeResidues]
  ring

private theorem unaryCoset_zero (q : Lˣ) (r s : Fin 9) :
    unaryCoset q 0 r s = cosetUnary221 q r s := by
  let A : ℤ := 8*(r : ℤ)-4*s+1
  let B : ℤ := 8*(s : ℤ)-4*r+1
  let C : ℤ := (r : ℤ)+s+4*(((r : ℤ)*r+(s : ℤ)*s-r*s-2*r-2*s)/9)
  have hA : cosetLinearA 0 r s = A := by norm_num [cosetLinearA, labels, A]; ring
  have hB : cosetLinearB 0 r s = B := by norm_num [cosetLinearB, labels, B]; ring
  have hC : cosetConstant 0 r s = C := by
    norm_num [cosetConstant, quadratic, labels, C, pow_two]
  have hp : (q^36)^3 = q^108 := by group
  have hv : q^A*(q^B)^2 = q^(A+2*B) := by group
  have hu' : q^A*q^36 = q^(A+36) := by group
  have hv' : q^A*(q^B)^2*(q^36)^3 = q^(A+2*B+108) := by group
  have hc : ((q^C : Lˣ) : L)*((q^A : Lˣ) : L)*((q^B : Lˣ) : L)*((q^36 : Lˣ) : L) =
      ((q^(C+A+B+36) : Lˣ) : L) := by
    simp only [← Units.val_mul, ← zpow_natCast, ← zpow_add]
    congr 2
  unfold unaryCoset
  rw [hA, hB, hC, hp, hv, hu', show q^(A+2*B)*q^108 = q^(A+2*B+108) by group]
  change ((q^C : Lˣ) : L)*(unary q 36 A*unary q 108 (A+2*B) +
      ((q^A : Lˣ) : L)*((q^B : Lˣ) : L)*((q^36 : Lˣ) : L)*
        (unary q 36 (A+36)*unary q 108 (A+2*B+108))) =
    pairedTerm q C A (A+2*B)+pairedTerm q (C+A+B+36) (A+36) (A+2*B+108)
  unfold pairedTerm
  linear_combination hc*(unary q 36 (A+36)*unary q 108 (A+2*B+108))

/-- The explicit compressed theta sum is the faithful image of the actual skew numerator. -/
theorem eval_principalNumerator_zero_eq_unaryMask221 :
    eval (principalNumerator 0) = unaryMask221 (p^2) := by
  rw [eval_principalNumerator_unary]
  simp_rw [unaryCoset_zero]
  exact active_sum_221 (fun a b => cosetUnary221 (p^2) a b)

end KanadeRussell.Representation
