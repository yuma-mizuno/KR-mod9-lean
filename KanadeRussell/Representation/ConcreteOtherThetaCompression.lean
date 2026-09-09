import KanadeRussell.Representation.LevelNineThetaFactorization
import KanadeRussell.Representation.LevelNineOtherThetaCompression

/-! The finite theta compression is an identity for the actual remaining principal
numerator under the faithful Laurent substitution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Representation
open LevelNineNumeratorMasks LevelNineThetaCompression LevelNineOtherThetaCompression
open Product.CubicScalarExtension (L p eval)

private theorem active_sum_411 (f : ℤ → ℤ → L) :
    (∑ r : ActiveResidue 1, (mask 1 r.val.1 r.val.2 : L)*f r.val.1 r.val.2) =
      ((positiveResidues 1).map (fun ab => f ab.1 ab.2)).sum-
        ((negativeResidues 1).map (fun ab => f ab.1 ab.2)).sum := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun r : Fin 9 × Fin 9 => mask 1 r.1 r.2 ≠ 0)
    (fun r => (mask 1 r.1 r.2 : L)*f r.1 r.2)
  have hz : (∑ r : {r : Fin 9 × Fin 9 // ¬ mask 1 r.1 r.2 ≠ 0},
      (mask 1 r.val.1 r.val.2 : L)*f r.val.1 r.val.2) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp [not_ne_iff.mp r.property]
  rw [hz, add_zero] at hs
  rw [hs]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, mask, positiveResidues, negativeResidues, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

private theorem unaryCoset_one (q : Lˣ) (r s : Fin 9) :
    unaryCoset q 1 r s = cosetUnary411 q r s := by
  let A : ℤ := 8*(r : ℤ)-4*s+9-4*4
  let B : ℤ := 8*(s : ℤ)-4*r+9-4*1
  let C : ℤ := (r : ℤ)+s+4*(((r : ℤ)*r+(s : ℤ)*s-r*s-4*r-1*s)/9)
  have hA : cosetLinearA 1 r s = A := by norm_num [cosetLinearA, labels, A, Matrix.cons_val_one, Matrix.cons_val_two]
  have hB : cosetLinearB 1 r s = B := by norm_num [cosetLinearB, labels, B, Matrix.cons_val_one, Matrix.cons_val_two]
  have hC : cosetConstant 1 r s = C := by
    norm_num [cosetConstant, quadratic, labels, C, pow_two, Matrix.cons_val_one, Matrix.cons_val_two]
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

/-- The explicit compressed theta sum is the faithful image of the actual vacuum numerator. -/
theorem eval_principalNumerator_one_eq_unaryMask411 :
    eval (principalNumerator 1) = unaryMask411 (p^2) := by
  rw [eval_principalNumerator_unary]
  simp_rw [unaryCoset_one]
  exact active_sum_411 (fun a b => cosetUnary411 (p^2) a b)

private theorem active_sum_112 (f : ℤ → ℤ → L) :
    (∑ r : ActiveResidue 2, (mask 2 r.val.1 r.val.2 : L)*f r.val.1 r.val.2) =
      ((positiveResidues 2).map (fun ab => f ab.1 ab.2)).sum-
        ((negativeResidues 2).map (fun ab => f ab.1 ab.2)).sum := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun r : Fin 9 × Fin 9 => mask 2 r.1 r.2 ≠ 0)
    (fun r => (mask 2 r.1 r.2 : L)*f r.1 r.2)
  have hz : (∑ r : {r : Fin 9 × Fin 9 // ¬ mask 2 r.1 r.2 ≠ 0},
      (mask 2 r.val.1 r.val.2 : L)*f r.val.1 r.val.2) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp [not_ne_iff.mp r.property]
  rw [hz, add_zero] at hs
  rw [hs]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, mask, positiveResidues, negativeResidues, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

private theorem unaryCoset_two (q : Lˣ) (r s : Fin 9) :
    unaryCoset q 2 r s = cosetUnary112 q r s := by
  let A : ℤ := 8*(r : ℤ)-4*s+9-4*1
  let B : ℤ := 8*(s : ℤ)-4*r+9-4*1
  let C : ℤ := (r : ℤ)+s+4*(((r : ℤ)*r+(s : ℤ)*s-r*s-1*r-1*s)/9)
  have hA : cosetLinearA 2 r s = A := by norm_num [cosetLinearA, labels, A, Matrix.cons_val_one, Matrix.cons_val_two]
  have hB : cosetLinearB 2 r s = B := by norm_num [cosetLinearB, labels, B, Matrix.cons_val_one, Matrix.cons_val_two]
  have hC : cosetConstant 2 r s = C := by
    norm_num [cosetConstant, quadratic, labels, C, pow_two, Matrix.cons_val_one, Matrix.cons_val_two]
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

/-- The explicit compressed theta sum is the faithful image of the actual alternating numerator. -/
theorem eval_principalNumerator_two_eq_unaryMask112 :
    eval (principalNumerator 2) = unaryMask112 (p^2) := by
  rw [eval_principalNumerator_unary]
  simp_rw [unaryCoset_two]
  exact active_sum_112 (fun a b => cosetUnary112 (p^2) a b)

end KanadeRussell.Representation
