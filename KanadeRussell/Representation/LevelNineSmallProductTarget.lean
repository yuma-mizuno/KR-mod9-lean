import KanadeRussell.Representation.PrincipalMaskNumerators
import KanadeRussell.Infra.JacobiQuintuple
import KanadeRussell.Product.CubicScalarExtension

/-! A smaller cleared product target for the first numerator, transported
through the faithful Laurent specialization `q=p^2`. The target's evaluation
is proved entirely from the existing Euler/Jacobi products. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open PowerSeries PowerSeries.WithPiTopology MvLaurentSeries
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Representation.LevelNineSmallProductTarget
open Infra.ThetaAddition Product
open Product.CubicScalarExtension (L p eval p_nilpotent eval_injective)

private theorem p_pow_tPow (n : ℕ) : p^n=Product.LevelNine.tPow (R:=ℂ) n := by
  apply Units.ext
  change (xPow () 1 : L)^n=xPow () (n:ℤ)
  rw [xPow_pow]
  congr 1
  simp

private theorem eval_eq_baseChange2 : eval=Product.LevelNine.baseChange2 (R:=ℂ) := by
  unfold Product.CubicScalarExtension.eval Product.LevelNine.baseChange2
  congr 1
  change (xPow () 1 : L)^2=xPow () 2
  rw [xPow_pow]
  norm_num

theorem eval_E (d : ℕ) (hd : 0<d) :
    eval (E d)=((p:L)^(2*d);(p:L)^(2*d))_∞ := by
  simpa only [Product.CubicScalarExtension.eval,← pow_mul] using
    intEval_E_of_nilpotent ((p:L)^2) (p_nilpotent.pow (by decide : 2 ≠ 0)) d hd

theorem eval_J (r : ℕ) (hr : r<9) :
    eval (Product.J r)=jacobi (p^9) (p^(2*r)) := by
  rw [eval_eq_baseChange2,← Product.LevelNine.J_even r hr]
  simp only [Product.LevelNine.J,p_pow_tPow,Nat.cast_mul,Nat.cast_ofNat]

private theorem nilpotent_pow (n : ℕ) (hn : n≠0) :
    IsTopologicallyNilpotent ((p^n:Lˣ):L) := by
  simpa only [Units.val_pow_eq_pow_val] using p_nilpotent.pow hn

private theorem pow_div (a b c : ℕ) (h : a=b+c) :
    (p^a/p^b:Lˣ)=p^c := by
  rw [h,Nat.add_comm b c,pow_add,div_eq_mul_inv,mul_assoc,mul_inv_cancel,mul_one]

private theorem progression_split (a : ℕ) :
    ((p:L)^a;(p:L)^18)_∞ =
      ((p:L)^a;(p:L)^36)_∞*((p:L)^(a+18);(p:L)^36)_∞ := by
  have hh := qPochhammerInf_eq_prod_range (a:=(p:L)^a) (m:=2) (by decide)
    (p_nilpotent.pow (by decide : 18 ≠ 0))
  simpa only [Finset.prod_range_succ,Finset.prod_range_zero,pow_zero,mul_one,
    one_mul,pow_one,← pow_mul,← pow_add,Nat.reduceMul,Nat.add_zero] using hh

/-- Splitting the two progressions modulo eighteen gives the exact doubling factor. -/
theorem J_four_doubling :
    eval (E 18)^2*eval (Product.J 4)=
      eval (E 9)*jacobi (p^18) (p^8)*jacobi (p^18) (p^26) := by
  rw [eval_E 18 (by decide),eval_E 9 (by decide),eval_J 4 (by decide)]
  norm_num only [Nat.reduceMul]
  rw [jacobi_eq_product (p^9) (p^8) (nilpotent_pow 9 (by decide)),
    jacobi_eq_product (p^18) (p^8) (nilpotent_pow 18 (by decide)),
    jacobi_eq_product (p^18) (p^26) (nilpotent_pow 18 (by decide))]
  simp only [← pow_mul,Nat.reduceMul,
    pow_div 18 8 10 (by decide),pow_div 36 8 28 (by decide),
    pow_div 36 26 10 (by decide),Units.val_pow_eq_pow_val]
  rw [progression_split 8,progression_split 10]
  norm_num only [Nat.reduceAdd]
  ring

/-- The two lower-level Jacobi values in the quintuple-product evaluation. -/
noncomputable def smallBracket : L :=
  jacobi (p^27) ((-1:Lˣ)*p^30)-(p:L)^4*jacobi (p^27) ((-1:Lˣ)*p^48)

noncomputable def smallTarget : L :=
  eval (E 1)*jacobi (p^18) (p^8)*smallBracket

theorem J_two_quintuple :
    eval (Product.J 2)*jacobi (p^18) (p^26)=eval (E 18)*smallBracket := by
  have h := Infra.JacobiQuintuple.quintuple (p^9) (p^4)
    (nilpotent_pow 9 (by decide))
  simp only [← pow_mul,Nat.reduceMul,Units.val_pow_eq_pow_val] at h
  have ha : p^18*p^8=p^26 := by
    simp only [← pow_add]
  have hb : (-1:Lˣ)*p^12*p^18=(-1:Lˣ)*p^30 := by
    simp only [mul_assoc,← pow_add]
  have hc : (-1:Lˣ)*p^12*p^36=(-1:Lˣ)*p^48 := by
    simp only [mul_assoc,← pow_add]
  rw [ha,hb,hc] at h
  simpa only [eval_J 2 (by decide),eval_E 18 (by decide),smallBracket,Nat.reduceMul] using h

/-- The existing `(2,2,1)` product has the exact smaller cleared target.
Here `p^2` is the original series variable, so there is no additional shift. -/
theorem eval_denominator221_small :
    eval (E 18)*eval (dualAffineDenominator 2 2 1)=smallTarget := by
  have hprod := congrArg eval dualAffineDenominator_221_J_cleared
  simp only [map_mul] at hprod
  have he9 := (isUnit_E 9 (by decide)).map eval
  have he18 := (isUnit_E 18 (by decide)).map eval
  apply (he9.mul he18).mul_left_inj.mp
  unfold smallTarget
  linear_combination eval (E 18)^2*hprod+
    eval (E 1)*eval (Product.J 2)*J_four_doubling+
    eval (E 1)*eval (E 9)*jacobi (p^18) (p^8)*J_two_quintuple

/-- The faithful Laurent equation is equivalent to the original integral numerator target. -/
theorem numerator_eq_221_iff_small (N : PowerSeries ℤ) :
    N=dualAffineDenominator 2 2 1 ↔ eval (E 18)*eval N=smallTarget := by
  constructor
  · intro h
    rw [h]
    exact eval_denominator221_small
  · intro h
    apply eval_injective
    exact ((isUnit_E 18 (by decide)).map eval).mul_right_inj.mp
      (h.trans eval_denominator221_small.symm)

theorem numerator_cleared_iff_small (N : PowerSeries ℤ) :
    E 9*N=E 1*Product.J 2*Product.J 4 ↔ eval (E 18)*eval N=smallTarget := by
  rw [← numerator_eq_221_iff_small]
  constructor
  · exact numerator_eq_221_of_J_cleared N
  · intro h
    rw [h]
    exact dualAffineDenominator_221_J_cleared

theorem principalNumerator_zero_cleared_iff_small :
    E 9*LevelNineNumeratorMasks.principalNumerator 0=E 1*Product.J 2*Product.J 4 ↔
      eval (E 18)*eval (LevelNineNumeratorMasks.principalNumerator 0)=smallTarget :=
  numerator_cleared_iff_small _

end KanadeRussell.Representation.LevelNineSmallProductTarget
