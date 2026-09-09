import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Tactic

/-! Classification of coefficients obeying the four G2 translation and
reflection equations. No coefficient identity is postulated. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace KanadeRussell.Infra.G2CoefficientRigidity
variable {R : Type*} [CommRing R]

private theorem sequence_translation (p : Rˣ) (f : ℤ → R) (c d : ℤ)
    (hf : ∀ t, f (t+1) = ((p^(2*c*t+c+d) : Rˣ) : R)*f t) (t : ℤ) :
    f t = ((p^(c*t*t+d*t) : Rˣ) : R)*f 0 := by
  induction t using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [hf, ih, ← mul_assoc, ← Units.val_mul, ← zpow_add]
    congr 2
    ring
  | pred n ih =>
    let a : ℤ := 2*c*(-(n : ℤ)-1)+c+d
    apply (p^a).isUnit.mul_left_cancel
    have h := hf (-(n : ℤ)-1)
    rw [show -(n : ℤ)-1+1 = -(n : ℤ) by ring, ih] at h
    rw [← h, ← mul_assoc, ← Units.val_mul, ← zpow_add]
    congr 2
    dsimp [a]
    ring

variable (p : Rˣ) (C : ℤ → ℤ → R)
    (h12 : ∀ M N, C (M+12) N = ((p^(2*(2*M-3*N+11)) : Rˣ) : R)*C M N)
    (h4 : ∀ M N, C M (N+4) = ((p^(2*(-M+2*N+3)) : Rˣ) : R)*C M N)

include h12 in
private theorem translate_first (M N a : ℤ) :
    C (M+12*a) N = ((p^(24*a*a+(4*M-6*N-2)*a) : Rˣ) : R)*C M N := by
  have h := sequence_translation p (fun t => C (M+12*t) N) 24 (4*M-6*N-2) (by
    intro t
    rw [show M+12*(t+1) = (M+12*t)+12 by ring, h12]
    congr 2
    ring) a
  simpa using h

include h4 in
private theorem translate_second (M N b : ℤ) :
    C M (N+4*b) = ((p^(8*b*b+(-2*M+4*N-2)*b) : Rˣ) : R)*C M N := by
  have h := sequence_translation p (fun t => C M (N+4*t)) 8 (-2*M+4*N-2) (by
    intro t
    rw [show N+4*(t+1) = (N+4*t)+4 by ring, h4]
    congr 2
    ring) b
  simpa using h

def translationExponent (M N a b : ℤ) : ℤ :=
  24*a*a+8*b*b-24*a*b+(4*M-6*N-2)*a+(-2*M+4*N-2)*b

include h12 h4 in
theorem translate (M N a b : ℤ) :
    C (M+12*a) (N+4*b) = ((p^translationExponent M N a b : Rˣ) : R)*C M N := by
  rw [translate_second p C h4, translate_first p C h12,
    ← mul_assoc, ← Units.val_mul, ← zpow_add]
  congr 2
  unfold translationExponent
  ring

include h12 h4 in
private theorem reflection_reduce (M N a b r s : ℤ)
    (href : C (M+12*a) (N+4*b) = -C r s) :
    C M N = -((p^(-translationExponent M N a b) : Rˣ) : R)*C r s := by
  have h := translate p C h12 h4 M N a b
  rw [href] at h
  have hh := congrArg (fun z : R => ((p^(-translationExponent M N a b) : Rˣ) : R)*z) h
  simpa only [mul_neg, ← mul_assoc, ← Units.val_mul, ← zpow_add,
    neg_add_cancel, zpow_zero, Units.val_one, one_mul, neg_mul] using hh.symm

private theorem propagate (d e : ℤ) (s : R) {x y v : R}
    (hx : x = -((p^d : Rˣ) : R)*y)
    (hy : y = s*((p^e : Rˣ) : R)*v) :
    x = (-s)*((p^(d+e) : Rˣ) : R)*v := by
  rw [hx, hy, zpow_add, Units.val_mul]
  ring

noncomputable def residueMultiplier (p : Rˣ) : Fin 12 → Fin 4 → R :=
  ![![(1 : R)*((p^(0 : ℤ) : Rˣ) : R), ((-1) : R)*((p^(0 : ℤ) : Rˣ) : R), 0, 0],
    ![((-1) : R)*((p^(0 : ℤ) : Rˣ) : R), 0, (1 : R)*((p^(0 : ℤ) : Rˣ) : R), 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![((-1) : R)*((p^(2 : ℤ) : Rˣ) : R), (1 : R)*((p^(0 : ℤ) : Rˣ) : R), 0, 0],
    ![0, 0, 0, 0],
    ![0, (1 : R)*((p^(2 : ℤ) : Rˣ) : R), ((-1) : R)*((p^(0 : ℤ) : Rˣ) : R), 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![(1 : R)*((p^(12 : ℤ) : Rˣ) : R), 0, ((-1) : R)*((p^(4 : ℤ) : Rˣ) : R), 0],
    ![0, ((-1) : R)*((p^(10 : ℤ) : Rˣ) : R), (1 : R)*((p^(6 : ℤ) : Rˣ) : R), 0],
    ![0, 0, 0, 0]]

variable (htwo : IsUnit (2 : R))
    (hs : ∀ M N, C (3*N-M+1) N = -C M N)
    (ht : ∀ M N, C M (M-N+1) = -C M N)

include h12 h4 htwo hs ht in
/-- The four equations force all 48 residue coefficients from the constant one. -/
theorem residue_classification (M : Fin 12) (N : Fin 4) :
    C M N = residueMultiplier p M N * C 0 0 := by
  have v0_0 : C 0 0 = (1 : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by simp
  have v1_0 : C 1 0 = ((-1) : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
    have he : C 1 0 = -((p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
      have h := reflection_reduce p C h12 h4 1 0 0 0 0 0 (by
        convert hs 0 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have h := propagate p 0 0 (1 : R) he v0_0
    convert h using 1; norm_num
  have v0_1 : C 0 1 = ((-1) : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
    have he : C 0 1 = -((p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
      have h := reflection_reduce p C h12 h4 0 1 0 0 0 0 (by
        convert ht 0 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have h := propagate p 0 0 (1 : R) he v0_0
    convert h using 1; norm_num
  have v1_2 : C 1 2 = (1 : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
    have he : C 1 2 = -((p^(0 : ℤ) : Rˣ) : R)*C 1 0 := by
      have h := reflection_reduce p C h12 h4 1 2 0 0 1 0 (by
        convert ht 1 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have h := propagate p 0 0 ((-1) : R) he v1_0
    convert h using 1; norm_num
  have v4_1 : C 4 1 = (1 : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
    have he : C 4 1 = -((p^(0 : ℤ) : Rˣ) : R)*C 0 1 := by
      have h := reflection_reduce p C h12 h4 4 1 0 0 0 1 (by
        convert hs 0 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have h := propagate p 0 0 ((-1) : R) he v0_1
    convert h using 1; norm_num
  have v6_2 : C 6 2 = ((-1) : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
    have he : C 6 2 = -((p^(0 : ℤ) : Rˣ) : R)*C 1 2 := by
      have h := reflection_reduce p C h12 h4 6 2 0 0 1 2 (by
        convert hs 1 2 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have h := propagate p 0 0 (1 : R) he v1_2
    convert h using 1; norm_num
  have v4_0 : C 4 0 = ((-1) : R)*((p^(2 : ℤ) : Rˣ) : R)*C 0 0 := by
    have he : C 4 0 = -((p^(2 : ℤ) : Rˣ) : R)*C 4 1 := by
      have h := reflection_reduce p C h12 h4 4 0 0 1 4 1 (by
        convert ht 4 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have h := propagate p 2 0 (1 : R) he v4_1
    convert h using 1; norm_num
  have v6_1 : C 6 1 = (1 : R)*((p^(2 : ℤ) : Rˣ) : R)*C 0 0 := by
    have he : C 6 1 = -((p^(2 : ℤ) : Rˣ) : R)*C 6 2 := by
      have h := reflection_reduce p C h12 h4 6 1 0 1 6 2 (by
        convert ht 6 2 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have h := propagate p 2 0 ((-1) : R) he v6_2
    convert h using 1; norm_num
  have v9_0 : C 9 0 = (1 : R)*((p^(12 : ℤ) : Rˣ) : R)*C 0 0 := by
    have he : C 9 0 = -((p^(10 : ℤ) : Rˣ) : R)*C 4 0 := by
      have h := reflection_reduce p C h12 h4 9 0 (-1) 0 4 0 (by
        convert hs 4 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have h := propagate p 10 2 ((-1) : R) he v4_0
    convert h using 1; norm_num
  have v10_1 : C 10 1 = ((-1) : R)*((p^(10 : ℤ) : Rˣ) : R)*C 0 0 := by
    have he : C 10 1 = -((p^(8 : ℤ) : Rˣ) : R)*C 6 1 := by
      have h := reflection_reduce p C h12 h4 10 1 (-1) 0 6 1 (by
        convert hs 6 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have h := propagate p 8 2 (1 : R) he v6_1
    convert h using 1; norm_num
  have v9_2 : C 9 2 = ((-1) : R)*((p^(4 : ℤ) : Rˣ) : R)*C 0 0 := by
    have he : C 9 2 = -((p^(-8 : ℤ) : Rˣ) : R)*C 9 0 := by
      have h := reflection_reduce p C h12 h4 9 2 0 2 9 0 (by
        convert ht 9 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have h := propagate p (-8) 12 (1 : R) he v9_0
    convert h using 1; norm_num
  have v10_2 : C 10 2 = (1 : R)*((p^(6 : ℤ) : Rˣ) : R)*C 0 0 := by
    have he : C 10 2 = -((p^(-4 : ℤ) : Rˣ) : R)*C 10 1 := by
      have h := reflection_reduce p C h12 h4 10 2 0 2 10 1 (by
        convert ht 10 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have h := propagate p (-4) 10 ((-1) : R) he v10_1
    convert h using 1; norm_num
  have v7_2 : C 7 2 = 0 := by
    have he : C 7 2 = -((p^(0 : ℤ) : Rˣ) : R)*C 7 2 := by
      have h := reflection_reduce p C h12 h4 7 2 0 1 7 2 (by
        convert ht 7 2 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have hz : (2 : R)*C 7 2 = 0 := by
      norm_num at he
      linear_combination he
    exact htwo.mul_left_cancel (by simpa only [mul_zero] using hz)
  have v0_2 : C 0 2 = 0 := by
    have he : C 0 2 = -((p^(0 : ℤ) : Rˣ) : R)*C 7 2 := by
      have h := reflection_reduce p C h12 h4 0 2 0 0 7 2 (by
        convert hs 7 2 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v7_2, mul_zero, neg_zero] using he
  have v0_3 : C 0 3 = 0 := by
    have he : C 0 3 = -((p^(2 : ℤ) : Rˣ) : R)*C 0 2 := by
      have h := reflection_reduce p C h12 h4 0 3 0 (-1) 0 2 (by
        convert ht 0 2 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v0_2, mul_zero, neg_zero] using he
  have v10_3 : C 10 3 = 0 := by
    have he : C 10 3 = -((p^(0 : ℤ) : Rˣ) : R)*C 0 3 := by
      have h := reflection_reduce p C h12 h4 10 3 0 0 0 3 (by
        convert hs 0 3 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v0_3, mul_zero, neg_zero] using he
  have v10_0 : C 10 0 = 0 := by
    have he : C 10 0 = -((p^(12 : ℤ) : Rˣ) : R)*C 10 3 := by
      have h := reflection_reduce p C h12 h4 10 0 0 2 10 3 (by
        convert ht 10 3 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v10_3, mul_zero, neg_zero] using he
  have v3_0 : C 3 0 = 0 := by
    have he : C 3 0 = -((p^(-14 : ℤ) : Rˣ) : R)*C 10 0 := by
      have h := reflection_reduce p C h12 h4 3 0 (-1) 0 10 0 (by
        convert hs 10 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v10_0, mul_zero, neg_zero] using he
  have v1_1 : C 1 1 = 0 := by
    have he : C 1 1 = -((p^(0 : ℤ) : Rˣ) : R)*C 1 1 := by
      have h := reflection_reduce p C h12 h4 1 1 0 0 1 1 (by
        convert ht 1 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have hz : (2 : R)*C 1 1 = 0 := by
      norm_num at he
      linear_combination he
    exact htwo.mul_left_cancel (by simpa only [mul_zero] using hz)
  have v3_1 : C 3 1 = 0 := by
    have he : C 3 1 = -((p^(0 : ℤ) : Rˣ) : R)*C 1 1 := by
      have h := reflection_reduce p C h12 h4 3 1 0 0 1 1 (by
        convert hs 1 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v1_1, mul_zero, neg_zero] using he
  have v3_3 : C 3 3 = 0 := by
    have he : C 3 3 = -((p^(0 : ℤ) : Rˣ) : R)*C 3 1 := by
      have h := reflection_reduce p C h12 h4 3 3 0 0 3 1 (by
        convert ht 3 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v3_1, mul_zero, neg_zero] using he
  have v7_3 : C 7 3 = 0 := by
    have he : C 7 3 = -((p^(0 : ℤ) : Rˣ) : R)*C 3 3 := by
      have h := reflection_reduce p C h12 h4 7 3 0 0 3 3 (by
        convert hs 3 3 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v3_3, mul_zero, neg_zero] using he
  have v7_1 : C 7 1 = 0 := by
    have he : C 7 1 = -((p^(4 : ℤ) : Rˣ) : R)*C 7 3 := by
      have h := reflection_reduce p C h12 h4 7 1 0 1 7 3 (by
        convert ht 7 3 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v7_3, mul_zero, neg_zero] using he
  have v9_1 : C 9 1 = 0 := by
    have he : C 9 1 = -((p^(4 : ℤ) : Rˣ) : R)*C 7 1 := by
      have h := reflection_reduce p C h12 h4 9 1 (-1) 0 7 1 (by
        convert hs 7 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v7_1, mul_zero, neg_zero] using he
  have v1_3 : C 1 3 = 0 := by
    have he : C 1 3 = -((p^(0 : ℤ) : Rˣ) : R)*C 1 3 := by
      have h := reflection_reduce p C h12 h4 1 3 0 (-1) 1 3 (by
        convert ht 1 3 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have hz : (2 : R)*C 1 3 = 0 := by
      norm_num at he
      linear_combination he
    exact htwo.mul_left_cancel (by simpa only [mul_zero] using hz)
  have v9_3 : C 9 3 = 0 := by
    have he : C 9 3 = -((p^(0 : ℤ) : Rˣ) : R)*C 1 3 := by
      have h := reflection_reduce p C h12 h4 9 3 0 0 1 3 (by
        convert hs 1 3 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v1_3, mul_zero, neg_zero] using he
  have v11_0 : C 11 0 = 0 := by
    have he : C 11 0 = -((p^(0 : ℤ) : Rˣ) : R)*C 11 0 := by
      have h := reflection_reduce p C h12 h4 11 0 0 3 11 0 (by
        convert ht 11 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have hz : (2 : R)*C 11 0 = 0 := by
      norm_num at he
      linear_combination he
    exact htwo.mul_left_cancel (by simpa only [mul_zero] using hz)
  have v2_0 : C 2 0 = 0 := by
    have he : C 2 0 = -((p^(-18 : ℤ) : Rˣ) : R)*C 11 0 := by
      have h := reflection_reduce p C h12 h4 2 0 (-1) 0 11 0 (by
        convert hs 11 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v11_0, mul_zero, neg_zero] using he
  have v2_3 : C 2 3 = 0 := by
    have he : C 2 3 = -((p^(0 : ℤ) : Rˣ) : R)*C 2 0 := by
      have h := reflection_reduce p C h12 h4 2 3 0 0 2 0 (by
        convert ht 2 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v2_0, mul_zero, neg_zero] using he
  have v8_3 : C 8 3 = 0 := by
    have he : C 8 3 = -((p^(0 : ℤ) : Rˣ) : R)*C 2 3 := by
      have h := reflection_reduce p C h12 h4 8 3 0 0 2 3 (by
        convert hs 2 3 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v2_3, mul_zero, neg_zero] using he
  have v8_2 : C 8 2 = 0 := by
    have he : C 8 2 = -((p^(2 : ℤ) : Rˣ) : R)*C 8 3 := by
      have h := reflection_reduce p C h12 h4 8 2 0 1 8 3 (by
        convert ht 8 3 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v8_3, mul_zero, neg_zero] using he
  have v11_2 : C 11 2 = 0 := by
    have he : C 11 2 = -((p^(6 : ℤ) : Rˣ) : R)*C 8 2 := by
      have h := reflection_reduce p C h12 h4 11 2 (-1) 0 8 2 (by
        convert hs 8 2 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v8_2, mul_zero, neg_zero] using he
  have v2_1 : C 2 1 = 0 := by
    have he : C 2 1 = -((p^(0 : ℤ) : Rˣ) : R)*C 2 1 := by
      have h := reflection_reduce p C h12 h4 2 1 0 0 2 1 (by
        convert hs 2 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have hz : (2 : R)*C 2 1 = 0 := by
      norm_num at he
      linear_combination he
    exact htwo.mul_left_cancel (by simpa only [mul_zero] using hz)
  have v2_2 : C 2 2 = 0 := by
    have he : C 2 2 = -((p^(0 : ℤ) : Rˣ) : R)*C 2 1 := by
      have h := reflection_reduce p C h12 h4 2 2 0 0 2 1 (by
        convert ht 2 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v2_1, mul_zero, neg_zero] using he
  have v5_2 : C 5 2 = 0 := by
    have he : C 5 2 = -((p^(0 : ℤ) : Rˣ) : R)*C 2 2 := by
      have h := reflection_reduce p C h12 h4 5 2 0 0 2 2 (by
        convert hs 2 2 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v2_2, mul_zero, neg_zero] using he
  have v5_0 : C 5 0 = 0 := by
    have he : C 5 0 = -((p^(4 : ℤ) : Rˣ) : R)*C 5 2 := by
      have h := reflection_reduce p C h12 h4 5 0 0 1 5 2 (by
        convert ht 5 2 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v5_2, mul_zero, neg_zero] using he
  have v8_0 : C 8 0 = 0 := by
    have he : C 8 0 = -((p^(6 : ℤ) : Rˣ) : R)*C 5 0 := by
      have h := reflection_reduce p C h12 h4 8 0 (-1) 0 5 0 (by
        convert hs 5 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v5_0, mul_zero, neg_zero] using he
  have v8_1 : C 8 1 = 0 := by
    have he : C 8 1 = -((p^(-4 : ℤ) : Rˣ) : R)*C 8 0 := by
      have h := reflection_reduce p C h12 h4 8 1 0 2 8 0 (by
        convert ht 8 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v8_0, mul_zero, neg_zero] using he
  have v3_2 : C 3 2 = 0 := by
    have he : C 3 2 = -((p^(0 : ℤ) : Rˣ) : R)*C 3 2 := by
      have h := reflection_reduce p C h12 h4 3 2 0 0 3 2 (by
        convert ht 3 2 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have hz : (2 : R)*C 3 2 = 0 := by
      norm_num at he
      linear_combination he
    exact htwo.mul_left_cancel (by simpa only [mul_zero] using hz)
  have v4_2 : C 4 2 = 0 := by
    have he : C 4 2 = -((p^(0 : ℤ) : Rˣ) : R)*C 3 2 := by
      have h := reflection_reduce p C h12 h4 4 2 0 0 3 2 (by
        convert hs 3 2 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v3_2, mul_zero, neg_zero] using he
  have v4_3 : C 4 3 = 0 := by
    have he : C 4 3 = -((p^(0 : ℤ) : Rˣ) : R)*C 4 2 := by
      have h := reflection_reduce p C h12 h4 4 3 0 0 4 2 (by
        convert ht 4 2 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v4_2, mul_zero, neg_zero] using he
  have v6_3 : C 6 3 = 0 := by
    have he : C 6 3 = -((p^(0 : ℤ) : Rˣ) : R)*C 4 3 := by
      have h := reflection_reduce p C h12 h4 6 3 0 0 4 3 (by
        convert hs 4 3 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v4_3, mul_zero, neg_zero] using he
  have v6_0 : C 6 0 = 0 := by
    have he : C 6 0 = -((p^(6 : ℤ) : Rˣ) : R)*C 6 3 := by
      have h := reflection_reduce p C h12 h4 6 0 0 1 6 3 (by
        convert ht 6 3 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v6_3, mul_zero, neg_zero] using he
  have v7_0 : C 7 0 = 0 := by
    have he : C 7 0 = -((p^(2 : ℤ) : Rˣ) : R)*C 6 0 := by
      have h := reflection_reduce p C h12 h4 7 0 (-1) 0 6 0 (by
        convert hs 6 0 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v6_0, mul_zero, neg_zero] using he
  have v5_1 : C 5 1 = 0 := by
    have he : C 5 1 = -((p^(0 : ℤ) : Rˣ) : R)*C 5 1 := by
      have h := reflection_reduce p C h12 h4 5 1 0 1 5 1 (by
        convert ht 5 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have hz : (2 : R)*C 5 1 = 0 := by
      norm_num at he
      linear_combination he
    exact htwo.mul_left_cancel (by simpa only [mul_zero] using hz)
  have v11_1 : C 11 1 = 0 := by
    have he : C 11 1 = -((p^(12 : ℤ) : Rˣ) : R)*C 5 1 := by
      have h := reflection_reduce p C h12 h4 11 1 (-1) 0 5 1 (by
        convert hs 5 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v5_1, mul_zero, neg_zero] using he
  have v11_3 : C 11 3 = 0 := by
    have he : C 11 3 = -((p^(-8 : ℤ) : Rˣ) : R)*C 11 1 := by
      have h := reflection_reduce p C h12 h4 11 3 0 2 11 1 (by
        convert ht 11 1 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    simpa only [v11_1, mul_zero, neg_zero] using he
  have v5_3 : C 5 3 = 0 := by
    have he : C 5 3 = -((p^(0 : ℤ) : Rˣ) : R)*C 5 3 := by
      have h := reflection_reduce p C h12 h4 5 3 0 0 5 3 (by
        convert hs 5 3 using 1; norm_num)
      convert h using 1; norm_num [translationExponent]
    have hz : (2 : R)*C 5 3 = 0 := by
      norm_num at he
      linear_combination he
    exact htwo.mul_left_cancel (by simpa only [mul_zero] using hz)
  fin_cases M <;> fin_cases N <;> norm_num only [residueMultiplier, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact v0_0
  · simpa using v0_1
  · simpa using v0_2
  · simpa using v0_3
  · simpa using v1_0
  · simpa using v1_1
  · simpa using v1_2
  · simpa using v1_3
  · simpa using v2_0
  · simpa using v2_1
  · simpa using v2_2
  · simpa using v2_3
  · simpa using v3_0
  · simpa using v3_1
  · simpa using v3_2
  · simpa using v3_3
  · simpa using v4_0
  · simpa using v4_1
  · simpa using v4_2
  · simpa using v4_3
  · simpa using v5_0
  · simpa using v5_1
  · simpa using v5_2
  · simpa using v5_3
  · simpa using v6_0
  · simpa using v6_1
  · simpa using v6_2
  · simpa using v6_3
  · simpa using v7_0
  · simpa using v7_1
  · simpa using v7_2
  · simpa using v7_3
  · simpa using v8_0
  · simpa using v8_1
  · simpa using v8_2
  · simpa using v8_3
  · simpa using v9_0
  · simpa using v9_1
  · simpa using v9_2
  · simpa using v9_3
  · simpa using v10_0
  · simpa using v10_1
  · simpa using v10_2
  · simpa using v10_3
  · simpa using v11_0
  · simpa using v11_1
  · simpa using v11_2
  · simpa using v11_3

include h12 h4 htwo hs ht in
/-- The 48 residue identities and the integer translation law classify every coefficient. -/
theorem classification (M N : ℤ) :
    C M N = ((p^translationExponent (M%12) (N%4) (M/12) (N/4) : Rˣ) : R)*
      residueMultiplier p ⟨(M%12).toNat, by omega⟩ ⟨(N%4).toNat, by omega⟩ * C 0 0 := by
  let r : Fin 12 := ⟨(M%12).toNat, by omega⟩
  let s : Fin 4 := ⟨(N%4).toNat, by omega⟩
  have hr : (r : ℤ) = M%12 := Int.toNat_of_nonneg (Int.emod_nonneg M (by norm_num))
  have hs' : (s : ℤ) = N%4 := Int.toNat_of_nonneg (Int.emod_nonneg N (by norm_num))
  have hc := residue_classification p C h12 h4 htwo hs ht r s
  rw [hr, hs'] at hc
  have h := translate p C h12 h4 (M%12) (N%4) (M/12) (N/4)
  rw [Int.emod_add_mul_ediv M 12, Int.emod_add_mul_ediv N 4, hc] at h
  simpa only [mul_assoc] using h

end KanadeRussell.Infra.G2CoefficientRigidity
