import KanadeRussell.Representation.LevelNineThetaCompression
import KanadeRussell.Infra.JacobiQuintuple

/-! Exact quintuple-product substitutions in the first level-nine numerator.
All identities are cleared by an Euler factor, so no invertibility of an
Euler product is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped QTheory
namespace KanadeRussell.Representation.LevelNineQuintupleFactors
open Infra.ThetaAddition LevelNineThetaCompression
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def euler144 (q : Rˣ) : R := ((q:R)^144;(q:R)^144)_∞

noncomputable def quintupleProduct (q : Rˣ) (b : ℤ) : R :=
  jacobi (q^36) (q^b) * jacobi (q^72) (q^(72+2*b))

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem jacobi_neg_power (q : Rˣ) (d : ℕ) (a : ℤ) :
    jacobi (q^d) ((-1:Rˣ)*q^a)=unary q d (a-d) := by
  unfold jacobi unary
  congr 1
  simp only [neg_mul,neg_neg,one_mul]
  rw [← zpow_natCast,div_eq_mul_inv,← zpow_sub]

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem cube_power_mul (q : Rˣ) (b : ℤ) (d : ℕ) :
    (q^b)^3*q^d=q^(3*b+d) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul,ofMul_pow,ofMul_zpow]
  module

/-- The general specialization at `p=q^36`, `z=q^b`. -/
theorem quintupleProduct_eq (q : Rˣ) (hq : IsTopologicallyNilpotent (q:R)) (b : ℤ) :
    quintupleProduct q b = euler144 q *
      (unary q 108 (3*b-36)-((q^b:Rˣ):R)*unary q 108 (3*b+36)) := by
  have hp : IsTopologicallyNilpotent ((q^36:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hq.pow (by decide : 36 ≠ 0)
  have hs : (q^36)^2*(q^b)^2=q^(72+2*b) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul,ofMul_pow,ofMul_zpow]
    module
  have h := Infra.JacobiQuintuple.quintuple (q^36) (q^b) hp
  rw [hs] at h
  simp only [← pow_mul,Nat.reduceMul,Units.val_pow_eq_pow_val] at h
  rw [mul_assoc,cube_power_mul,mul_assoc,cube_power_mul] at h
  rw [jacobi_neg_power,jacobi_neg_power] at h
  have he1 : 3*b+(72:ℕ)-(108:ℕ)=3*b-36 := by omega
  have he2 : 3*b+(144:ℕ)-(108:ℕ)=3*b+36 := by omega
  simpa only [quintupleProduct,euler144,he1,he2] using h

private theorem scaled_unary_shift (q : Rˣ) (hq : IsTopologicallyNilpotent (q:R))
    (c a : ℤ) :
    ((q^c:Rˣ):R)*unary q 108 (a+216)=
      ((q^(c-108-a):Rˣ):R)*unary q 108 a := by
  have hp : IsTopologicallyNilpotent ((q^108:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hq.pow (by decide : 108 ≠ 0)
  have he : (q^108)^2*q^a=q^(a+216) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul,ofMul_pow,ofMul_zpow]
    module
  have hv : ((q^c:Rˣ):R)*(((q^108)⁻¹*(q^a)⁻¹:Rˣ):R)=
      ((q^(c-108-a):Rˣ):R) := by
    rw [← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul,ofMul_pow,ofMul_zpow,ofMul_inv]
    module
  unfold unary
  rw [← he,theta_shift (q^108) (q^a) hp,← mul_assoc,hv]

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem unary_neg (q : Rˣ) (d : ℕ) (a : ℤ) :
    unary q d (-a)=unary q d a := by
  simp only [unary,zpow_neg,theta_inv]

theorem quintupleProduct_11 (q : Rˣ) (hq : IsTopologicallyNilpotent (q:R)) :
    quintupleProduct q 11 = euler144 q *
      (unary q 108 3-(q:R)^11*unary q 108 69) := by
  have h := quintupleProduct_eq q hq 11
  norm_num only [Int.reduceMul,Int.reduceSub,Int.reduceAdd] at h
  rw [unary_neg] at h
  simpa only [zpow_ofNat,Units.val_pow_eq_pow_val] using h

theorem quintupleProduct_5 (q : Rˣ) (hq : IsTopologicallyNilpotent (q:R)) :
    quintupleProduct q 5 = euler144 q *
      (unary q 108 21-(q:R)^5*unary q 108 51) := by
  have h := quintupleProduct_eq q hq 5
  norm_num only [Int.reduceMul,Int.reduceSub,Int.reduceAdd] at h
  rw [unary_neg] at h
  simpa only [zpow_ofNat,Units.val_pow_eq_pow_val] using h

theorem quintupleProduct_3 (q : Rˣ) (hq : IsTopologicallyNilpotent (q:R)) :
    quintupleProduct q 3 = euler144 q *
      (unary q 108 27-(q:R)^3*unary q 108 45) := by
  have h := quintupleProduct_eq q hq 3
  norm_num only [Int.reduceMul,Int.reduceSub,Int.reduceAdd] at h
  rw [unary_neg] at h
  simpa only [zpow_ofNat,Units.val_pow_eq_pow_val] using h

theorem quintupleProduct_25 (q : Rˣ) (hq : IsTopologicallyNilpotent (q:R)) :
    quintupleProduct q 25 = euler144 q *
      (unary q 108 39-(q:R)^22*unary q 108 105) := by
  have h := quintupleProduct_eq q hq 25
  norm_num only [Int.reduceMul,Int.reduceSub,Int.reduceAdd] at h
  have hs : ((q^25:Rˣ):R)*unary q 108 111=
      ((q^22:Rˣ):R)*unary q 108 105 := by
    have ht := scaled_unary_shift q hq 25 (-105)
    norm_num only [Int.reduceAdd,Int.reduceSub] at ht
    rw [unary_neg] at ht
    exact ht
  simp only [zpow_ofNat,Units.val_pow_eq_pow_val] at h hs
  rw [hs] at h
  exact h

theorem quintupleProduct_31 (q : Rˣ) (hq : IsTopologicallyNilpotent (q:R)) :
    quintupleProduct q 31 = euler144 q *
      (unary q 108 57-(q:R)^10*unary q 108 87) := by
  have h := quintupleProduct_eq q hq 31
  norm_num only [Int.reduceMul,Int.reduceSub,Int.reduceAdd] at h
  have hs : ((q^31:Rˣ):R)*unary q 108 129=
      ((q^10:Rˣ):R)*unary q 108 87 := by
    have ht := scaled_unary_shift q hq 31 (-87)
    norm_num only [Int.reduceAdd,Int.reduceSub] at ht
    rw [unary_neg] at ht
    exact ht
  simp only [zpow_ofNat,Units.val_pow_eq_pow_val] at h hs
  rw [hs] at h
  exact h

theorem quintupleProduct_33 (q : Rˣ) (hq : IsTopologicallyNilpotent (q:R)) :
    quintupleProduct q 33 = euler144 q *
      (unary q 108 63-(q:R)^6*unary q 108 81) := by
  have h := quintupleProduct_eq q hq 33
  norm_num only [Int.reduceMul,Int.reduceSub,Int.reduceAdd] at h
  have hs : ((q^33:Rˣ):R)*unary q 108 135=
      ((q^6:Rˣ):R)*unary q 108 81 := by
    have ht := scaled_unary_shift q hq 33 (-81)
    norm_num only [Int.reduceAdd,Int.reduceSub] at ht
    rw [unary_neg] at ht
    exact ht
  simp only [zpow_ofNat,Units.val_pow_eq_pow_val] at h hs
  rw [hs] at h
  exact h

/-- The first numerator's finite theta expression after six exact quintuple substitutions. -/
theorem unaryMask221_quintuple (q : Rˣ) (hq : IsTopologicallyNilpotent (q:R)) :
    euler144 q * unaryMask221 q =
      (unary q 36 1-(q:R)^2*unary q 36 17)*
        (quintupleProduct q 11-(q:R)*quintupleProduct q 5)-
      (q:R)^2*(unary q 36 7-(q:R)^4*unary q 36 25)*quintupleProduct q 3+
      (q:R)^6*(unary q 36 19-(q:R)^6*unary q 36 35)*
        (quintupleProduct q 25-(q:R)^4*quintupleProduct q 31)-
      (q:R)^10*(unary q 36 11-(q:R)^5*unary q 36 29)*quintupleProduct q 33 := by
  rw [unaryMask221_compressed q hq,quintupleProduct_11 q hq,
    quintupleProduct_5 q hq,quintupleProduct_3 q hq,quintupleProduct_25 q hq,
    quintupleProduct_31 q hq,quintupleProduct_33 q hq]
  ring

end KanadeRussell.Representation.LevelNineQuintupleFactors
