import KanadeRussell.Infra.WeierstrassAddition
import KanadeRussell.Representation.LevelNineNumeratorMasks

/-! Exact theta-shift reduction of the first level-nine mask's 24 unary
products. This proves the finite compression only, not its final Euler/Jacobi
product evaluation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KanadeRussell.Representation.LevelNineThetaCompression
open Infra.ThetaAddition LevelNineNumeratorMasks
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def unary (q : Rˣ) (d : ℕ) (a : ℤ) : R := theta (q^d) (q^a)

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem unary_neg (q : Rˣ) (d : ℕ) (a : ℤ) : unary q d (-a)=unary q d a := by
  simp only [unary, zpow_neg, theta_inv]

private theorem unary_shift (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R))
    (d : ℕ) (hd : d ≠ 0) (a : ℤ) :
    unary q d (a+2*d) = ((q^(-(d : ℤ)-a) : Rˣ) : R)*unary q d a := by
  have hp : IsTopologicallyNilpotent ((q^d : Rˣ) : R) := by
    simpa only [Units.val_pow_eq_pow_val] using hq.pow hd
  have he : (q^d)^2*q^a=q^(a+2*(d : ℤ)) := by
    simp only [← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    ring
  have hc : (q^d)⁻¹*(q^a)⁻¹=q^(-(d : ℤ)-a) := by
    simp only [← zpow_natCast, ← zpow_neg, ← zpow_add]
    congr 1
  simpa only [unary, he, hc] using theta_shift (q^d) (q^a) hp

noncomputable def pairedTerm (q : Rˣ) (c a b : ℤ) : R :=
  ((q^c : Rˣ) : R)*unary q 36 a*unary q 108 b

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem paired_neg_first (q : Rˣ) (c a b : ℤ) :
    pairedTerm q c (-a) b=pairedTerm q c a b := by rw [pairedTerm, unary_neg]; rfl

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem paired_neg_second (q : Rˣ) (c a b : ℤ) :
    pairedTerm q c a (-b)=pairedTerm q c a b := by rw [pairedTerm, unary_neg]; rfl

private theorem paired_shift_first (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R))
    (c a b : ℤ) : pairedTerm q c (a+72) b=pairedTerm q (c-36-a) a b := by
  unfold pairedTerm
  rw [show a+72=a+2*(36 : ℕ) by norm_num, unary_shift q hq 36 (by decide)]
  have hc : ((q^c : Rˣ) : R)*((q^(-36-a) : Rˣ) : R)=((q^(c-36-a) : Rˣ) : R) := by
    rw [← Units.val_mul, ← zpow_add]
    congr 2
    ring
  calc
    _ = (((q^c : Rˣ) : R)*((q^(-36-a) : Rˣ) : R))*unary q 36 a*unary q 108 b := by ac_rfl
    _ = _ := by rw [hc]

private theorem paired_shift_second (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R))
    (c a b : ℤ) : pairedTerm q c a (b+216)=pairedTerm q (c-108-b) a b := by
  unfold pairedTerm
  rw [show b+216=b+2*(108 : ℕ) by norm_num, unary_shift q hq 108 (by decide)]
  have hc : ((q^c : Rˣ) : R)*((q^(-108-b) : Rˣ) : R)=((q^(c-108-b) : Rˣ) : R) := by
    rw [← Units.val_mul, ← zpow_add]
    congr 2
    ring
  calc
    _ = (((q^c : Rˣ) : R)*((q^(-108-b) : Rˣ) : R))*unary q 36 a*unary q 108 b := by ac_rfl
    _ = _ := by rw [hc]

/-- The two parity products for the residue `(a,b)` in the `(2,2,1)` case. -/
noncomputable def cosetUnary221 (q : Rˣ) (a b : ℤ) : R :=
  let A := 8*a-4*b+1
  let B := 8*b-4*a+1
  let C := a+b+4*((a*a+b*b-a*b-2*a-2*b)/9)
  pairedTerm q C A (A+2*B)+pairedTerm q (C+A+B+36) (A+36) (A+2*B+108)

noncomputable def unaryMask221 (q : Rˣ) : R :=
  ((positiveResidues 0).map (fun ab => cosetUnary221 q ab.1 ab.2)).sum-
    ((negativeResidues 0).map (fun ab => cosetUnary221 q ab.1 ab.2)).sum

/-- The full 24-term first numerator compression, proved by exact theta shifts. -/
theorem unaryMask221_compressed (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) :
    unaryMask221 q =
      (unary q 36 1-(q : R)^2*unary q 36 17)*
        (unary q 108 3-(q : R)*unary q 108 21+(q : R)^6*unary q 108 51-(q : R)^11*unary q 108 69)-
      (q : R)^2*(unary q 36 7-(q : R)^4*unary q 36 25)*
        (unary q 108 27-(q : R)^3*unary q 108 45)+
      (q : R)^6*(unary q 36 19-(q : R)^6*unary q 36 35)*
        (unary q 108 39-(q : R)^4*unary q 108 57+(q : R)^14*unary q 108 87-(q : R)^22*unary q 108 105)-
      (q : R)^10*(unary q 36 11-(q : R)^5*unary q 36 29)*
        (unary q 108 63-(q : R)^6*unary q 108 81) := by
  have h0 : pairedTerm q 0 1 3 = pairedTerm q 0 1 3 := by
    rfl
  have h1 : pairedTerm q 38 37 111 = pairedTerm q 34 35 105 := by
    calc
      _ = pairedTerm q 37 (-35) 111 := by convert paired_shift_first q hq 38 (-35) 111 using 1 <;> norm_num
      _ = pairedTerm q 37 35 111 := paired_neg_first q 37 35 111
      _ = pairedTerm q 34 35 (-105) := by convert paired_shift_second q hq 37 35 (-105) using 1 <;> norm_num
      _ = pairedTerm q 34 35 105 := paired_neg_second q 34 35 105
  have h2 : pairedTerm q 20 (-19) 87 = pairedTerm q 20 19 87 := by
    exact paired_neg_first q 20 19 87
  have h3 : pairedTerm q 90 17 195 = pairedTerm q 3 17 21 := by
    calc
      _ = pairedTerm q 3 17 (-21) := by convert paired_shift_second q hq 90 17 (-21) using 1 <;> norm_num
      _ = pairedTerm q 3 17 21 := paired_neg_second q 3 17 21
  have h4 : pairedTerm q 6 1 51 = pairedTerm q 6 1 51 := by
    rfl
  have h5 : pairedTerm q 68 37 159 = pairedTerm q 16 35 57 := by
    calc
      _ = pairedTerm q 67 (-35) 159 := by convert paired_shift_first q hq 68 (-35) 159 using 1 <;> norm_num
      _ = pairedTerm q 67 35 159 := paired_neg_first q 67 35 159
      _ = pairedTerm q 16 35 (-57) := by convert paired_shift_second q hq 67 35 (-57) using 1 <;> norm_num
      _ = pairedTerm q 16 35 57 := paired_neg_second q 16 35 57
  have h6 : pairedTerm q 6 25 27 = pairedTerm q 6 25 27 := by
    rfl
  have h7 : pairedTerm q 68 61 135 = pairedTerm q 16 11 81 := by
    calc
      _ = pairedTerm q 43 (-11) 135 := by convert paired_shift_first q hq 68 (-11) 135 using 1 <;> norm_num
      _ = pairedTerm q 43 11 135 := paired_neg_first q 43 11 135
      _ = pairedTerm q 16 11 (-81) := by convert paired_shift_second q hq 43 11 (-81) using 1 <;> norm_num
      _ = pairedTerm q 16 11 81 := paired_neg_second q 16 11 81
  have h8 : pairedTerm q 15 29 63 = pairedTerm q 15 29 63 := by
    rfl
  have h9 : pairedTerm q 97 65 171 = pairedTerm q 5 7 45 := by
    calc
      _ = pairedTerm q 68 (-7) 171 := by convert paired_shift_first q hq 97 (-7) 171 using 1 <;> norm_num
      _ = pairedTerm q 68 7 171 := paired_neg_first q 68 7 171
      _ = pairedTerm q 5 7 (-45) := by convert paired_shift_second q hq 68 7 (-45) using 1 <;> norm_num
      _ = pairedTerm q 5 7 45 := paired_neg_second q 5 7 45
  have h10 : pairedTerm q 23 53 39 = pairedTerm q 6 19 39 := by
    calc
      _ = pairedTerm q 6 (-19) 39 := by convert paired_shift_first q hq 23 (-19) 39 using 1 <;> norm_num
      _ = pairedTerm q 6 19 39 := paired_neg_first q 6 19 39
  have h11 : pairedTerm q 105 89 147 = pairedTerm q 13 17 69 := by
    calc
      _ = pairedTerm q 52 17 147 := by convert paired_shift_first q hq 105 17 147 using 1 <;> norm_num
      _ = pairedTerm q 13 17 (-69) := by convert paired_shift_second q hq 52 17 (-69) using 1 <;> norm_num
      _ = pairedTerm q 13 17 69 := paired_neg_second q 13 17 69
  have h12 : pairedTerm q 2 (-7) 27 = pairedTerm q 2 7 27 := by
    exact paired_neg_first q 2 7 27
  have h13 : pairedTerm q 48 29 135 = pairedTerm q 21 29 81 := by
    calc
      _ = pairedTerm q 21 29 (-81) := by convert paired_shift_second q hq 48 29 (-81) using 1 <;> norm_num
      _ = pairedTerm q 21 29 81 := paired_neg_second q 21 29 81
  have h14 : pairedTerm q 10 (-11) 63 = pairedTerm q 10 11 63 := by
    exact paired_neg_first q 10 11 63
  have h15 : pairedTerm q 72 25 171 = pairedTerm q 9 25 45 := by
    calc
      _ = pairedTerm q 9 25 (-45) := by convert paired_shift_second q hq 72 25 (-45) using 1 <;> norm_num
      _ = pairedTerm q 9 25 45 := paired_neg_second q 9 25 45
  have h16 : pairedTerm q 2 17 3 = pairedTerm q 2 17 3 := by
    rfl
  have h17 : pairedTerm q 48 53 111 = pairedTerm q 28 19 105 := by
    calc
      _ = pairedTerm q 31 (-19) 111 := by convert paired_shift_first q hq 48 (-19) 111 using 1 <;> norm_num
      _ = pairedTerm q 31 19 111 := paired_neg_first q 31 19 111
      _ = pairedTerm q 28 19 (-105) := by convert paired_shift_second q hq 31 19 (-105) using 1 <;> norm_num
      _ = pairedTerm q 28 19 105 := paired_neg_second q 28 19 105
  have h18 : pairedTerm q 8 17 51 = pairedTerm q 8 17 51 := by
    rfl
  have h19 : pairedTerm q 78 53 159 = pairedTerm q 10 19 57 := by
    calc
      _ = pairedTerm q 61 (-19) 159 := by convert paired_shift_first q hq 78 (-19) 159 using 1 <;> norm_num
      _ = pairedTerm q 61 19 159 := paired_neg_first q 61 19 159
      _ = pairedTerm q 10 19 (-57) := by convert paired_shift_second q hq 61 19 (-57) using 1 <;> norm_num
      _ = pairedTerm q 10 19 57 := paired_neg_second q 10 19 57
  have h20 : pairedTerm q 13 37 39 = pairedTerm q 12 35 39 := by
    calc
      _ = pairedTerm q 12 (-35) 39 := by convert paired_shift_first q hq 13 (-35) 39 using 1 <;> norm_num
      _ = pairedTerm q 12 35 39 := paired_neg_first q 12 35 39
  have h21 : pairedTerm q 87 73 147 = pairedTerm q 11 1 69 := by
    calc
      _ = pairedTerm q 50 1 147 := by convert paired_shift_first q hq 87 1 147 using 1 <;> norm_num
      _ = pairedTerm q 11 1 (-69) := by convert paired_shift_second q hq 50 1 (-69) using 1 <;> norm_num
      _ = pairedTerm q 11 1 69 := paired_neg_second q 11 1 69
  have h22 : pairedTerm q 27 37 87 = pairedTerm q 26 35 87 := by
    calc
      _ = pairedTerm q 26 (-35) 87 := by convert paired_shift_first q hq 27 (-35) 87 using 1 <;> norm_num
      _ = pairedTerm q 26 35 87 := paired_neg_first q 26 35 87
  have h23 : pairedTerm q 125 73 195 = pairedTerm q 1 1 21 := by
    calc
      _ = pairedTerm q 88 1 195 := by convert paired_shift_first q hq 125 1 195 using 1 <;> norm_num
      _ = pairedTerm q 1 1 (-21) := by convert paired_shift_second q hq 88 1 (-21) using 1 <;> norm_num
      _ = pairedTerm q 1 1 21 := paired_neg_second q 1 1 21
  norm_num [unaryMask221, positiveResidues, negativeResidues, cosetUnary221]
  rw [h1, h2, h3, h5, h7, h9, h10, h11, h12, h13, h14, h15, h17, h19, h20, h21, h22, h23]
  simp only [pairedTerm, zpow_ofNat, Units.val_pow_eq_pow_val]
  ring

end KanadeRussell.Representation.LevelNineThetaCompression
