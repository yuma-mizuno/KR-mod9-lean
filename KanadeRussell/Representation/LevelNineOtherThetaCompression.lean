import KanadeRussell.Representation.LevelNineThetaCompression
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KanadeRussell.Representation.LevelNineOtherThetaCompression
open Infra.ThetaAddition LevelNineNumeratorMasks LevelNineThetaCompression
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]
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

noncomputable def cosetUnary411 (q : Rˣ) (a b : ℤ) : R :=
  let A := 8*a-4*b+9-4*4
  let B := 8*b-4*a+9-4*1
  let C := a+b+4*((a*a+b*b-a*b-4*a-1*b)/9)
  pairedTerm q C A (A+2*B)+pairedTerm q (C+A+B+36) (A+36) (A+2*B+108)
noncomputable def unaryMask411 (q : Rˣ) : R :=
  ((positiveResidues 1).map (fun ab => cosetUnary411 q ab.1 ab.2)).sum-
    ((negativeResidues 1).map (fun ab => cosetUnary411 q ab.1 ab.2)).sum

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem cert411_hc0 (q : Rˣ) : pairedTerm q 0 (-7) 3 = pairedTerm q 0 7 3 := by
  calc
    _ = pairedTerm q 0 7 3 := paired_neg_first q 0 7 3

private theorem cert411_hc1 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 34 29 111 = pairedTerm q 31 29 105 := by
  calc
    _ = pairedTerm q 31 29 (-105) := by convert paired_shift_second q hq 34 29 (-105) using 1 <;> norm_num
    _ = pairedTerm q 31 29 105 := paired_neg_second q 31 29 105

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem cert411_hc2 (q : Rˣ) : pairedTerm q 18 (-11) 87 = pairedTerm q 18 11 87 := by
  calc
    _ = pairedTerm q 18 11 87 := paired_neg_first q 18 11 87

private theorem cert411_hc3 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 92 25 195 = pairedTerm q 5 25 21 := by
  calc
    _ = pairedTerm q 5 25 (-21) := by convert paired_shift_second q hq 92 25 (-21) using 1 <;> norm_num
    _ = pairedTerm q 5 25 21 := paired_neg_second q 5 25 21

private theorem cert411_hc5 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 79 41 171 = pairedTerm q 11 31 45 := by
  calc
    _ = pairedTerm q 74 (-31) 171 := by convert paired_shift_first q hq 79 (-31) 171 using 1 <;> norm_num
    _ = pairedTerm q 74 31 171 := paired_neg_first q 74 31 171
    _ = pairedTerm q 11 31 (-45) := by convert paired_shift_second q hq 74 31 (-45) using 1 <;> norm_num
    _ = pairedTerm q 11 31 45 := paired_neg_second q 11 31 45

private theorem cert411_hc7 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 64 65 123 = pairedTerm q 20 7 93 := by
  calc
    _ = pairedTerm q 35 (-7) 123 := by convert paired_shift_first q hq 64 (-7) 123 using 1 <;> norm_num
    _ = pairedTerm q 35 7 123 := paired_neg_first q 35 7 123
    _ = pairedTerm q 20 7 (-93) := by convert paired_shift_second q hq 35 7 (-93) using 1 <;> norm_num
    _ = pairedTerm q 20 7 93 := paired_neg_second q 20 7 93

private theorem cert411_hc9 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 103 61 183 = pairedTerm q 3 11 33 := by
  calc
    _ = pairedTerm q 78 (-11) 183 := by convert paired_shift_first q hq 103 (-11) 183 using 1 <;> norm_num
    _ = pairedTerm q 78 11 183 := paired_neg_first q 78 11 183
    _ = pairedTerm q 3 11 (-33) := by convert paired_shift_second q hq 78 11 (-33) using 1 <;> norm_num
    _ = pairedTerm q 3 11 33 := paired_neg_second q 3 11 33

private theorem cert411_hc10 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 18 49 27 = pairedTerm q 5 23 27 := by
  calc
    _ = pairedTerm q 5 (-23) 27 := by convert paired_shift_first q hq 18 (-23) 27 using 1 <;> norm_num
    _ = pairedTerm q 5 23 27 := paired_neg_first q 5 23 27

private theorem cert411_hc11 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 92 85 135 = pairedTerm q 16 13 81 := by
  calc
    _ = pairedTerm q 43 13 135 := by convert paired_shift_first q hq 92 13 135 using 1 <;> norm_num
    _ = pairedTerm q 16 13 (-81) := by convert paired_shift_second q hq 43 13 (-81) using 1 <;> norm_num
    _ = pairedTerm q 16 13 81 := paired_neg_second q 16 13 81

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem cert411_hc12 (q : Rˣ) : pairedTerm q 1 (-11) 15 = pairedTerm q 1 11 15 := by
  calc
    _ = pairedTerm q 1 11 15 := paired_neg_first q 1 11 15

private theorem cert411_hc13 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 39 25 123 = pairedTerm q 24 25 93 := by
  calc
    _ = pairedTerm q 24 25 (-93) := by convert paired_shift_second q hq 39 25 (-93) using 1 <;> norm_num
    _ = pairedTerm q 24 25 93 := paired_neg_second q 24 25 93

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem cert411_hc14 (q : Rˣ) : pairedTerm q 13 (-7) 75 = pairedTerm q 13 7 75 := by
  calc
    _ = pairedTerm q 13 7 75 := paired_neg_first q 13 7 75

private theorem cert411_hc15 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 83 29 183 = pairedTerm q 8 29 33 := by
  calc
    _ = pairedTerm q 8 29 (-33) := by convert paired_shift_second q hq 83 29 (-33) using 1 <;> norm_num
    _ = pairedTerm q 8 29 33 := paired_neg_second q 8 29 33

private theorem cert411_hc17 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 54 61 111 = pairedTerm q 26 11 105 := by
  calc
    _ = pairedTerm q 29 (-11) 111 := by convert paired_shift_first q hq 54 (-11) 111 using 1 <;> norm_num
    _ = pairedTerm q 29 11 111 := paired_neg_first q 29 11 111
    _ = pairedTerm q 26 11 (-105) := by convert paired_shift_second q hq 29 11 (-105) using 1 <;> norm_num
    _ = pairedTerm q 26 11 105 := paired_neg_second q 26 11 105

private theorem cert411_hc19 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 84 49 171 = pairedTerm q 8 23 45 := by
  calc
    _ = pairedTerm q 71 (-23) 171 := by convert paired_shift_first q hq 84 (-23) 171 using 1 <;> norm_num
    _ = pairedTerm q 71 23 171 := paired_neg_first q 71 23 171
    _ = pairedTerm q 8 23 (-45) := by convert paired_shift_second q hq 71 23 (-45) using 1 <;> norm_num
    _ = pairedTerm q 8 23 45 := paired_neg_second q 8 23 45

private theorem cert411_hc20 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 13 41 27 = pairedTerm q 8 31 27 := by
  calc
    _ = pairedTerm q 8 (-31) 27 := by convert paired_shift_first q hq 13 (-31) 27 using 1 <;> norm_num
    _ = pairedTerm q 8 31 27 := paired_neg_first q 8 31 27

private theorem cert411_hc21 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 83 77 135 = pairedTerm q 15 5 81 := by
  calc
    _ = pairedTerm q 42 5 135 := by convert paired_shift_first q hq 83 5 135 using 1 <;> norm_num
    _ = pairedTerm q 15 5 (-81) := by convert paired_shift_second q hq 42 5 (-81) using 1 <;> norm_num
    _ = pairedTerm q 15 5 81 := paired_neg_second q 15 5 81

private theorem cert411_hc23 (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) : pairedTerm q 117 65 195 = pairedTerm q 1 7 21 := by
  calc
    _ = pairedTerm q 88 (-7) 195 := by convert paired_shift_first q hq 117 (-7) 195 using 1 <;> norm_num
    _ = pairedTerm q 88 7 195 := paired_neg_first q 88 7 195
    _ = pairedTerm q 1 7 (-21) := by convert paired_shift_second q hq 88 7 (-21) using 1 <;> norm_num
    _ = pairedTerm q 1 7 21 := paired_neg_second q 1 7 21

/-- Exact four-term compression for the (4,1,1) residue mask. -/
theorem unaryMask411_compressed (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) :
    unaryMask411 q =
      1*(unary q 36 7-(q : R)^4*unary q 36 25)*(unary q 108 3 - (q : R)*unary q 108 21 - (q : R)^13*unary q 108 75 + (q : R)^20*unary q 108 93) +
      (q : R)*(unary q 36 11-(q : R)^5*unary q 36 29)*( - unary q 108 15 + (q : R)^2*unary q 108 33 + (q : R)^17*unary q 108 87 - (q : R)^25*unary q 108 105) +
      (q : R)^9*(unary q 36 5-(q : R)*unary q 36 13)*(unary q 108 63 - (q : R)^6*unary q 108 81) +
      (q : R)^5*(unary q 36 23-(q : R)^3*unary q 36 31)*(unary q 108 27 - (q : R)^3*unary q 108 45) := by
  simp only [unaryMask411, positiveResidues, negativeResidues, Matrix.cons_val_one, Matrix.cons_val_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [cosetUnary411]
  rw [cert411_hc0 q, cert411_hc1 q hq, cert411_hc2 q, cert411_hc3 q hq, cert411_hc5 q hq, cert411_hc7 q hq, cert411_hc9 q hq, cert411_hc10 q hq, cert411_hc11 q hq, cert411_hc12 q, cert411_hc13 q hq, cert411_hc14 q, cert411_hc15 q hq, cert411_hc17 q hq, cert411_hc19 q hq, cert411_hc20 q hq, cert411_hc21 q hq, cert411_hc23 q hq]
  simp only [pairedTerm, zpow_ofNat, Units.val_pow_eq_pow_val]
  ring

noncomputable def cosetUnary112 (q : Rˣ) (a b : ℤ) : R :=
  let A := 8*a-4*b+9-4*1
  let B := 8*b-4*a+9-4*1
  let C := a+b+4*((a*a+b*b-a*b-1*a-1*b)/9)
  pairedTerm q C A (A+2*B)+pairedTerm q (C+A+B+36) (A+36) (A+2*B+108)
noncomputable def unaryMask112 (q : Rˣ) : R :=
  ((positiveResidues 2).map (fun ab => cosetUnary112 q ab.1 ab.2)).sum-
    ((negativeResidues 2).map (fun ab => cosetUnary112 q ab.1 ab.2)).sum

/-- Exact four-term compression for the (1,1,2) residue mask. -/
theorem unaryMask112_compressed (q : Rˣ) (hq : IsTopologicallyNilpotent (q : R)) :
    unaryMask112 q =
      1*(unary q 36 5-(q : R)*unary q 36 13)*(unary q 108 15 - (q : R)^2*unary q 108 33 + (q : R)^3*unary q 108 39 - (q : R)^7*unary q 108 57) +
      (q : R)*(unary q 36 1-(q : R)^2*unary q 36 17)*( - unary q 108 27 + (q : R)^3*unary q 108 45) +
      (q : R)^11*(unary q 36 19-(q : R)^6*unary q 36 35)*( - unary q 108 63 + (q : R)^6*unary q 108 81) +
      (q : R)^9*(unary q 36 23-(q : R)^3*unary q 36 31)*(unary q 108 51 - (q : R)^5*unary q 108 69 + (q : R)^7*unary q 108 75 - (q : R)^14*unary q 108 93) := by
  have hc1 : pairedTerm q 46 41 123 = pairedTerm q 26 31 93 := by
    calc
      _ = pairedTerm q 41 (-31) 123 := by convert paired_shift_first q hq 46 (-31) 123 using 1 <;> norm_num
      _ = pairedTerm q 41 31 123 := paired_neg_first q 41 31 123
      _ = pairedTerm q 26 31 (-93) := by convert paired_shift_second q hq 41 31 (-93) using 1 <;> norm_num
      _ = pairedTerm q 26 31 93 := paired_neg_second q 26 31 93
  have hc3 : pairedTerm q 61 41 147 = pairedTerm q 17 31 69 := by
    calc
      _ = pairedTerm q 56 (-31) 147 := by convert paired_shift_first q hq 61 (-31) 147 using 1 <;> norm_num
      _ = pairedTerm q 56 31 147 := paired_neg_first q 56 31 147
      _ = pairedTerm q 17 31 (-69) := by convert paired_shift_second q hq 56 31 (-69) using 1 <;> norm_num
      _ = pairedTerm q 17 31 69 := paired_neg_second q 17 31 69
  have hc5 : pairedTerm q 61 53 135 = pairedTerm q 17 19 81 := by
    calc
      _ = pairedTerm q 44 (-19) 135 := by convert paired_shift_first q hq 61 (-19) 135 using 1 <;> norm_num
      _ = pairedTerm q 44 19 135 := paired_neg_first q 44 19 135
      _ = pairedTerm q 17 19 (-81) := by convert paired_shift_second q hq 44 19 (-81) using 1 <;> norm_num
      _ = pairedTerm q 17 19 81 := paired_neg_second q 17 19 81
  have hc6 : pairedTerm q 18 37 63 = pairedTerm q 17 35 63 := by
    calc
      _ = pairedTerm q 17 (-35) 63 := by convert paired_shift_first q hq 18 (-35) 63 using 1 <;> norm_num
      _ = pairedTerm q 17 35 63 := paired_neg_first q 17 35 63
  have hc7 : pairedTerm q 104 73 171 = pairedTerm q 4 1 45 := by
    calc
      _ = pairedTerm q 67 1 171 := by convert paired_shift_first q hq 104 1 171 using 1 <;> norm_num
      _ = pairedTerm q 4 1 (-45) := by convert paired_shift_second q hq 67 1 (-45) using 1 <;> norm_num
      _ = pairedTerm q 4 1 45 := paired_neg_second q 4 1 45
  have hc8 : pairedTerm q 22 49 51 = pairedTerm q 9 23 51 := by
    calc
      _ = pairedTerm q 9 (-23) 51 := by convert paired_shift_first q hq 22 (-23) 51 using 1 <;> norm_num
      _ = pairedTerm q 9 23 51 := paired_neg_first q 9 23 51
  have hc9 : pairedTerm q 108 85 159 = pairedTerm q 8 13 57 := by
    calc
      _ = pairedTerm q 59 13 159 := by convert paired_shift_first q hq 108 13 159 using 1 <;> norm_num
      _ = pairedTerm q 8 13 (-57) := by convert paired_shift_second q hq 59 13 (-57) using 1 <;> norm_num
      _ = pairedTerm q 8 13 57 := paired_neg_second q 8 13 57
  have hc10 : pairedTerm q 29 49 75 = pairedTerm q 16 23 75 := by
    calc
      _ = pairedTerm q 16 (-23) 75 := by convert paired_shift_first q hq 29 (-23) 75 using 1 <;> norm_num
      _ = pairedTerm q 16 23 75 := paired_neg_first q 16 23 75
  have hc11 : pairedTerm q 127 85 183 = pairedTerm q 3 13 33 := by
    calc
      _ = pairedTerm q 78 13 183 := by convert paired_shift_first q hq 127 13 183 using 1 <;> norm_num
      _ = pairedTerm q 3 13 (-33) := by convert paired_shift_second q hq 78 13 (-33) using 1 <;> norm_num
      _ = pairedTerm q 3 13 33 := paired_neg_second q 3 13 33
  have hc13 : pairedTerm q 51 37 135 = pairedTerm q 23 35 81 := by
    calc
      _ = pairedTerm q 50 (-35) 135 := by convert paired_shift_first q hq 51 (-35) 135 using 1 <;> norm_num
      _ = pairedTerm q 50 35 135 := paired_neg_first q 50 35 135
      _ = pairedTerm q 23 35 (-81) := by convert paired_shift_second q hq 50 35 (-81) using 1 <;> norm_num
      _ = pairedTerm q 23 35 81 := paired_neg_second q 23 35 81
  have hc15 : pairedTerm q 51 49 123 = pairedTerm q 23 23 93 := by
    calc
      _ = pairedTerm q 38 (-23) 123 := by convert paired_shift_first q hq 51 (-23) 123 using 1 <;> norm_num
      _ = pairedTerm q 38 23 123 := paired_neg_first q 38 23 123
      _ = pairedTerm q 23 23 (-93) := by convert paired_shift_second q hq 38 23 (-93) using 1 <;> norm_num
      _ = pairedTerm q 23 23 93 := paired_neg_second q 23 23 93
  have hc17 : pairedTerm q 66 49 147 = pairedTerm q 14 23 69 := by
    calc
      _ = pairedTerm q 53 (-23) 147 := by convert paired_shift_first q hq 66 (-23) 147 using 1 <;> norm_num
      _ = pairedTerm q 53 23 147 := paired_neg_first q 53 23 147
      _ = pairedTerm q 14 23 (-69) := by convert paired_shift_second q hq 53 23 (-69) using 1 <;> norm_num
      _ = pairedTerm q 14 23 69 := paired_neg_second q 14 23 69
  have hc18 : pairedTerm q 17 41 51 = pairedTerm q 12 31 51 := by
    calc
      _ = pairedTerm q 12 (-31) 51 := by convert paired_shift_first q hq 17 (-31) 51 using 1 <;> norm_num
      _ = pairedTerm q 12 31 51 := paired_neg_first q 12 31 51
  have hc19 : pairedTerm q 99 77 159 = pairedTerm q 7 5 57 := by
    calc
      _ = pairedTerm q 58 5 159 := by convert paired_shift_first q hq 99 5 159 using 1 <;> norm_num
      _ = pairedTerm q 7 5 (-57) := by convert paired_shift_second q hq 58 5 (-57) using 1 <;> norm_num
      _ = pairedTerm q 7 5 57 := paired_neg_second q 7 5 57
  have hc20 : pairedTerm q 24 41 75 = pairedTerm q 19 31 75 := by
    calc
      _ = pairedTerm q 19 (-31) 75 := by convert paired_shift_first q hq 24 (-31) 75 using 1 <;> norm_num
      _ = pairedTerm q 19 31 75 := paired_neg_first q 19 31 75
  have hc21 : pairedTerm q 118 77 183 = pairedTerm q 2 5 33 := by
    calc
      _ = pairedTerm q 77 5 183 := by convert paired_shift_first q hq 118 5 183 using 1 <;> norm_num
      _ = pairedTerm q 2 5 (-33) := by convert paired_shift_second q hq 77 5 (-33) using 1 <;> norm_num
      _ = pairedTerm q 2 5 33 := paired_neg_second q 2 5 33
  have hc22 : pairedTerm q 28 53 63 = pairedTerm q 11 19 63 := by
    calc
      _ = pairedTerm q 11 (-19) 63 := by convert paired_shift_first q hq 28 (-19) 63 using 1 <;> norm_num
      _ = pairedTerm q 11 19 63 := paired_neg_first q 11 19 63
  have hc23 : pairedTerm q 122 89 171 = pairedTerm q 6 17 45 := by
    calc
      _ = pairedTerm q 69 17 171 := by convert paired_shift_first q hq 122 17 171 using 1 <;> norm_num
      _ = pairedTerm q 6 17 (-45) := by convert paired_shift_second q hq 69 17 (-45) using 1 <;> norm_num
      _ = pairedTerm q 6 17 45 := paired_neg_second q 6 17 45
  simp only [unaryMask112, positiveResidues, negativeResidues, Matrix.cons_val_two]
  norm_num [cosetUnary112]
  rw [hc1, hc3, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc13, hc15, hc17, hc18, hc19, hc20, hc21, hc22, hc23]
  simp only [pairedTerm, zpow_ofNat, Units.val_pow_eq_pow_val]
  ring

end KanadeRussell.Representation.LevelNineOtherThetaCompression
