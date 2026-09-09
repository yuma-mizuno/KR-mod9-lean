import KanadeRussell.Infra.A2CoefficientResidues
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped QTheory
namespace KanadeRussell.Infra.A2ConvolutionConstant
open ThetaAddition A2JacobiCoefficients A2CoefficientResidues
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem nilpotent_pow (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (d : ℕ) (hd : d≠0) : IsTopologicallyNilpotent ((p^d:Rˣ):R) := by
  simpa only [Units.val_pow_eq_pow_val] using hp.pow hd

/-- This linear transformation always has index sum divisible by three. -/
theorem coefficient_transformed (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n : ℤ) :
    coefficient p (-2*m+n) (-m-n)=
      euler p*(↑(p^(2*(m^2+n^2-m*n)+2*m)):R) := by
  have hc := coefficient_residue p hp (-2*m+n) (-m-n) (-m) 0 (by norm_num; ring)
  have he : residueExponent (-2*m+n) (-m-n) (-m) 0=2*(m^2+n^2-m*n)+2*m := by
    unfold residueExponent
    ring
  simp only [show (0:Fin 3)≠2 by decide,ite_false,Fin.val_zero,Nat.cast_zero,
    zpow_zero,one_mul] at hc
  rw [he] at hc
  exact hc.trans (mul_comm _ _)

/-- An exact termwise bridge to the actual A2 expansion at the fourth power of the base. -/
theorem convolution_term (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (m n : ℤ) :
    euler (p^4)*(coefficient p (-2*m+n) (-m-n)*coefficient p m n)=
      euler p^2*(coefficient (p^4) m n*(↑(p^(4*m)*p^(2*n)):R)) := by
  let k : ℤ := (m+n)/3
  let r : Fin 3 := ⟨((m+n)%3).toNat,by omega⟩
  have h : m+n=3*k+(r:ℤ) := by dsimp [k,r]; omega
  have hc := coefficient_residue p hp m n k r h
  have hc4 := coefficient_residue (p^4) (nilpotent_pow p hp 4 (by decide)) m n k r h
  by_cases hr : r=2
  · simp only [hr,ite_true] at hc hc4
    rw [hc,hc4]
    ring
  · rw [if_neg hr] at hc hc4
    have hf := residueExponent_identity m n k r h hr
    have he : p^(2*(m^2+n^2-m*n)+2*m)*p^(residueExponent m n k r)=
        (p^4)^(residueExponent m n k r)*(p^(4*m)*p^(2*n)) := by
      simp only [← zpow_natCast,← zpow_mul,← zpow_add]
      congr 1
      norm_num only [Nat.cast_ofNat]
      nlinarith [hf]
    rw [coefficient_transformed p hp,hc,hc4]
    calc
      _ = euler (p^4)*euler p^2*(↑((-1:Rˣ)^(r:ℤ)):R)*
          (↑(p^(2*(m^2+n^2-m*n)+2*m)*p^(residueExponent m n k r)):R) := by
            simp only [Units.val_mul]
            ring
      _ = _ := by
        rw [he]
        simp only [Units.val_mul]
        ring

private theorem small_a2_product (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    jacobi (p^4) (p^4)*jacobi (p^4) (p^2)*jacobi (p^4) (p^4*p^2)=
      euler (p^4)*euler p^2 := by
  have hxy : p^4*p^2=p^6 := by rw [← pow_add]
  have hd (a b : ℕ) (h : a+b=8) : (p^4)^2/p^a=p^b := by
    rw [← pow_mul]
    norm_num only [Nat.reduceMul]
    rw [← h,Nat.add_comm a b,pow_add,div_eq_mul_inv,mul_assoc,mul_inv_cancel,mul_one]

  have hp4 := nilpotent_pow p hp 4 (by decide)
  rw [hxy,jacobi_eq_product _ _ hp4,jacobi_eq_product _ _ hp4,jacobi_eq_product _ _ hp4,
    hd 4 4 (by decide),hd 2 6 (by decide),hd 6 2 (by decide)]
  have he := qPochhammerInf_eq_prod_range (a:=(p:R)^2) (m:=4) (by decide)
    (hp.pow (by decide : 2 ≠ 0))
  norm_num only [Finset.prod_range_succ,Finset.prod_range_zero,pow_zero,pow_one,
    one_mul,mul_one,← pow_mul,← pow_add,Nat.reduceMul,Nat.reduceAdd] at he
  simp only [euler,Units.val_pow_eq_pow_val,← pow_mul,Nat.reduceMul]
  rw [he]
  ring

/-- Cooper's equal-base raw constant-term convolution, with all infinite sums evaluated. -/
theorem hasSum_constant_convolution (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    HasSum (fun mn : ℤ × ℤ => coefficient p (-2*mn.1+mn.2) (-mn.1-mn.2)*
      coefficient p mn.1 mn.2) (euler p^4) := by
  have hp4 := nilpotent_pow p hp 4 (by decide)
  have hu : IsUnit (euler (p^4)) := isUnit_qPochhammerInf
    (hp4.pow (by decide : 2 ≠ 0)) (hp4.pow (by decide : 2 ≠ 0))
  have hs := (hasSum_triple_product (p^4) (p^4) (p^2) hp4).mul_left
    (bInv (euler (p^4))*euler p^2)
  rw [small_a2_product p hp] at hs
  have hv : bInv (euler (p^4))*euler p^2*(euler (p^4)*euler p^2)=euler p^4 := by
    calc
      _ = (bInv (euler (p^4))*euler (p^4))*euler p^4 := by ring
      _ = _ := by rw [hu.bInv_mul_cancel,one_mul]
  rw [hv] at hs
  apply hs.congr_fun
  rintro ⟨m,n⟩
  have he : (↑((p^4)^m*(p^2)^n):R)=(↑(p^(4*m)*p^(2*n)):R) := by
    simp only [← zpow_natCast,← zpow_mul]
    norm_num only [Nat.cast_ofNat]
  rw [he]
  calc
    _ = (bInv (euler (p^4))*euler (p^4))*
        (coefficient p (-2*m+n) (-m-n)*coefficient p m n) := by
          rw [hu.bInv_mul_cancel,one_mul]
    _ = _ := by
      rw [mul_assoc,convolution_term p hp]
      ring

theorem constant_convolution (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    (∑' mn : ℤ × ℤ, coefficient p (-2*mn.1+mn.2) (-mn.1-mn.2)*
      coefficient p mn.1 mn.2)=euler p^4 :=
  (hasSum_constant_convolution p hp).tsum_eq

end KanadeRussell.Infra.A2ConvolutionConstant
