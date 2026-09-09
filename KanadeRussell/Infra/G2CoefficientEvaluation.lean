import KanadeRussell.Infra.G2ConstantTerm
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace KanadeRussell.Infra.G2CoefficientEvaluation
open ThetaAddition A2CoefficientResidues
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

private theorem first_exponent (M N k : ℤ) (r : Fin 3) (hM : M=3*k+r) (i j : ℤ) :
    residueExponent (M-N-2*i+j) (N-i-j) (k-i) r =
      residueExponent (M-N) N k r + 2*(i^2+j^2-i*j)+
        (2-2*M+2*N)*i+(2*M-4*N)*j := by
  rw [hM]
  unfold residueExponent
  ring

private theorem first_coefficient (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (M N k : ℤ) (r : Fin 3) (hM : M=3*k+r) (i j : ℤ) :
    A2JacobiCoefficients.coefficient p (M-N-2*i+j) (N-i-j) =
      if r=2 then 0 else
        (↑(((-1:Rˣ)^(r:ℤ))*p^(residueExponent (M-N-2*i+j) (N-i-j) (k-i) r)):R)*euler p :=
  coefficient_residue p hp _ _ (k-i) r (by omega)

/-- The actual coefficient convolution transports termwise to a fourth-base A2 expansion. -/
theorem convolution_term (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (M N k : ℤ) (r : Fin 3) (hM : M=3*k+r) (hr : r≠2) (i j : ℤ) :
    euler (p^4)*(A2JacobiCoefficients.coefficient p (M-N-2*i+j) (N-i-j)*
      A2JacobiCoefficients.coefficient p i j) =
      (↑(((-1:Rˣ)^(r:ℤ))*p^(residueExponent (M-N) N k r)):R)*euler p^2*
        (A2JacobiCoefficients.coefficient (p^4) i j*
          (↑((p^(4-2*M+2*N))^i*(p^(2*M-4*N+2))^j):R)) := by
  let l : ℤ := (i+j)/3
  let s : Fin 3 := ⟨((i+j)%3).toNat,by omega⟩
  have hs : i+j=3*l+(s:ℤ) := by dsimp [l,s]; omega
  have hp4 : IsTopologicallyNilpotent ((p^4:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 4 ≠ 0)
  have hc := coefficient_residue p hp i j l s hs
  have hc4 := coefficient_residue (p^4) hp4 i j l s hs
  by_cases hs2 : s=2
  · simp only [hs2,ite_true] at hc hc4
    rw [hc,hc4]
    ring
  · rw [if_neg hs2] at hc hc4
    have hf := residueExponent_identity i j l s hs hs2
    have he : p^(residueExponent (M-N-2*i+j) (N-i-j) (k-i) r)*
        p^(residueExponent i j l s) =
        p^(residueExponent (M-N) N k r)*((p^4)^(residueExponent i j l s)*
          ((p^(4-2*M+2*N))^i*(p^(2*M-4*N+2))^j)) := by
      simp only [← zpow_natCast,← zpow_mul,← zpow_add]
      congr 1
      norm_num only [Nat.cast_ofNat]
      rw [first_exponent M N k r hM]
      nlinarith [hf]
    rw [first_coefficient p hp M N k r hM,if_neg hr,hc,hc4]
    calc
      _ = euler (p^4)*euler p^2*(↑((-1:Rˣ)^(r:ℤ)):R)*
          (↑((-1:Rˣ)^(s:ℤ)):R)*
          (↑(p^(residueExponent (M-N-2*i+j) (N-i-j) (k-i) r)*
            p^(residueExponent i j l s)):R) := by
              simp only [Units.val_mul]
              ring
      _ = _ := by
        rw [he]
        simp only [Units.val_mul]
        ring

/-- The residue-two class of the actual G2 coefficients vanishes identically. -/
theorem coefficient_zero_of_residue_two (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (M N k : ℤ) (hM : M=3*k+2) : G2JacobiCoefficients.coefficient p M N=0 := by
  unfold G2JacobiCoefficients.coefficient
  calc
    _ = ∑' _ij : ℤ × ℤ, (0:R) := by
      apply tsum_congr
      rintro ⟨i,j⟩
      have hh := first_coefficient p hp M N k 2 (by simpa using hM) i j
      rw [if_pos rfl] at hh
      rw [hh,zero_mul]
    _ = 0 := tsum_zero

/-- A cleared exact evaluation of every actual G2 coefficient, including its zero class. -/
theorem coefficient_class (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (M N k : ℤ) (r : Fin 3) (hM : M=3*k+r) :
    euler (p^4)*G2JacobiCoefficients.coefficient p M N =
      if r=2 then 0 else
        (↑(((-1:Rˣ)^(r:ℤ))*p^(residueExponent (M-N) N k r)):R)*euler p^2*
          (jacobi (p^4) (p^(4-2*M+2*N))*jacobi (p^4) (p^(2*M-4*N+2))*
            jacobi (p^4) (p^(6-2*N))) := by
  by_cases hr : r=2
  · subst r
    rw [if_pos rfl,coefficient_zero_of_residue_two p hp M N k (by simpa using hM),mul_zero]
  · rw [if_neg hr]
    have hp4 : IsTopologicallyNilpotent ((p^4:Rˣ):R) := by
      simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 4 ≠ 0)
    have hh := (G2JacobiCoefficients.summable_coefficient p hp M N).hasSum.mul_left
      (euler (p^4))
    have ha := (A2JacobiCoefficients.hasSum_triple_product (p^4)
      (p^(4-2*M+2*N)) (p^(2*M-4*N+2)) hp4).mul_left
      ((↑(((-1:Rˣ)^(r:ℤ))*p^(residueExponent (M-N) N k r)):R)*euler p^2)
    have he : p^(4-2*M+2*N)*p^(2*M-4*N+2)=p^(6-2*N) := by
      rw [← zpow_add]
      congr 1
      ring
    rw [he] at ha
    apply hh.unique
    apply ha.congr_fun
    rintro ⟨i,j⟩
    exact convolution_term p hp M N k r hM hr i j

/-- A canonical all-index version with the residue and quotient computed from `M`. -/
theorem coefficient_evaluation (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (M N : ℤ) :
    euler (p^4)*G2JacobiCoefficients.coefficient p M N =
      if M%3=2 then 0 else
        (↑(((-1:Rˣ)^(M%3))*p^(residueExponent (M-N) N (M/3) (M%3))):R)*euler p^2*
          (jacobi (p^4) (p^(4-2*M+2*N))*jacobi (p^4) (p^(2*M-4*N+2))*
            jacobi (p^4) (p^(6-2*N))) := by
  let r : Fin 3 := ⟨(M%3).toNat,by omega⟩
  have hr : (r:ℤ)=M%3 := by dsimp [r]; omega
  have hh := coefficient_class p hp M N (M/3) r (by omega)
  have he : r=2 ↔ M%3=2 := by
    rw [← hr]
    constructor
    · intro he
      rw [he]
      rfl
    · intro he
      apply Fin.ext
      exact_mod_cast he
  simpa only [hr,he] using hh

end KanadeRussell.Infra.G2CoefficientEvaluation
