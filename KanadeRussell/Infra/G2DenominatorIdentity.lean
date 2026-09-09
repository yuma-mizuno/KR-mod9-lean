import KanadeRussell.Infra.G2CoefficientHFrame
import KanadeRussell.Infra.G2CoefficientRecurrences
import KanadeRussell.Infra.G2CoefficientTranslateFour
import KanadeRussell.Infra.G2ConstantTerm

/-! The actual G2 denominator sum, obtained from the full six-Jacobi coefficient
expansion, its proved coefficient classification, and the evaluated constant.
The twelve occupied residue classes are reindexed injectively; all omitted
integer lattice points are proved to have coefficient zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped QTheory
namespace KanadeRussell.Infra.G2DenominatorIdentity
open ThetaAddition G2CoefficientRigidity A2CoefficientResidues

/-- The occupied integer lattice points, retaining the original H-polynomial powers. -/
def latticeIndex (z : Fin 12 × (ℤ × ℤ)) : ℤ × ℤ :=
  (12*z.2.1+(hPowers z.1).1,4*z.2.2+(hPowers z.1).2)

theorem latticeIndex_injective : Function.Injective latticeIndex := by
  rintro ⟨h,m,n⟩ ⟨h',m',n'⟩ he
  have hi := congrArg Prod.fst he
  have hj := congrArg Prod.snd he
  dsimp [latticeIndex] at hi hj
  have hlt := (hResidue h).1.isLt
  have hlt' := (hResidue h').1.isLt
  have hh : h=h' := by
    apply hResidue_injective
    apply Prod.ext
    · apply Fin.ext
      change (hPowers h).1=(hPowers h').1
      dsimp [hResidue] at hlt hlt'
      omega
    · apply Fin.ext
      change (hPowers h).2%4=(hPowers h').2%4
      omega
  subst h'
  congr 1
  apply Prod.ext <;> omega

/-- Cooper's complete quadratic exponent in the unit `p`, whose square is `Q`. -/
def exponent (h : Fin 12) (m n : ℤ) : ℤ :=
  2*(12*m*m-12*m*n+4*n*n-m-n+
    (2*m-n)*(hPowers h).1+(2*n-3*m)*(hPowers h).2)

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def sixProduct (p x y : Rˣ) : R :=
  jacobi p x*jacobi p y*jacobi p (x*y)*jacobi p (x^2*y)*
    jacobi p (x^3*y)*jacobi p (x^3*y^2)

noncomputable def flattenedTerm (p x y : Rˣ) (z : Fin 12 × (ℤ × ℤ)) : R :=
  (hSign z.1:R)*(↑(p^(exponent z.1 z.2.1 z.2.2)*
    x^(12*z.2.1+(hPowers z.1).1)*y^(4*z.2.2+(hPowers z.1).2)):R)

private theorem actual_twelve (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (M N : ℤ) :
    G2JacobiCoefficients.coefficient p (M+12) N =
      (↑(p^(2*(2*M-3*N+11))):R)*G2JacobiCoefficients.coefficient p M N := by
  rw [show 2*(2*M-3*N+11)=4*M-6*N+22 by ring]
  exact G2JacobiCoefficients.coefficient_translate_twelve p hp M N

private theorem actual_four (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) (M N : ℤ) :
    G2JacobiCoefficients.coefficient p M (N+4) =
      (↑(p^(2*(-M+2*N+3))):R)*G2JacobiCoefficients.coefficient p M N := by
  rw [show 2*(-M+2*N+3)=-2*M+4*N+6 by ring]
  exact G2JacobiCoefficients.coefficient_translate_four p hp M N

/-- Every occupied lattice coefficient has the evaluated constant factor. -/
theorem coefficient_latticeIndex (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (htwo : IsUnit (2:R)) (z : Fin 12 × (ℤ × ℤ)) :
    G2JacobiCoefficients.coefficient p (latticeIndex z).1 (latticeIndex z).2 =
      (hSign z.1:R)*(↑(p^(exponent z.1 z.2.1 z.2.2)):R)*euler p^4 := by
  have hh := coefficient_h_translate p (G2JacobiCoefficients.coefficient p)
    (actual_twelve p hp) (actual_four p hp) htwo
    (G2JacobiCoefficients.coefficient_short_reflection p hp)
    (G2JacobiCoefficients.coefficient_long_reflection p hp) z.1 z.2.1 z.2.2
  rw [G2ConstantTerm.coefficient_zero p hp] at hh
  exact hh

/-- The classification kills every lattice point outside the twelve residue classes. -/
theorem coefficient_zero_outside (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (htwo : IsUnit (2:R)) (z : ℤ × ℤ) (hz : z∉Set.range latticeIndex) :
    G2JacobiCoefficients.coefficient p z.1 z.2=0 := by
  let M : Fin 12 := ⟨(z.1%12).toNat,by omega⟩
  let N : Fin 4 := ⟨(z.2%4).toNat,by omega⟩
  have hc := classification p (G2JacobiCoefficients.coefficient p)
    (actual_twelve p hp) (actual_four p hp) htwo
    (G2JacobiCoefficients.coefficient_short_reflection p hp)
    (G2JacobiCoefficients.coefficient_long_reflection p hp) z.1 z.2
  have hh : residueMultiplier p M N=0 := by
    apply residueMultiplier_eq_zero_of_not_h
    intro h he
    apply hz
    have hi := congrArg (fun t : Fin 12 × Fin 4 => (t.1:ℕ)) he
    have hj := congrArg (fun t : Fin 12 × Fin 4 => (t.2:ℕ)) he
    dsimp [hResidue,M,N] at hi hj
    refine ⟨(h,(z.1-(hPowers h).1)/12,(z.2-(hPowers h).2)/4),?_⟩
    apply Prod.ext <;> dsimp [latticeIndex] <;> omega
  change residueMultiplier p ⟨(z.1%12).toNat,_⟩ ⟨(z.2%4).toNat,_⟩=0 at hh
  rw [hh,mul_zero,zero_mul] at hc
  exact hc

/-- The complete denominator identity, with its fourth Euler factor retained in each term. -/
theorem hasSum_euler_mul_flattened (p x y : Rˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (htwo : IsUnit (2:R)) :
    HasSum (fun z : Fin 12 × (ℤ × ℤ) => euler p^4*flattenedTerm p x y z)
      (sixProduct p x y) := by
  have hz (z : ℤ × ℤ) (h : z∉Set.range latticeIndex) :
      G2JacobiCoefficients.coefficient p z.1 z.2*(↑(x^z.1*y^z.2):R)=0 := by
    rw [coefficient_zero_outside p hp htwo z h,zero_mul]
  have hh := (latticeIndex_injective.hasSum_iff hz).mpr
    (G2JacobiCoefficients.hasSum_six_product p x y hp)
  apply hh.congr_fun
  intro z
  simp only [Function.comp_apply]
  rw [coefficient_latticeIndex p hp htwo]
  simp only [flattenedTerm,latticeIndex,Units.val_mul]
  ring

/-- The same identity normalized by the proved Euler unit. -/
theorem hasSum_flattened (p x y : Rˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (htwo : IsUnit (2:R)) :
    HasSum (flattenedTerm p x y) (bInv (euler p)^4*sixProduct p x y) := by
  have hu : IsUnit (euler p) := isUnit_qPochhammerInf
    (hp.pow (by decide : 2 ≠ 0)) (hp.pow (by decide : 2 ≠ 0))
  have hh := (hasSum_euler_mul_flattened p x y hp htwo).mul_left (bInv (euler p)^4)
  apply hh.congr_fun
  intro z
  calc
    _ = (bInv (euler p)*euler p)^4*flattenedTerm p x y z := by
      rw [hu.bInv_mul_cancel,one_pow,one_mul]
    _ = _ := by ring

theorem tsum_flattened (p x y : Rˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (htwo : IsUnit (2:R)) :
    (∑' z : Fin 12 × (ℤ × ℤ), flattenedTerm p x y z)=
      bInv (euler p)^4*sixProduct p x y :=
  (hasSum_flattened p x y hp htwo).tsum_eq

end KanadeRussell.Infra.G2DenominatorIdentity
