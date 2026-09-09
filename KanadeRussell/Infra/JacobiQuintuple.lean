import KanadeRussell.Product.CubicFrame
import KanadeRussell.Infra.JacobiSeriesDissection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped QTheory
namespace KanadeRussell.Infra.JacobiQuintuple
open ThetaAddition

def residueEquiv : Fin 3 × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun rkt := (rkt.2.1+(rkt.1:ℤ)-2*rkt.2.2,rkt.2.1+rkt.2.2)
  invFun nm := let r : Fin 3 := ⟨((nm.1+2*nm.2)%3).toNat,by omega⟩
    let k := (nm.1+2*nm.2-(r:ℤ))/3
    (r,(k,nm.2-k))
  left_inv := by
    rintro ⟨r,k,t⟩
    apply Prod.ext
    · apply Fin.ext; simp only; omega
    · apply Prod.ext <;> simp only <;> omega
  right_inv := by
    rintro ⟨n,m⟩
    apply Prod.ext <;> simp only <;> omega

variable {R : Type*} [CommRing R]

theorem term_residue (p z : Rˣ) (r k t : ℤ) :
    jacobiTerm p z (k+r-2*t)*jacobiTerm (p^2) (p^2*z^2) (k+t) =
      (↑(((-1:Rˣ)^r*z^r)*p^(r*(r-1))):R)*
      (jacobiTerm (p^3) ((-1:Rˣ)*z^3*p^(2*r+2)) k *
        jacobiTerm (p^6) (p^(8-4*r)) t) := by
  have hs : (-1:Rˣ)^(k+r-2*t)*(-1:Rˣ)^(k+t) = (-1:Rˣ)^r*(-1:Rˣ)^t := by
    rw [← zpow_add, show k+r-2*t+(k+t)=2*(k-t)+(r+t) by ring,
      zpow_add, zpow_mul, zpow_add]
    norm_num [zpow_ofNat]
  have hk : (-1:Rˣ)^k*(-1:Rˣ)^k=1 := by
    rw [← zpow_add, show k+k=2*k by ring,zpow_mul]
    norm_num [zpow_ofNat]
  simp only [jacobiTerm, ← Units.val_mul, mul_zpow]
  congr 1
  calc
    _ = ((-1:Rˣ)^(k+r-2*t)*(-1:Rˣ)^(k+t))*
      (z^(k+r-2*t)*p^((k+r-2*t)*(k+r-2*t-1))*(p^2)^(k+t)*(z^2)^(k+t)*
        (p^2)^((k+t)*(k+t-1))) := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul]
      abel
    _ = _ := by
      rw [hs]
      have hrewrite : (-1:Rˣ)^k*(((-1:Rˣ)^k*(z^3)^k)* (p^(2*r+2))^k) =
          (z^3)^k*(p^(2*r+2))^k := by rw [← mul_assoc,← mul_assoc,hk,one_mul]
      rw [hrewrite]
      apply Additive.ofMul.injective
      simp only [ofMul_mul,ofMul_zpow,ofMul_pow]
      module
variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R]

theorem residue_sum (p z : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    jacobi p z * jacobi (p^2) (p^2*z^2) = ∑ r : Fin 3,
      (↑(((-1:Rˣ)^(r:ℤ)*z^(r:ℤ))*p^((r:ℤ)*(r-1))):R)*
      (jacobi (p^3) ((-1:Rˣ)*z^3*p^(2*(r:ℤ)+2)) *
        jacobi (p^6) (p^(8-4*(r:ℤ)))) := by
  have hpn (n : ℕ) (hn : n ≠ 0) : IsTopologicallyNilpotent ((p^n:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow hn
  have ht : HasSum (fun nm : ℤ × ℤ => jacobiTerm p z nm.1 *
      jacobiTerm (p^2) (p^2*z^2) nm.2) (jacobi p z * jacobi (p^2) (p^2*z^2)) :=
    (hasSum_jacobiTerm p z hp).mul_of_nonarchimedean'
      (hasSum_jacobiTerm (p^2) (p^2*z^2) (hpn 2 (by decide)))
  have hf (r : Fin 3) : HasSum (fun kt : ℤ × ℤ =>
      jacobiTerm p z (kt.1+(r:ℤ)-2*kt.2)*jacobiTerm (p^2) (p^2*z^2) (kt.1+kt.2))
      ((↑(((-1:Rˣ)^(r:ℤ)*z^(r:ℤ))*p^((r:ℤ)*(r-1))):R)*
        (jacobi (p^3) ((-1:Rˣ)*z^3*p^(2*(r:ℤ)+2))*jacobi (p^6) (p^(8-4*(r:ℤ))))) := by
    have hh := ((hasSum_jacobiTerm (p^3) ((-1:Rˣ)*z^3*p^(2*(r:ℤ)+2)) (hpn 3 (by decide))).mul_of_nonarchimedean'
      (hasSum_jacobiTerm (p^6) (p^(8-4*(r:ℤ))) (hpn 6 (by decide)))).mul_left
        (↑(((-1:Rˣ)^(r:ℤ)*z^(r:ℤ))*p^((r:ℤ)*(r-1))):R)
    apply hh.congr_fun
    rintro ⟨k,t⟩
    exact term_residue p z r k t
  have hwhole := residueEquiv.hasSum_iff.mpr ht
  exact (hwhole.prod_fiberwise hf).unique (hasSum_fintype _)

/-- The quintuple product is evaluated by an exact bilateral determinant-three reindexing. -/
theorem quintuple (p z : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    jacobi p z * jacobi (p^2) (p^2*z^2) =
      ((p:R)^4;(p:R)^4)_∞ *
        (jacobi (p^3) ((-1:Rˣ)*z^3*p^2) -
          (z:R)*jacobi (p^3) ((-1:Rˣ)*z^3*p^4)) := by
  have hp2 : IsTopologicallyNilpotent ((p^2:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 2 ≠ 0)
  have hp6 : IsTopologicallyNilpotent ((p^6:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 6 ≠ 0)
  have h4 : jacobi (p^6) (p^4) = ((p:R)^4;(p:R)^4)_∞ := by
    simpa only [← pow_mul,Units.val_pow_eq_pow_val,Nat.reduceMul] using
      Product.jacobi_cubic_argument (p^2) hp2
  have h8 : jacobi (p^6) (p^8) = ((p:R)^4;(p:R)^4)_∞ := by
    have he : (p^6)^2/p^4=p^8 := by
      apply Additive.ofMul.injective
      simp only [ofMul_div,ofMul_pow]
      module
    rw [← he,Product.CubicFrame.jacobi_complement,h4]
  rw [residue_sum p z hp,Fin.sum_univ_three]
  simp only [show (2 : Fin 3) = ⟨2, by decide⟩ by decide]
  norm_num only [zpow_ofNat,Units.val_mul,Units.val_neg,Units.val_one,Units.val_pow_eq_pow_val,
    zpow_zero,zpow_one,pow_zero,pow_one,Int.reduceMul,Int.reduceAdd,Int.reduceSub,
    Fin.val_zero,Fin.val_one,Fin.val_ofNat]
  rw [h8,h4,jacobi_one_eq_zero (p^6) hp6]
  ring
end KanadeRussell.Infra.JacobiQuintuple
