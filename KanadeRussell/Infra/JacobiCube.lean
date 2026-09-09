import KanadeRussell.Infra.JacobiTrisection
import KanadeRussell.Infra.CubeLattice
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Cubic Jacobi dissection from an exhaustive integral lattice bijection. -/
namespace KanadeRussell.Infra.ThetaAddition
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def cubeCoeffTerm (p : Rˣ) (h : ℤ) (rs : ℤ × ℤ) : R :=
  jacobiTerm p 1 (h-rs.1-rs.2)*jacobiTerm p 1 rs.1*jacobiTerm p 1 rs.2

noncomputable def cubeCoeff (p : Rˣ) (h : ℤ) : R := ∑' rs, cubeCoeffTerm p h rs

private theorem slice_injective (h : ℤ) :
    Function.Injective (fun rs : ℤ × ℤ => ((h-rs.1-rs.2,rs.1),rs.2)) := by
  rintro ⟨r,s⟩ ⟨u,v⟩ he
  simp only [Prod.mk.injEq] at he ⊢
  omega

omit [T2Space R] in
theorem summable_cubeCoeffTerm (p : Rˣ) (h : ℤ) (hp : IsTopologicallyNilpotent (p : R)) :
    Summable (cubeCoeffTerm p h) := by
  have ht := ((hasSum_jacobiTerm p 1 hp).mul_of_nonarchimedean'
    (hasSum_jacobiTerm p 1 hp)).mul_of_nonarchimedean' (hasSum_jacobiTerm p 1 hp)
  have hh : Summable (fun rs : ℤ × ℤ =>
      jacobiTerm p 1 (h-rs.1-rs.2)*jacobiTerm p 1 rs.1*jacobiTerm p 1 rs.2) :=
    ht.summable.comp_injective
      (i := fun rs : ℤ × ℤ => ((h-rs.1-rs.2,rs.1),rs.2)) (slice_injective h)
  exact hh

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
private theorem triple_term (p z : Rˣ) (a b c : ℤ) :
    jacobiTerm p z a*jacobiTerm p z b*jacobiTerm p z c =
      (((-1:Rˣ)^(a+b+c)*z^(a+b+c)*p^(a*(a-1)+b*(b-1)+c*(c-1)) : Rˣ) : R) := by
  unfold jacobiTerm
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
theorem cubeCoeffTerm_formula (p : Rˣ) (h r s : ℤ) :
    cubeCoeffTerm p h (r,s) =
      (((-1:Rˣ)^h*p^((h-r-s)*(h-r-s-1)+r*(r-1)+s*(s-1)) : Rˣ):R) := by
  rw [cubeCoeffTerm, triple_term]
  rw [show h-r-s+r+s=h by ring]
  simp only [one_zpow, mul_one]

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
private theorem term_dissection (p z : Rˣ) (h : ℕ) (k r s : ℤ) :
    jacobiTerm p z (k+(h:ℤ)-r-s)*jacobiTerm p z (k+r)*jacobiTerm p z (k+s) =
      cubeCoeffTerm p h (r,s)*(z:R)^h*jacobiTerm (p^3) (z^3*p^(2*h)) k := by
  rw [triple_term]
  have he : k+(h:ℤ)-r-s+(k+r)+(k+s) = 3*k+h := by ring
  rw [he]
  have hn : (-1:Rˣ)^(3*k+(h:ℤ)) = (-1:Rˣ)^((h:ℤ)+k) := by
    rw [show 3*k+(h:ℤ) = ((h:ℤ)+k)+2*k by ring, zpow_add, zpow_mul]
    have hn2 : (-1:Rˣ)^(2:ℤ) = 1 := by
      rw [zpow_ofNat]
      apply Units.ext
      norm_num
    rw [hn2, one_zpow, mul_one]
  rw [hn]
  unfold cubeCoeffTerm
  rw [triple_term]
  have he0 : (h:ℤ)-r-s+r+s = h := by ring
  rw [he0]
  simp only [one_zpow, mul_one]
  unfold jacobiTerm
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul]
  congr 1
  apply Additive.ofMul.injective
  simp only [← zpow_natCast, ofMul_mul, ofMul_zpow]
  push_cast
  module

/-- The cube is a sum of three bilateral theta series at the cubed nome. -/
theorem jacobi_cube_dissection (p z : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    (jacobi p z)^3 = ∑ h : Fin 3,
      cubeCoeff p (h:ℤ)*(z:R)^(h:ℕ)*jacobi (p^3) (z^3*p^(2*(h:ℕ))) := by
  have hp3 : IsTopologicallyNilpotent ((p^3:Rˣ):R) := by
    simpa only [Units.val_pow_eq_pow_val] using hp.pow (by decide : 3 ≠ 0)
  have ht := ((hasSum_jacobiTerm p z hp).mul_of_nonarchimedean'
    (hasSum_jacobiTerm p z hp)).mul_of_nonarchimedean' (hasSum_jacobiTerm p z hp)
  have hr := CubeLattice.equiv.hasSum_iff.mpr ht
  have hf (h : Fin 3) : HasSum (fun kr : ℤ × (ℤ × ℤ) =>
      jacobiTerm p z (CubeLattice.combine (h,kr)).1.1 *
        jacobiTerm p z (CubeLattice.combine (h,kr)).1.2 *
        jacobiTerm p z (CubeLattice.combine (h,kr)).2)
      (cubeCoeff p (h:ℤ)*(z:R)^(h:ℕ)*jacobi (p^3) (z^3*p^(2*(h:ℕ)))) := by
    have hc := (summable_cubeCoeffTerm p (h:ℤ) hp).hasSum
    have hj := hasSum_jacobiTerm (p^3) (z^3*p^(2*(h:ℕ))) hp3
    have hh := hj.mul_of_nonarchimedean' (hc.mul_right ((z:R)^(h:ℕ)))
    have he : jacobi (p^3) (z^3*p^(2*(h:ℕ))) *
        ((∑' rs, cubeCoeffTerm p (h:ℤ) rs)*(z:R)^(h:ℕ)) =
        cubeCoeff p (h:ℤ)*(z:R)^(h:ℕ)*jacobi (p^3) (z^3*p^(2*(h:ℕ))) := by
      rw [cubeCoeff]
      ring
    rw [he] at hh
    apply hh.congr_fun
    rintro ⟨k,r,s⟩
    dsimp only [CubeLattice.combine]
    rw [term_dissection]
    ring
  have hh := hr.prod_fiberwise hf
  have he := hh.unique (hasSum_fintype _)
  simpa only [pow_succ, pow_zero, one_mul] using he

end KanadeRussell.Infra.ThetaAddition
