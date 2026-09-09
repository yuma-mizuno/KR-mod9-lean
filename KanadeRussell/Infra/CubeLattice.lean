import Mathlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Integer bijections for the cubic dissection of Jacobi's bilateral series. -/
namespace KanadeRussell.Infra.CubeLattice

def combine (hkr : Fin 3 × (ℤ × (ℤ × ℤ))) : (ℤ × ℤ) × ℤ :=
  let h := (hkr.1 : ℤ)
  let k := hkr.2.1
  let r := hkr.2.2.1
  let s := hkr.2.2.2
  ((k+h-r-s,k+r),k+s)

theorem combine_injective : Function.Injective combine := by
  rintro ⟨h,k,r,s⟩ ⟨j,l,u,v⟩ he
  have hh := h.isLt
  have hj := j.isLt
  simp only [combine, Prod.mk.injEq] at he
  have eh : h = j := by apply Fin.ext; omega
  subst j
  simp only [Prod.mk.injEq, true_and]
  omega

theorem combine_surjective : Function.Surjective combine := by
  rintro ⟨⟨a,b⟩,c⟩
  let n := a+b+c
  let k := n/3
  have hn : 0 ≤ n%3 := Int.emod_nonneg n (by decide)
  have hn' : n%3 < 3 := Int.emod_lt_of_pos n (by decide)
  let h : Fin 3 := ⟨(n%3).toNat, by omega⟩
  refine ⟨(h,k,b-k,c-k), ?_⟩
  have hh : (h:ℤ) = n%3 := Int.toNat_of_nonneg hn
  simp only [combine, Prod.mk.injEq]
  rw [hh]
  dsimp only [k,n] at *
  omega

noncomputable def equiv : (Fin 3 × (ℤ × (ℤ × ℤ))) ≃ ((ℤ × ℤ) × ℤ) :=
  Equiv.ofBijective combine ⟨combine_injective,combine_surjective⟩

def shifted (k : Fin 3) (rs : ℤ × ℤ) : ℤ × ℤ :=
  match k with
  | 0 => (rs.1+2*rs.2+1,rs.1-rs.2)
  | 1 => (-2*rs.1-rs.2,rs.1+2*rs.2+1)
  | 2 => (rs.1-rs.2,-2*rs.1-rs.2)

theorem shifted_injective : Function.Injective (fun kr : Fin 3 × (ℤ × ℤ) => shifted kr.1 kr.2) := by
  rintro ⟨i,r,s⟩ ⟨j,u,v⟩ h
  fin_cases i <;> fin_cases j <;> simp [shifted] at h ⊢ <;> omega

theorem shifted_surjective : Function.Surjective (fun kr : Fin 3 × (ℤ × ℤ) => shifted kr.1 kr.2) := by
  rintro ⟨r,s⟩
  have h0 := Int.emod_nonneg (r-s) (by decide : (3:ℤ) ≠ 0)
  have h3 := Int.emod_lt_of_pos (r-s) (by decide : (0:ℤ) < 3)
  interval_cases h : (r-s)%3
  · refine ⟨(2,((r-s)/3,(-2*r-s)/3)), ?_⟩
    simp only [shifted, Prod.mk.injEq]
    omega
  · refine ⟨(0,((r+2*s-1)/3,(r-s-1)/3)), ?_⟩
    simp only [shifted, Prod.mk.injEq]
    omega
  · refine ⟨(1,((-2*r-s+1)/3,(r+2*s-2)/3)), ?_⟩
    simp only [shifted, Prod.mk.injEq]
    omega

noncomputable def shiftedEquiv : Fin 3 × (ℤ × ℤ) ≃ ℤ × ℤ :=
  Equiv.ofBijective (fun kr => shifted kr.1 kr.2) ⟨shifted_injective,shifted_surjective⟩

theorem shifted_norm (k : Fin 3) (r s : ℤ) :
    (shifted k (r,s)).1^2+(shifted k (r,s)).1*(shifted k (r,s)).2+
      (shifted k (r,s)).2^2-(shifted k (r,s)).1-(shifted k (r,s)).2 =
      3*(r^2+r*s+s^2)+r+2*s := by
  fin_cases k <;> norm_num [shifted] <;> ring

end KanadeRussell.Infra.CubeLattice
