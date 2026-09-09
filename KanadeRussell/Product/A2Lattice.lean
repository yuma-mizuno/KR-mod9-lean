import KanadeRussell.Source.Defs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! The integral lattice bijection behind A₂ trisection. -/
namespace KanadeRussell.Product.A2Lattice

def diagonal (rs : ℤ × ℤ) : ℤ × ℤ := (rs.1+2*rs.2, rs.1-rs.2)

def coset (k : Fin 6) (rs : ℤ × ℤ) : ℤ × ℤ :=
  match k with
  | 0 => (3*rs.2+1, 3*rs.1)
  | 1 => (-3*rs.1, 3*rs.2+3*rs.1+1)
  | 2 => (-3*rs.2-3*rs.1-1, 3*rs.2+1)
  | 3 => (-3*rs.2-1, -3*rs.1)
  | 4 => (3*rs.1, -3*rs.2-3*rs.1-1)
  | 5 => (3*rs.2+3*rs.1+1, -3*rs.2-1)

def combine : (ℤ × ℤ) ⊕ (Fin 6 × (ℤ × ℤ)) → ℤ × ℤ :=
  Sum.elim diagonal (fun kr => coset kr.1 kr.2)

theorem combine_injective : Function.Injective combine := by
  intro p q hpq
  rcases p with ⟨r,s⟩ | ⟨i,r,s⟩ <;> rcases q with ⟨u,v⟩ | ⟨j,u,v⟩
  · simp only [combine, Sum.elim_inl, diagonal, Prod.mk.injEq] at hpq
    congr 2 <;> omega
  · fin_cases j <;> simp [combine, diagonal, coset] at hpq <;> omega
  · fin_cases i <;> simp [combine, diagonal, coset] at hpq <;> omega
  · fin_cases i <;> fin_cases j <;> simp [combine, coset] at hpq ⊢ <;> omega

theorem combine_surjective : Function.Surjective combine := by
  rintro ⟨x,y⟩
  by_cases h : x % 3 = y % 3
  · refine ⟨Sum.inl (y+(x-y)/3, (x-y)/3), ?_⟩
    simp only [combine, Sum.elim_inl, diagonal, Prod.mk.injEq]
    omega
  have hx := Int.emod_nonneg x (by decide : (3:ℤ) ≠ 0)
  have hx' := Int.emod_lt_of_pos x (by decide : (0:ℤ) < 3)
  have hy := Int.emod_nonneg y (by decide : (3:ℤ) ≠ 0)
  have hy' := Int.emod_lt_of_pos y (by decide : (0:ℤ) < 3)
  interval_cases hxv : x % 3 <;> interval_cases hyv : y % 3
  all_goals try omega
  · refine ⟨Sum.inr (1, ((-x)/3, (x+y-1)/3)), ?_⟩
    simp [combine, coset, Prod.mk.injEq]
    omega
  · refine ⟨Sum.inr (4, (x/3, (-x-y-1)/3)), ?_⟩
    simp [combine, coset, Prod.mk.injEq]
    omega
  · refine ⟨Sum.inr (0, (y/3, (x-1)/3)), ?_⟩
    simp [combine, coset, Prod.mk.injEq]
    omega
  · refine ⟨Sum.inr (5, ((x+y)/3, (-y-1)/3)), ?_⟩
    simp [combine, coset, Prod.mk.injEq]
    omega
  · refine ⟨Sum.inr (3, ((-y)/3, (-x-1)/3)), ?_⟩
    simp [combine, coset, Prod.mk.injEq]
    omega
  · refine ⟨Sum.inr (2, ((-x-y)/3, (y-1)/3)), ?_⟩
    simp [combine, coset, Prod.mk.injEq]
    omega

noncomputable def equiv : (ℤ × ℤ) ⊕ (Fin 6 × (ℤ × ℤ)) ≃ ℤ × ℤ :=
  Equiv.ofBijective combine ⟨combine_injective, combine_surjective⟩

theorem diagonal_norm (r s : ℤ) :
    (diagonal (r,s)).1^2 + (diagonal (r,s)).1*(diagonal (r,s)).2 +
      (diagonal (r,s)).2^2 = 3*(r^2+r*s+s^2) := by
  dsimp only [diagonal]
  ring

theorem coset_norm (k : Fin 6) (r s : ℤ) :
    (coset k (r,s)).1^2 + (coset k (r,s)).1*(coset k (r,s)).2 +
      (coset k (r,s)).2^2 = 1+3*(3*(r^2+r*s+s^2)+r+2*s) := by
  fin_cases k <;> norm_num [coset] <;> ring

end KanadeRussell.Product.A2Lattice
