import KanadeRussell.Sectors.TensorPermutation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! A non-vacuum sector obtained from the transposition-antisymmetric subspace. -/
namespace KanadeRussell.Sectors
open Tsuchioka Tsuchioka.Fock
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem grade_zero_constant (p : Space K) (hp : p ∈ grade 0) :
    p = MvPolynomial.C (MvPolynomial.constantCoeff p) := by
  classical
  apply MvPolynomial.ext
  intro m
  by_cases hm : m=0
  · subst m; rw [MvPolynomial.coeff_zero_C]; rfl
  · have hc : MvPolynomial.coeff m p = 0 := by
      by_contra hc
      have hw := hp hc
      have he : m=0 := by
        ext s
        by_contra hs
        have hh := Finsupp.le_weight_of_ne_zero (w := variableWeight)
          (fun s => Int.natCast_nonneg s.2.val) hs
        have hpos : 0 < variableWeight s := by
          change (0:ℤ) < (s.2.val:ℤ)
          exact_mod_cast mode_pos s.2
        rw [hw] at hh
        omega
      exact hm he
    simp [hc, MvPolynomial.coeff_C, Ne.symm hm]

noncomputable def swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

noncomputable def skewSpace : Submodule K (Space K) :=
  LinearMap.ker ((permute (K := K) swap01).toLinearMap + LinearMap.id)

omit [CharZero K] in
theorem mem_skewSpace (p : Space K) : p ∈ skewSpace (K := K) ↔ permute swap01 p = -p := by
  change permute swap01 p + p = 0 ↔ _
  exact add_eq_zero_iff_eq_neg

theorem mode_mem_skewSpace (w : K) (i : ℤ) (p : Space K) (hp : p ∈ skewSpace) :
    mode w i p ∈ skewSpace := by
  rw [mem_skewSpace] at hp ⊢
  rw [permute_mode, hp, map_neg]

noncomputable def skewMode (w : K) (i : ℤ) : Module.End K (skewSpace (K := K)) where
  toFun p := ⟨mode w i p.val, mode_mem_skewSpace w i p.val p.property⟩
  map_add' p q := by apply Subtype.ext; exact (mode w i).map_add p.val q.val
  map_smul' c p := by apply Subtype.ext; exact (mode w i).map_smul c p.val

noncomputable def skewGrade (d : ℤ) : Submodule K (skewSpace (K := K)) :=
  (grade (d+1)).comap (skewSpace (K := K)).subtype

theorem skewGrade_negative (d : ℤ) (hd : d<0) : skewGrade (K := K) d = ⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  rw [Submodule.mem_bot]
  apply Subtype.ext
  change p.val=0
  change p.val ∈ grade (d+1) at hp
  by_cases hn : d+1<0
  · rw [grade_negative _ hn, Submodule.mem_bot] at hp
    exact hp
  · have hz : d+1=0 := by omega
    rw [hz] at hp
    have hc := grade_zero_constant p.val hp
    have hs := (mem_skewSpace p.val).mp p.property
    have hfix : permute swap01 p.val = p.val := by rw [hc, permute_C]
    rw [hfix] at hs
    have htwo : (2:K) • p.val = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr hs
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem skewMode_mem_grade (w : K) (i d : ℤ) (p : skewSpace (K := K))
    (hp : p ∈ skewGrade d) : skewMode w i p ∈ skewGrade (d-i) := by
  change mode w i p.val ∈ grade (d-i+1)
  have h := mode_mem_grade w i (d+1) p.val hp
  simpa only [show d-i+1=d+1-i by ring] using h

end KanadeRussell.Sectors
