import KanadeRussell.Tsuchioka.AlternatingSeed
import KanadeRussell.Sectors.TensorPermutation

/-! Alternating tensor polynomials have no principal degrees below three.
This supplies the shifted nonnegative grading for the third highest-weight action. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Tsuchioka.Fock
open Sectors
variable {K : Type*} [Field K] [CharZero K]

/-- A monomial of weight less than three uses only the degree-one variables. -/
theorem low_weight_supported_firstMode (m : (Fin 3 × Mode) →₀ ℕ)
    (hm : Finsupp.weight variableWeight m < 3) (a : Fin 3) (n : Mode) (hn : n ≠ firstMode) :
    m (a,n) = 0 := by
  by_contra h
  have hb := Finsupp.le_weight_of_ne_zero (w := variableWeight)
    (fun s => Int.natCast_nonneg s.2.val) h
  have hn1 : n.val ≠ 1 := fun he => hn (Subtype.ext he)
  have hp := n.property
  change (n.val : ℤ) ≤ Finsupp.weight variableWeight m at hb
  dsimp [IsMode] at hp
  omega

theorem low_weight_monomial_expansion (m : (Fin 3 × Mode) →₀ ℕ)
    (hm : Finsupp.weight variableWeight m < 3) :
    m = ∑ a : Fin 3, Finsupp.single (a,firstMode) (m (a,firstMode)) := by
  classical
  ext s
  rcases s with ⟨a,n⟩
  by_cases hn : n = firstMode
  · subst n
    simp [Finsupp.single_apply, Prod.mk.injEq]
  · rw [low_weight_supported_firstMode m hm a n hn]
    simp [Finsupp.single_apply, Prod.mk.injEq, hn, Ne.symm hn]

theorem low_weight_equal_tensor_counts (m : (Fin 3 × Mode) →₀ ℕ)
    (hm : Finsupp.weight variableWeight m < 3) :
    ∃ a b : Fin 3, a ≠ b ∧ m (a,firstMode) = m (b,firstMode) := by
  have h := congrArg (Finsupp.weight variableWeight) (low_weight_monomial_expansion m hm)
  have hw (a : Fin 3) : variableWeight (a,firstMode) = 1 := rfl
  simp only [map_sum, map_add, Finsupp.weight_single, Fin.sum_univ_three, hw,
    nsmul_eq_mul, mul_one] at h
  by_cases h01 : m (0,firstMode) = m (1,firstMode)
  · exact ⟨0,1,by decide,h01⟩
  by_cases h02 : m (0,firstMode) = m (2,firstMode)
  · exact ⟨0,2,by decide,h02⟩
  refine ⟨1,2,by decide,?_⟩
  omega

theorem low_weight_swap_fixed (m : (Fin 3 × Mode) →₀ ℕ)
    (hm : Finsupp.weight variableWeight m < 3) (a b : Fin 3)
    (hab : m (a,firstMode) = m (b,firstMode)) :
    Finsupp.mapDomain (fun s : Fin 3 × Mode => (Equiv.swap a b s.1,s.2)) m = m := by
  classical
  let e : (Fin 3 × Mode) ≃ (Fin 3 × Mode) := (Equiv.swap a b).prodCongr (Equiv.refl Mode)
  change Finsupp.mapDomain e m = m
  ext s
  rw [Finsupp.mapDomain_equiv_apply]
  rcases s with ⟨c,n⟩
  change m (Equiv.swap a b c,n) = m (c,n)
  by_cases hn : n = firstMode
  · subst n
    by_cases hca : c = a
    · subst c; simpa only [Equiv.swap_apply_left] using hab.symm
    by_cases hcb : c = b
    · subst c; simpa only [Equiv.swap_apply_right] using hab
    rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
  · rw [low_weight_supported_firstMode m hm _ n hn,
      low_weight_supported_firstMode m hm _ n hn]

noncomputable def alternatingSpace : Submodule K (Space K) where
  carrier := {p | ∀ a b : Fin 3, a ≠ b → permute (Equiv.swap a b) p = -p}
  zero_mem' := by simp
  add_mem' hp hq := by
    intro a b hab
    rw [map_add, hp a b hab, hq a b hab, neg_add]
  smul_mem' c p hp := by
    intro a b hab
    rw [map_smul, hp a b hab, smul_neg]

theorem alternating_grade_lt_three (d : ℤ) (hd : d < 3) (p : Space K)
    (hp : p ∈ alternatingSpace) (hg : p ∈ grade d) : p = 0 := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_zero]
  by_contra hc
  have hm : Finsupp.weight variableWeight m < 3 := by rw [hg hc]; exact hd
  obtain ⟨a,b,hab,he⟩ := low_weight_equal_tensor_counts m hm
  have hinj : Function.Injective (fun s : Fin 3 × Mode => (Equiv.swap a b s.1,s.2)) := by
    exact ((Equiv.swap a b).prodCongr (Equiv.refl Mode)).injective
  have hx := MvPolynomial.coeff_rename_mapDomain
    (fun s : Fin 3 × Mode => (Equiv.swap a b s.1,s.2)) hinj p m
  rw [low_weight_swap_fixed m hm a b he] at hx
  change MvPolynomial.coeff m (permute (Equiv.swap a b) p) = MvPolynomial.coeff m p at hx
  rw [hp a b hab, MvPolynomial.coeff_neg] at hx
  have htwo : (2 : K) * MvPolynomial.coeff m p = 0 := by linear_combination -hx
  exact hc ((mul_eq_zero.mp htwo).resolve_left (by norm_num))

theorem alternatingSeed_mem : alternatingSeed (K := K) ∈ alternatingSpace := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> try exact (hab rfl).elim
  all_goals
    norm_num [alternatingSeed, degreeOneVariable, permute_X, map_sub, map_mul,
      Equiv.swap_apply_def, Fin.ext_iff]
    try simp only [show MvPolynomial.X (σ := Fin 3 × Mode) (R := K) (⟨2, by decide⟩, firstMode) =
      MvPolynomial.X (2, firstMode) from rfl]
    ring

theorem mode_mem_alternatingSpace (w : K) (i : ℤ) (p : Space K) (hp : p ∈ alternatingSpace) :
    mode w i p ∈ alternatingSpace := by
  intro a b hab
  rw [permute_mode, hp a b hab, map_neg]

noncomputable def alternatingMode (w : K) (i : ℤ) : Module.End K (alternatingSpace (K := K)) where
  toFun p := ⟨mode w i p.val, mode_mem_alternatingSpace w i p.val p.property⟩
  map_add' p q := by apply Subtype.ext; exact (mode w i).map_add p.val q.val
  map_smul' c p := by apply Subtype.ext; exact (mode w i).map_smul c p.val

noncomputable def alternatingGrade (d : ℤ) : Submodule K (alternatingSpace (K := K)) :=
  (grade (d+3)).comap (alternatingSpace (K := K)).subtype

theorem alternatingGrade_negative (d : ℤ) (hd : d < 0) : alternatingGrade (K := K) d = ⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  rw [Submodule.mem_bot]
  apply Subtype.ext
  exact alternating_grade_lt_three (d+3) (by omega) p.val p.property hp

theorem alternatingMode_mem_grade (w : K) (i d : ℤ) (p : alternatingSpace (K := K))
    (hp : p ∈ alternatingGrade d) : alternatingMode w i p ∈ alternatingGrade (d-i) := by
  change mode w i p.val ∈ grade (d-i+3)
  simpa only [show d-i+3=d+3-i by ring] using mode_mem_grade w i (d+3) p.val hp

noncomputable def alternatingHighestWeightAction (w : K) :
    HighestWeightAction K (alternatingSpace (K := K)) where
  grade := alternatingGrade
  negative := alternatingGrade_negative
  mode := alternatingMode w
  mode_mem := alternatingMode_mem_grade w
  vacuum := ⟨alternatingSeed,alternatingSeed_mem⟩
  vacuum_mem := alternatingSeed_grade

end KanadeRussell.Tsuchioka.Fock
