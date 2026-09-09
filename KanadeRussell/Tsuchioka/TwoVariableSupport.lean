import KanadeRussell.Tsuchioka.TwoFields

/-!
Separate lower bounds for the two exponents of a normal-ordered product.
These bounds make every contraction along a fixed total exponent finite.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

open scoped BigOperators

variable {A : Type*} [CommRing A]

/-- Lower bounds for the inner and outer exponents, separately. -/
def RectangularBound (f : LaurentSeries (LaurentSeries A)) (l r : ℤ) : Prop :=
  ∀ a b : ℤ, a < l ∨ b < r → (f.coeff b).coeff a = 0

theorem rectangular_mono {f : LaurentSeries (LaurentSeries A)} {l r l' r' : ℤ}
    (h : RectangularBound f l r) (hl : l' ≤ l) (hr : r' ≤ r) :
    RectangularBound f l' r' := by
  intro a b hab
  apply h a b
  rcases hab with ha | hb
  · exact Or.inl (lt_of_lt_of_le ha hl)
  · exact Or.inr (lt_of_lt_of_le hb hr)

theorem rectangular_zero (l r : ℤ) :
    RectangularBound (0 : LaurentSeries (LaurentSeries A)) l r := by
  intro a b h
  simp

theorem rectangular_add {f g : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (hg : RectangularBound g l r) :
    RectangularBound (f + g) l r := by
  intro a b h
  simp only [HahnSeries.coeff_add, hf a b h, hg a b h, add_zero]

theorem rectangular_ne_zero {f : LaurentSeries (LaurentSeries A)} {l r a b : ℤ}
    (hf : RectangularBound f l r) (h : (f.coeff b).coeff a ≠ 0) :
    l ≤ a ∧ r ≤ b := by
  constructor
  · by_contra ha
    exact h (hf a b (Or.inl (by omega)))
  · by_contra hb
    exact h (hf a b (Or.inr (by omega)))

/-- Multiplication adds separate lower bounds; both convolutions are the
finite Hahn-series convolutions. -/
theorem rectangular_mul {f g : LaurentSeries (LaurentSeries A)} {l r l' r' : ℤ}
    (hf : RectangularBound f l r) (hg : RectangularBound g l' r') :
    RectangularBound (f * g) (l + l') (r + r') := by
  intro a b hab
  rw [HahnSeries.coeff_mul, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro uv huv
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  by_cases hfi : (f.coeff uv.1).coeff ij.1 = 0
  · simp [hfi]
  by_cases hgj : (g.coeff uv.2).coeff ij.2 = 0
  · simp [hgj]
  have hfb := rectangular_ne_zero hf hfi
  have hgb := rectangular_ne_zero hg hgj
  have hu := (Finset.mem_addAntidiagonal.mp huv).2.2
  have hi := (Finset.mem_addAntidiagonal.mp hij).2.2
  rcases hab with ha | hb <;> omega

theorem rectangular_single (a b : ℤ) (c : A) :
    RectangularBound (HahnSeries.single b (HahnSeries.single a c)) a b := by
  intro i j hij
  by_cases hj : j = b
  · subst j
    rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single,
      if_neg (by omega : i ≠ a)]
  · simp [HahnSeries.coeff_single, hj]

theorem rectangular_innerPowerSeries (f : PowerSeries A) :
    RectangularBound (HahnSeries.C (f : LaurentSeries A)) 0 0 := by
  intro a b hab
  rw [HahnSeries.C_apply]
  by_cases hb : b = 0
  · subst b
    rw [HahnSeries.coeff_single_same, PowerSeries.coeff_coe, if_pos (by omega)]
  · simp [HahnSeries.coeff_single, hb]

theorem rectangular_outerPowerSeries (f : PowerSeries A) :
    RectangularBound
      ((PowerSeries.map (HahnSeries.C : A →+* LaurentSeries A) f :
        PowerSeries (LaurentSeries A)) : LaurentSeries (LaurentSeries A)) 0 0 := by
  intro a b hab
  rw [PowerSeries.coeff_coe]
  split_ifs with hb
  · simp
  · rw [PowerSeries.coeff_map, HahnSeries.C_apply]
    simp only [HahnSeries.coeff_single]
    rw [if_neg (by omega : a ≠ 0)]

theorem rectangular_diagonal_support {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (d : ℤ) :
    Function.support (fun a => (f.coeff (d - a)).coeff a) ⊆ Set.Icc l (d - r) := by
  intro a ha
  have h := rectangular_ne_zero hf ha
  exact ⟨h.1, by omega⟩

/-- Every fixed-total-exponent diagonal has finite support. -/
theorem rectangular_diagonal_finite {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (d : ℤ) :
    (Function.support (fun a => (f.coeff (d - a)).coeff a)).Finite :=
  (Set.finite_Icc l (d - r)).subset (rectangular_diagonal_support hf d)

theorem rectangular_contraction_support {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (c : ℤ → A) (a b : ℤ) :
    Function.support (fun n => c n * (f.coeff (b - n)).coeff (a + n)) ⊆
      Set.Icc (l - a) (b - r) := by
  intro n hn
  have hc : (f.coeff (b - n)).coeff (a + n) ≠ 0 := by
    intro hz
    exact hn (by simp [hz])
  have h := rectangular_ne_zero hf hc
  exact ⟨by omega, by omega⟩

theorem rectangular_contraction_finite {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (c : ℤ → A) (a b : ℤ) :
    (Function.support (fun n => c n * (f.coeff (b - n)).coeff (a + n))).Finite :=
  (Set.finite_Icc (l - a) (b - r)).subset (rectangular_contraction_support hf c a b)

end KanadeRussell.Tsuchioka.FormalSeries

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

/-- Any polynomial in the two inverse field variables has separate lower
bounds after its iterated Laurent embedding. -/
theorem jointLaurentEmbedding_bounded (p : MvPolynomial (Fin 2) (Space K)) :
    ∃ l r : ℤ, RectangularBound (jointLaurentEmbedding p) l r := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, 0, ?_⟩
    simpa only [jointLaurentEmbedding, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
      HahnSeries.C_apply] using rectangular_single 0 0 c
  | add p q hp hq =>
    obtain ⟨l, r, hp⟩ := hp
    obtain ⟨l', r', hq⟩ := hq
    refine ⟨min l l', min r r', ?_⟩
    rw [map_add]
    exact rectangular_add
      (rectangular_mono hp (min_le_left _ _) (min_le_left _ _))
      (rectangular_mono hq (min_le_right _ _) (min_le_right _ _))
  | mul_X p v hp =>
    obtain ⟨l, r, hp⟩ := hp
    have hv : RectangularBound (jointLaurentEmbedding (MvPolynomial.X v : MvPolynomial (Fin 2) (Space K))) (-1) (-1) := by
      simp only [jointLaurentEmbedding, MvPolynomial.eval₂Hom_X']
      split_ifs
      · exact rectangular_mono (rectangular_single (-1) 0 (1 : Space K)) le_rfl (by omega)
      · exact rectangular_mono (rectangular_single 0 (-1) (1 : Space K)) (by omega) le_rfl
    refine ⟨l + -1, r + -1, ?_⟩
    rw [map_mul]
    exact rectangular_mul hp hv

/-- The actual normal-ordered operator product has separate lower bounds
on every polynomial input. These bounds justify finite diagonal contractions. -/
theorem normalProduct_bounded (w : K) (s t : Fin 3) (f : Space K) :
    ∃ l r : ℤ, RectangularBound (normalProduct w s t f) l r := by
  obtain ⟨l, r, hp⟩ := jointLaurentEmbedding_bounded
    (jointAnnihilationPolynomial w (RootData.simpleRoot 0) (RootData.simpleRoot 0) s t f)
  refine ⟨l, r, ?_⟩
  have hc := rectangular_mul (rectangular_innerPowerSeries (creation (K := K) s))
    (rectangular_outerPowerSeries (creation (K := K) t))
  have h := rectangular_mul hc hp
  simpa only [zero_add, normalProduct] using h

theorem normalProduct_contraction_finite (w : K) (s t : Fin 3) (f : Space K)
    (c : ℤ → Space K) (a b : ℤ) :
    (Function.support (fun n => c n * ((normalProduct w s t f).coeff (b - n)).coeff (a + n))).Finite := by
  obtain ⟨l, r, h⟩ := normalProduct_bounded w s t f
  exact rectangular_contraction_finite h c a b

end KanadeRussell.Tsuchioka.Fock
