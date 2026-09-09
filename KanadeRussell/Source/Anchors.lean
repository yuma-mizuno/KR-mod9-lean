import KanadeRussell.Source.Defs

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell

theorem isUnit_qPochhammer_q (d m : ℕ) : IsUnit (q ^ (d + 1); q ^ (d + 1))_m :=
  isUnit_qPochhammer (by simp [q]) (by simp [q]) m

/-- Coefficients outside a finite square vanish; hence the double series is honest. -/
theorem sourceTerm_coeff_eq_zero (a b k : ℕ) (mn : ℕ × ℕ)
    (h : k < mn.1 ∨ k < mn.2) : coeff k (sourceTerm a b mn) = 0 := by
  have hm : mn.1 ≤ mn.1 ^ 2 := Nat.le_self_pow (by decide) _
  have hn : mn.2 ≤ mn.2 ^ 2 := Nat.le_self_pow (by decide) _
  have hexp : ¬(mn.1 ^ 2 + 3 * mn.1 * mn.2 + 3 * mn.2 ^ 2 + a * mn.1 + b * mn.2 ≤ k) := by
    rcases h with h | h <;> omega
  rw [sourceTerm, mul_assoc, coeff_X_pow_mul', if_neg hexp]

theorem summable_sourceTerm (a b : ℕ) : Summable (sourceTerm a b) := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (k + 1) ×ˢ Finset.range (k + 1))).subset
  intro mn hmn
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
  by_contra h
  have hz := sourceTerm_coeff_eq_zero a b k mn (by omega)
  exact hmn hz

theorem hasProd_P9 (r : ℕ) :
    HasProd (fun i : ℕ ↦ 1 - q ^ (r + 1) * (q ^ 9) ^ i) (P9 (r + 1)) :=
  hasProd_qPochhammerInf (by simp [q])

theorem isUnit_P9 (r : ℕ) (hr : 0 < r) : IsUnit (P9 r) :=
  isUnit_qPochhammerInf (by simpa [q] using (PowerSeries.HasEval.X (R := ℤ)).pow hr.ne')
    (by simp [q])

theorem K₁_mul : K₁ * (P9 1 * P9 3 * P9 6 * P9 8) = 1 :=
  (((isUnit_P9 1 (by decide)).mul (isUnit_P9 3 (by decide))).mul
    (isUnit_P9 6 (by decide)) |>.mul (isUnit_P9 8 (by decide))).bInv_mul_cancel

theorem K₂_mul : K₂ * (P9 2 * P9 3 * P9 6 * P9 7) = 1 :=
  (((isUnit_P9 2 (by decide)).mul (isUnit_P9 3 (by decide))).mul
    (isUnit_P9 6 (by decide)) |>.mul (isUnit_P9 7 (by decide))).bInv_mul_cancel

theorem K₃_mul : K₃ * (P9 3 * P9 4 * P9 5 * P9 6) = 1 :=
  (((isUnit_P9 3 (by decide)).mul (isUnit_P9 4 (by decide))).mul
    (isUnit_P9 5 (by decide)) |>.mul (isUnit_P9 6 (by decide))).bInv_mul_cancel

@[simp] theorem constantCoeff_P9 (r : ℕ) (hr : 0 < r) : constantCoeff (P9 r) = 1 := by
  rw [P9, map_qPochhammerInf (constantCoeff (R := ℤ)) (continuous_constantCoeff _) _ (by simp [q])]
  simp [q, hr.ne']

@[simp] theorem constantCoeff_source (a b : ℕ) :
    constantCoeff (∑' mn, sourceTerm a b mn) = 1 := by
  rw [(summable_sourceTerm a b).map_tsum (constantCoeff (R := ℤ)) (continuous_constantCoeff _)]
  rw [tsum_eq_single (0, 0)]
  · simp [sourceTerm, q]
  · intro mn hmn
    rw [← coeff_zero_eq_constantCoeff]
    apply sourceTerm_coeff_eq_zero
    by_contra h
    apply hmn
    apply Prod.ext <;> simp only <;> omega

theorem constantCoeff_eq_one :
    constantCoeff A = 1 ∧ constantCoeff B = 1 ∧ constantCoeff C = 1 ∧
    constantCoeff K₁ = 1 ∧ constantCoeff K₂ = 1 ∧ constantCoeff K₃ = 1 := by
  have h1 := congrArg (constantCoeff (R := ℤ)) K₁_mul
  have h2 := congrArg (constantCoeff (R := ℤ)) K₂_mul
  have h3 := congrArg (constantCoeff (R := ℤ)) K₃_mul
  simp (disch := decide) only [map_mul, map_one, constantCoeff_P9, mul_one] at h1 h2 h3
  exact ⟨constantCoeff_source 0 0, constantCoeff_source 1 3, constantCoeff_source 2 3, h1, h2, h3⟩

end KanadeRussell
