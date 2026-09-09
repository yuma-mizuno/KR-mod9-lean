import KanadeRussell.Tsuchioka.Coefficients

/-! Integer phases in the ordering relation and its corrected exceptional case. -/

namespace KanadeRussell.Tsuchioka.Coefficients

variable {K : Type*} [Field K] [CharZero K] (w : K)

theorem root_ne_zero (hw : w ^ 4 - w ^ 2 + 1 = 0) : w ≠ 0 := by
  intro hz
  simp [hz] at hw

theorem zpow_mod_twelve (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : ℤ) :
    w ^ n = w ^ ((n % 12).toNat) := by
  let u : Kˣ := Units.mk0 w (root_ne_zero w hw)
  have hp : u ^ 12 = 1 := by
    apply Units.ext
    simpa [u] using pow_twelve w hw
  have hz := congrArg (fun v : Kˣ => (v : K)) (zpow_eq_zpow_emod' n hp)
  simp only [Units.val_zpow_eq_zpow_val] at hz
  have hn : ((n % 12).toNat : ℤ) = n % 12 :=
    Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num))
  dsimp [u] at hz
  rw [← hn, zpow_natCast] at hz
  exact hz

theorem zpow_eq_of_mod (hw : w ^ 4 - w ^ 2 + 1 = 0) (m n : ℤ)
    (h : m % 12 = n % 12) : w ^ m = w ^ n := by
  rw [zpow_mod_twelve w hw m, zpow_mod_twelve w hw n, h]

/-- The common phase in the two quadratic relations depends only on A-B. -/
theorem ordering_phase_factor (hw : w ^ 4 - w ^ 2 + 1 = 0) (a b : ℤ) :
    w ^ (4 * a + 9 * b) = w ^ b * w ^ (4 * (a - b)) ∧
    w ^ (9 * a + 4 * b) = w ^ b * w ^ (9 * (a - b)) := by
  have hn := root_ne_zero w hw
  constructor
  · rw [← zpow_add₀ hn]
    apply zpow_eq_of_mod w hw
    omega
  · rw [← zpow_add₀ hn]
    apply zpow_eq_of_mod w hw
    omega

/-- For all integer A,B in the exceptional class, the second-root
coefficients in the two proposed relations coincide. -/
theorem exceptional_cancellation (hw : w ^ 4 - w ^ 2 + 1 = 0) (a b : ℤ)
    (hr : (a - b) % 12 = 7) :
    w ^ (4 * a + 9 * b) - w ^ (9 * a + 4 * b) =
      w ^ (4 * (a - 1) + 9 * (b + 1)) -
        w ^ (9 * (a - 1) + 4 * (b + 1)) := by
  obtain ⟨ha, hb⟩ := ordering_phase_factor w hw a b
  obtain ⟨hc, hd⟩ := ordering_phase_factor w hw (a - 1) (b + 1)
  rw [ha, hb, hc, hd]
  have h4 : w ^ (4 * (a - b)) = w ^ (4 : ℕ) := by
    rw [zpow_mod_twelve w hw]
    congr 1
    omega
  have h9 : w ^ (9 * (a - b)) = w ^ (3 : ℕ) := by
    rw [zpow_mod_twelve w hw]
    congr 1
    omega
  have h4' : w ^ (4 * (a - 1 - (b + 1))) = w ^ (8 : ℕ) := by
    rw [zpow_mod_twelve w hw]
    congr 1
    omega
  have h9' : w ^ (9 * (a - 1 - (b + 1))) = w ^ (9 : ℕ) := by
    rw [zpow_mod_twelve w hw]
    congr 1
    omega
  rw [h4, h9, h4', h9', zpow_add₀ (root_ne_zero w hw), zpow_one]
  have he := exceptional_phase_cancellation w hw
  linear_combination w ^ b * he


/-- The unnormalized leading coefficient d_(A,B) in Section 4.4. -/
def orderingLeading (a b : ℤ) : K :=
  (-24 - 28 * w + 14 * w ^ 3) * (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) -
  (-52 + 104 * w ^ 2 + 90 * w ^ 3) * (w ^ (4 * a + 9 * b) - w ^ (9 * a + 4 * b))

theorem orderingLeading_eq_zero_iff (hw : w ^ 4 - w ^ 2 + 1 = 0) (a b : ℤ) :
    orderingLeading w a b = 0 ↔ (a - b) % 12 = 7 := by
  let r : Fin 12 := ⟨((a - b) % 12).toNat, by omega⟩
  have h4 : ((4 * (a - b)) % 12).toNat = (4 * r.val) % 12 := by
    dsimp [r]
    omega
  have h9 : ((9 * (a - b)) % 12).toNat = (9 * r.val) % 12 := by
    dsimp [r]
    omega
  have hf : orderingLeading w a b = w ^ b * orderingCoefficient w r := by
    obtain ⟨ha, hb⟩ := ordering_phase_factor w hw a b
    dsimp [orderingLeading, orderingCoefficient]
    rw [ha, hb, zpow_mod_twelve w hw (4 * (a - b)),
      zpow_mod_twelve w hw (9 * (a - b)), h4, h9]
    ring
  rw [hf, mul_eq_zero, or_iff_right (zpow_ne_zero _ (root_ne_zero w hw)),
    orderingCoefficient_eq_zero_iff w hw r]
  dsimp [r]
  omega



end KanadeRussell.Tsuchioka.Coefficients
