import KanadeRussell.Source.Defs
import KanadeRussell.Infra.BaseChange
set_option backward.isDefEq.respectTransparency false

/-! The A₂ theta parity identity, paper `eq:a2-parity`, in the t-world. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity

namespace KanadeRussell.Infra

noncomputable def theta (d : ℕ) : PowerSeries ℤ := ∑' n : ℤ, X ^ (d * n.natAbs ^ 2)

noncomputable def twist : PowerSeries ℤ →+* PowerSeries ℤ := rescale (-1)

theorem twist_continuous : Continuous twist := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, tendsto_iff_coeff_tendsto]
  intro n
  simp only [twist, coeff_rescale]
  exact (continuous_const.mul (continuous_coeff ℤ n)).continuousAt

theorem summable_theta (d : ℕ) (hd : 0 < d) :
    Summable (fun n : ℤ => (X : PowerSeries ℤ) ^ (d * n.natAbs ^ 2)) := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply (Set.finite_Icc (-(k : ℤ)) k).subset
  intro n hn
  have he : d * n.natAbs ^ 2 = k := by
    by_contra he
    exact hn (by simp [coeff_X_pow, Ne.symm he])
  have hb : n.natAbs ≤ k := by
    have hsq : n.natAbs ≤ n.natAbs ^ 2 := Nat.le_self_pow (by decide) _
    nlinarith
  have hh : |n| ≤ (k : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hb
  exact abs_le.mp hh

/-- The A₂ exponent has no negative values hidden by `Int.toNat`. -/
theorem a2_nonneg (r s : ℤ) : 0 ≤ r ^ 2 + r * s + s ^ 2 := by
  nlinarith [sq_nonneg (r - s), sq_nonneg (r + s)]

theorem summable_a2 :
    Summable (fun rs : ℤ × ℤ => (X : PowerSeries ℤ) ^
      (rs.1 ^ 2 + rs.1 * rs.2 + rs.2 ^ 2).toNat) := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply ((Set.finite_Icc (-(2 * (k : ℤ) + 2)) (2 * k + 2)).prod
    (Set.finite_Icc (-(2 * (k : ℤ) + 2)) (2 * k + 2))).subset
  rintro ⟨r, s⟩ hn
  have he : (r ^ 2 + r * s + s ^ 2).toNat = k := by
    by_contra he
    exact hn (by simp [coeff_X_pow, Ne.symm he])
  have hq : r ^ 2 + r * s + s ^ 2 = (k : ℤ) := by
    rw [← Int.toNat_of_nonneg (a2_nonneg r s), he]
  have hr : r ^ 2 ≤ 4 * (k : ℤ) := by nlinarith [sq_nonneg (r + 2 * s)]
  have hs : s ^ 2 ≤ 4 * (k : ℤ) := by nlinarith [sq_nonneg (2 * r + s)]
  change (-(2 * (k : ℤ) + 2) ≤ r ∧ r ≤ 2 * k + 2) ∧
    (-(2 * (k : ℤ) + 2) ≤ s ∧ s ≤ 2 * k + 2)
  constructor <;> constructor <;> nlinarith [sq_nonneg ((k : ℤ) + 1)]

private def lattice (rs : ℤ × ℤ) : ℤ × ℤ := (2 * rs.1 + rs.2, rs.2)

private theorem lattice_injective : Function.Injective lattice := by
  rintro ⟨r, s⟩ ⟨u, v⟩ h
  simp only [lattice, Prod.mk.injEq] at h ⊢
  omega

private def thetaExponent (kl : ℤ × ℤ) : ℕ := kl.1.natAbs ^ 2 + 3 * kl.2.natAbs ^ 2

private theorem thetaExponent_cast (k l : ℤ) :
    (thetaExponent (k, l) : ℤ) = k ^ 2 + 3 * l ^ 2 := by
  simp [thetaExponent]

private theorem thetaExponent_lattice (r s : ℤ) :
    thetaExponent (lattice (r, s)) = 4 * (r ^ 2 + r * s + s ^ 2).toNat := by
  have he := thetaExponent_cast (2 * r + s) s
  have hh := Int.toNat_of_nonneg (a2_nonneg r s)
  dsimp [lattice]
  exact_mod_cast (show (thetaExponent (2 * r + s, s) : ℤ) =
    4 * ((r ^ 2 + r * s + s ^ 2).toNat : ℤ) by rw [he, hh]; ring)

private theorem thetaExponent_parity (k l : ℤ) :
    (thetaExponent (k, l) : ℤ) % 2 = (k - l) % 2 := by
  rw [thetaExponent_cast]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk <;>
    rcases Int.emod_two_eq_zero_or_one l with hl | hl <;>
    simp [Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, hk, hl]

private noncomputable def evenThetaTerm (kl : ℤ × ℤ) : PowerSeries ℤ :=
  X ^ thetaExponent kl + (-X) ^ thetaExponent kl

private theorem evenThetaTerm_off_lattice (kl : ℤ × ℤ) (h : kl ∉ Set.range lattice) :
    evenThetaTerm kl = 0 := by
  have hpar : (kl.1 - kl.2) % 2 ≠ 0 := by
    intro he
    apply h
    refine ⟨((kl.1 - kl.2) / 2, kl.2), ?_⟩
    have hd := Int.mul_ediv_add_emod (kl.1 - kl.2) 2
    apply Prod.ext
    · change 2 * ((kl.1 - kl.2) / 2) + kl.2 = kl.1
      omega
    · rfl
  have hodd : Odd (thetaExponent kl) := by
    rw [Nat.odd_iff]
    have he : (thetaExponent kl : ℤ) % 2 = (kl.1 - kl.2) % 2 :=
      thetaExponent_parity kl.1 kl.2
    omega
  simp only [evenThetaTerm, hodd.neg_pow, add_neg_cancel]

private theorem evenThetaTerm_lattice (rs : ℤ × ℤ) :
    evenThetaTerm (lattice rs) =
      2 * baseChange (X ^ (rs.1 ^ 2 + rs.1 * rs.2 + rs.2 ^ 2).toNat) := by
  rw [evenThetaTerm, thetaExponent_lattice]
  have he : Even (4 * (rs.1 ^ 2 + rs.1 * rs.2 + rs.2 ^ 2).toNat) := by
    exact even_iff_two_dvd.mpr ⟨2 * (rs.1 ^ 2 + rs.1 * rs.2 + rs.2 ^ 2).toNat, by ring⟩
  rw [he.neg_pow, map_pow, baseChange_X, ← pow_mul]
  ring

/-- The even theta product is exactly twice the A₂ series after `q = t⁴`.
This is a lattice bijection, with no triple-product or modular-form input. -/
theorem theta_even_product :
    theta 1 * theta 3 + twist (theta 1) * twist (theta 3) = 2 * baseChange a := by
  have hp : HasSum (fun kl : ℤ × ℤ => (X : PowerSeries ℤ) ^ thetaExponent kl)
      (theta 1 * theta 3) := by
    have h := (summable_theta 1 (by decide)).hasSum.mul_of_nonarchimedean'
      (summable_theta 3 (by decide)).hasSum
    simpa only [theta, thetaExponent, one_mul, pow_add] using h
  have hm := hp.map twist twist_continuous
  have he : HasSum evenThetaTerm
      (theta 1 * theta 3 + twist (theta 1) * twist (theta 3)) := by
    convert hp.add hm using 1
    · ext kl
      simp [evenThetaTerm, twist]
    · simp
  have hr := lattice_injective.hasSum_iff evenThetaTerm_off_lattice |>.mpr he
  have ha := ((summable_a2.hasSum.map baseChange baseChange_continuous).mul_left
    (2 : PowerSeries ℤ))
  have hc : HasSum (evenThetaTerm ∘ lattice) (2 * baseChange a) := by
    exact ha.congr_fun (fun rs => evenThetaTerm_lattice rs)
  exact hr.unique hc

end KanadeRussell.Infra
