import KanadeRussell.Source.LongFunctional
import KanadeRussell.Source.ShortRows
set_option backward.isDefEq.respectTransparency false

/-! The short theta functionals: odd projection and cleared Euler rows. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Source
open Infra

private theorem twist_inv_even (d n : ℕ) (hd : 0 < d) :
    twist (bInv (q ^ (2 * d); q ^ (2 * d))_n) = bInv (q ^ (2 * d); q ^ (2 * d))_n := by
  have hu : IsUnit (q ^ (2 * d); q ^ (2 * d))_n :=
    isUnit_qPochhammer (by simp [q, hd.ne']) (by simp [q, hd.ne']) n
  rw [hu.map_bInv, map_qPochhammer, twist_even_q_pow]

private def shortLattice (a : ℕ) (p : (ℕ × ℤ) × ℕ) : ℤ × (ℕ × ℕ) :=
  (3 * (p.1.1 : ℤ) + 2 * a - 1 + 2 * p.1.2 - p.2, (p.2, p.1.1))

private theorem shortLattice_injective (a : ℕ) : Function.Injective (shortLattice a) := by
  rintro ⟨⟨n, ν⟩, m⟩ ⟨⟨s, μ⟩, r⟩ h
  simp only [shortLattice, Prod.mk.injEq] at h ⊢
  omega

private def shortFullExponent (a : ℕ) (k : ℤ) (m n : ℕ) : ℕ :=
  k.natAbs ^ 2 + m ^ 2 + 3 * n ^ 2 + 6 * n + 6 * m * n + 4 * a * m

private noncomputable def shortRaw (a : ℕ) (p : ℤ × (ℕ × ℕ)) : QSeries :=
  (-1) ^ p.2.1 * q ^ shortFullExponent a p.1 p.2.1 p.2.2 *
    bInv (q ^ 4; q ^ 4)_p.2.1 * bInv (q ^ 12; q ^ 12)_p.2.2

private theorem hasSum_shortRaw (a : ℕ) : HasSum (shortRaw a) (theta 1 * uAt a) := by
  have h := (summable_theta 1 (by decide)).hasSum.mul_of_nonarchimedean' (hasSum_uAt a)
  apply h.congr_fun
  rintro ⟨k, m, n⟩
  simp only [shortRaw, shortFullExponent, uTerm, pow_add, one_mul, pow_mul]
  ring

private noncomputable def shortOdd (a : ℕ) (p : ℤ × (ℕ × ℕ)) : QSeries :=
  shortRaw a p - twist (shortRaw a p)

private theorem shortOdd_expand (a : ℕ) (k : ℤ) (m n : ℕ) :
    shortOdd a (k, m, n) = (-1) ^ m *
      (q ^ shortFullExponent a k m n - (-q) ^ shortFullExponent a k m n) *
        bInv (q ^ 4; q ^ 4)_m * bInv (q ^ 12; q ^ 12)_n := by
  simp only [shortOdd, shortRaw, map_mul]
  rw [twist_inv_even 2 m (by decide), twist_inv_even 6 n (by decide)]
  rw [map_pow twist, map_pow twist, map_neg, map_one, show twist q = -q by simp [twist, q]]
  ring

private theorem square_mod_two (z : ℤ) : z ^ 2 % 2 = z % 2 := by
  rcases Int.emod_two_eq_zero_or_one z with h | h <;> simp [pow_two, Int.mul_emod, h]

private theorem shortFullExponent_parity (a : ℕ) (k : ℤ) (m n : ℕ) :
    (shortFullExponent a k m n : ℤ) % 2 = (k + m + n) % 2 := by
  have he : (shortFullExponent a k m n : ℤ) =
      k ^ 2 + (m : ℤ) ^ 2 + 3 * (n : ℤ) ^ 2 + 6 * n + 6 * m * n + 4 * a * m := by
    simp [shortFullExponent]
  rw [he]
  simp [Int.add_emod, Int.mul_emod, square_mod_two]

private theorem shortOdd_off (a : ℕ) (p : ℤ × (ℕ × ℕ)) (h : p ∉ Set.range (shortLattice a)) :
    shortOdd a p = 0 := by
  rcases p with ⟨k, m, n⟩
  have hpar : (k + m - 3 * n - 2 * a + 1) % 2 ≠ 0 := by
    intro hp
    apply h
    refine ⟨((n, (k + m - 3 * n - 2 * a + 1) / 2), m), ?_⟩
    have he := Int.mul_ediv_add_emod (k + m - 3 * n - 2 * a + 1) 2
    apply Prod.ext
    · dsimp [shortLattice]; omega
    · rfl
  have heven : Even (shortFullExponent a k m n) := by
    rw [Nat.even_iff]
    have hp := shortFullExponent_parity a k m n
    omega
  rw [shortOdd_expand, heven.neg_pow, sub_self]
  ring

private theorem shortOdd_lattice (a n : ℕ) (ν : ℤ) (m : ℕ) :
    shortOdd a (shortLattice a ((n, ν), m)) =
      2 * bInv (q ^ 12; q ^ 12)_n * shortRowTerm a n ν m := by
  have he : shortFullExponent a (3 * (n : ℤ) + 2 * a - 1 + 2 * ν - m) m n =
      shortExponent a n ν m := by simp only [shortFullExponent, shortExponent]; ring
  have hodd : Odd (shortFullExponent a (3 * (n : ℤ) + 2 * a - 1 + 2 * ν - m) m n) := by
    rw [Nat.odd_iff]
    have hp := shortFullExponent_parity a (3 * (n : ℤ) + 2 * a - 1 + 2 * ν - m) m n
    omega
  change shortOdd a ((3 * (n : ℤ) + 2 * a - 1 + 2 * ν - m), m, n) = _
  rw [shortOdd_expand, hodd.neg_pow, he, shortRowTerm]
  ring

private def negativeShortRow (nr : ℕ × ℕ) : ℕ × ℤ := (nr.1, -(nr.2 : ℤ))

private theorem negativeShortRow_injective : Function.Injective negativeShortRow := by
  rintro ⟨m, r⟩ ⟨n, s⟩ h
  simp only [negativeShortRow, Prod.mk.injEq] at h ⊢
  omega

private theorem shortRows_off (a : ℕ) (p : ℕ × ℤ) (h : p ∉ Set.range negativeShortRow) :
    2 * bInv (q ^ 12; q ^ 12)_p.1 * shortRow a p.1 p.2 = 0 := by
  have hp : 0 < p.2 := by
    by_contra hn
    apply h
    refine ⟨(p.1, (-p.2).toNat), ?_⟩
    have he := Int.toNat_of_nonneg (show 0 ≤ -p.2 by omega)
    apply Prod.ext
    · rfl
    · dsimp [negativeShortRow]; omega
  have he : p.2 = ((p.2 - 1).toNat : ℤ) + 1 := by
    have hh := Int.toNat_of_nonneg (show 0 ≤ p.2 - 1 by omega)
    omega
  rw [he, shortRow_positive]
  ring

noncomputable def shortSurvivor (a : ℕ) (nr : ℕ × ℕ) : QSeries :=
  2 * bInv (q ^ 12; q ^ 12)_nr.1 *
    (q ^ shortExponent a nr.1 (-(nr.2 : ℤ)) 0 * (q ^ 4; q ^ 4)_∞ * bInv (q ^ 4; q ^ 4)_nr.2)

/-- The odd theta product is the convergent sum of its surviving Euler rows. -/
theorem hasSum_shortSurvivor (a : ℕ) : HasSum (shortSurvivor a)
    (theta 1 * uAt a - twist (theta 1) * twist (uAt a)) := by
  have hraw := hasSum_shortRaw a
  have he : HasSum (shortOdd a) (theta 1 * uAt a - twist (theta 1) * twist (uAt a)) := by
    change HasSum (fun p => shortRaw a p - twist (shortRaw a p)) _
    simpa only [Function.comp_def, map_mul] using hraw.sub (hraw.map twist twist_continuous)
  have hlat := ((shortLattice_injective a).hasSum_iff (shortOdd_off a)).mpr he
  have hrows : HasSum
      (fun p : (ℕ × ℤ) × ℕ => 2 * bInv (q ^ 12; q ^ 12)_p.1.1 * shortRowTerm a p.1.1 p.1.2 p.2)
      (theta 1 * uAt a - twist (theta 1) * twist (uAt a)) :=
    hlat.congr_fun (fun p => (shortOdd_lattice a p.1.1 p.1.2 p.2).symm)
  have hr : HasSum (fun p : ℕ × ℤ => 2 * bInv (q ^ 12; q ^ 12)_p.1 * shortRow a p.1 p.2)
      (theta 1 * uAt a - twist (theta 1) * twist (uAt a)) := by
    apply hrows.prod_fiberwise
    intro p
    have hp : HasSum (shortRowTerm a p.1 p.2) (shortRow a p.1 p.2) :=
      (summable_shortRow a p.1 p.2).hasSum
    exact hp.mul_left (2 * bInv (q ^ 12; q ^ 12)_p.1)
  have hn := (negativeShortRow_injective.hasSum_iff (shortRows_off a)).mpr hr
  apply hn.congr_fun
  intro nr
  simp only [shortSurvivor, Function.comp_def, negativeShortRow, shortRow_negative]

private theorem baseChange_E_one : baseChange (E 1) = (q ^ 4; q ^ 4)_∞ := by
  rw [E, map_qPochhammerInf baseChange baseChange_continuous (q ^ 1) (by simp [q])]
  simp only [pow_one, q, baseChange_X]

private theorem shortSurvivor_zero (n r : ℕ) : shortSurvivor 0 (n, r) =
    2 * q * baseChange (E 1) * baseChange (q ^ r * reflectedTerm (r, n)) := by
  have hu : IsUnit (q; q)_r := by simpa using isUnit_qPochhammer_q 0 r
  have hv : IsUnit (q ^ 3; q ^ 3)_n := by simpa using isUnit_qPochhammer_q 2 n
  rw [shortSurvivor, shortExponent_zero_negative, baseChange_E_one]
  simp only [reflectedTerm, map_mul, map_pow]
  rw [hu.map_bInv, hv.map_bInv, map_qPochhammer, map_qPochhammer]
  simp only [map_pow, q, baseChange_X, pow_add, pow_mul]
  ring_nf

private theorem shortSurvivor_one (n r : ℕ) : shortSurvivor 1 (n, r) =
    2 * q * baseChange (E 1) * baseChange (minusTerm (r, n)) := by
  have hu : IsUnit (q; q)_r := by simpa using isUnit_qPochhammer_q 0 r
  have hv : IsUnit (q ^ 3; q ^ 3)_n := by simpa using isUnit_qPochhammer_q 2 n
  rw [shortSurvivor, shortExponent_one_negative, baseChange_E_one]
  simp only [minusTerm, map_mul, map_pow]
  rw [hu.map_bInv, hv.map_bInv, map_qPochhammer, map_qPochhammer]
  simp only [map_pow, q, baseChange_X, pow_add, pow_mul]
  ring_nf

theorem short_functional_one :
    theta 1 * uOne - twist (theta 1) * twist uOne = 2 * q * baseChange (E 1 * Wval) := by
  have h := ((summable_series_mul summable_reflectedTerm (fun mn => q ^ mn.1)).hasSum.map
    baseChange baseChange_continuous).mul_left (2 * q * baseChange (E 1))
  have hb := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr h
  have ht := hb.congr_fun (fun nr => shortSurvivor_zero nr.1 nr.2)
  have he := (hasSum_shortSurvivor 0).unique ht
  simpa only [uAt_zero, Wval, map_mul, mul_assoc] using he

theorem short_functional_five :
    theta 1 * uFive - twist (theta 1) * twist uFive = 2 * q * baseChange (E 1 * Vval) := by
  have h := (summable_minusTerm.hasSum.map baseChange baseChange_continuous).mul_left
    (2 * q * baseChange (E 1))
  have hb := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr h
  have ht := hb.congr_fun (fun nr => shortSurvivor_one nr.1 nr.2)
  have he := (hasSum_shortSurvivor 1).unique ht
  simpa only [uAt_one, Vval, map_mul, mul_assoc] using he

end KanadeRussell.Source
