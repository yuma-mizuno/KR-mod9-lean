import KanadeRussell.Source.U
import KanadeRussell.Source.LongRows
set_option backward.isDefEq.respectTransparency false

/-! The long theta functionals: parity reindexing followed by cleared Euler rows. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Source
open Infra

noncomputable def uAt (a : ℕ) : QSeries := ∑' mn : ℕ × ℕ, (q ^ 4) ^ (a * mn.1) * uTerm mn

theorem hasSum_uAt (a : ℕ) :
    HasSum (fun mn : ℕ × ℕ => (q ^ 4) ^ (a * mn.1) * uTerm mn) (uAt a) :=
  (summable_series_mul summable_uTerm (fun mn => (q ^ 4) ^ (a * mn.1))).hasSum

@[simp] theorem uAt_zero : uAt 0 = uOne := by simp [uAt, uOne]
@[simp] theorem uAt_one : uAt 1 = uFive := by simp [uAt, uFive]

@[simp] theorem twist_twist (f : QSeries) : twist (twist f) = f := by
  simp [twist, rescale_rescale]

private theorem twist_inv_even (d n : ℕ) (hd : 0 < d) :
    twist (bInv (q ^ (2 * d); q ^ (2 * d))_n) = bInv (q ^ (2 * d); q ^ (2 * d))_n := by
  have hu : IsUnit (q ^ (2 * d); q ^ (2 * d))_n :=
    isUnit_qPochhammer (by simp [q, hd.ne']) (by simp [q, hd.ne']) n
  rw [hu.map_bInv, map_qPochhammer, twist_even_q_pow]

private def longLattice (p : (ℕ × ℤ) × ℕ) : ℤ × (ℕ × ℕ) :=
  ((p.1.1 : ℤ) - p.2 + 2 * p.1.2, (p.1.1, p.2))

private theorem longLattice_injective : Function.Injective longLattice := by
  rintro ⟨⟨m, ν⟩, n⟩ ⟨⟨r, μ⟩, s⟩ h
  simp only [longLattice, Prod.mk.injEq] at h ⊢
  omega

private def longFullExponent (k : ℤ) (m n : ℕ) : ℕ :=
  3 * k.natAbs ^ 2 + m ^ 2 + 3 * n ^ 2 + 6 * n + 6 * m * n

private noncomputable def longRaw (a : ℕ) (p : ℤ × (ℕ × ℕ)) : QSeries :=
  (-1) ^ (3 * p.1.natAbs ^ 2 + p.2.1) * q ^ longFullExponent p.1 p.2.1 p.2.2 *
    (q ^ 4) ^ (a * p.2.1) * bInv (q ^ 4; q ^ 4)_p.2.1 * bInv (q ^ 12; q ^ 12)_p.2.2

private theorem hasSum_longRaw (a : ℕ) : HasSum (longRaw a) (twist (theta 3) * uAt a) := by
  have h := ((summable_theta 3 (by decide)).hasSum.map twist twist_continuous).mul_of_nonarchimedean'
    (hasSum_uAt a)
  apply h.congr_fun
  rintro ⟨k, m, n⟩
  simp only [longRaw, longFullExponent, Function.comp_def, twist, map_pow,
    rescale_neg_one_X, uTerm, pow_add]
  rw [neg_eq_neg_one_mul (q : QSeries), mul_pow]
  ring

private noncomputable def longEven (a : ℕ) (p : ℤ × (ℕ × ℕ)) : QSeries :=
  longRaw a p + twist (longRaw a p)

private theorem longEven_expand (a : ℕ) (k : ℤ) (m n : ℕ) :
    longEven a (k, m, n) =
      (-1) ^ (3 * k.natAbs ^ 2 + m) *
        (q ^ longFullExponent k m n + (-q) ^ longFullExponent k m n) *
        (q ^ 4) ^ (a * m) * bInv (q ^ 4; q ^ 4)_m * bInv (q ^ 12; q ^ 12)_n := by
  simp only [longEven, longRaw, map_mul]
  rw [twist_inv_even 2 m (by decide), twist_inv_even 6 n (by decide)]
  rw [map_pow twist, map_pow twist, map_pow twist, map_neg, map_one,
    show twist q = -q by simp [twist, q], twist_q_four]
  ring

private theorem square_mod_two (z : ℤ) : z ^ 2 % 2 = z % 2 := by
  rcases Int.emod_two_eq_zero_or_one z with h | h <;> simp [pow_two, Int.mul_emod, h]

private theorem longFullExponent_parity (k : ℤ) (m n : ℕ) :
    (longFullExponent k m n : ℤ) % 2 = (k + m + n) % 2 := by
  have he : (longFullExponent k m n : ℤ) =
      3 * k ^ 2 + (m : ℤ) ^ 2 + 3 * (n : ℤ) ^ 2 + 6 * n + 6 * m * n := by
    simp [longFullExponent]
  rw [he]
  simp [Int.add_emod, Int.mul_emod, square_mod_two]

private theorem longEven_off (a : ℕ) (p : ℤ × (ℕ × ℕ)) (h : p ∉ Set.range longLattice) :
    longEven a p = 0 := by
  rcases p with ⟨k, m, n⟩
  have hpar : (k - m + n) % 2 ≠ 0 := by
    intro hp
    apply h
    refine ⟨((m, (k - m + n) / 2), n), ?_⟩
    have he := Int.mul_ediv_add_emod (k - m + n) 2
    apply Prod.ext
    · dsimp [longLattice]; omega
    · rfl
  have hodd : Odd (longFullExponent k m n) := by
    rw [Nat.odd_iff]
    have hp := longFullExponent_parity k m n
    omega
  rw [longEven_expand, hodd.neg_pow, add_neg_cancel]
  ring

private theorem longEven_lattice (a m : ℕ) (ν : ℤ) (n : ℕ) :
    longEven a (longLattice ((m, ν), n)) =
      2 * (q ^ 4) ^ (a * m) * bInv (q ^ 4; q ^ 4)_m * longRowTerm m ν n := by
  have he : longFullExponent ((m : ℤ) - n + 2 * ν) m n = longExponent m ν n := by
    simp only [longFullExponent, longExponent]; ring
  have heven : Even (longFullExponent ((m : ℤ) - n + 2 * ν) m n) := by
    rw [Nat.even_iff]
    have hp := longFullExponent_parity ((m : ℤ) - n + 2 * ν) m n
    omega
  have hs : (3 * ((m : ℤ) - n + 2 * ν).natAbs ^ 2 + m) % 2 = n % 2 := by
    have ht : ((3 * ((m : ℤ) - n + 2 * ν).natAbs ^ 2 + m : ℕ) : ℤ) =
        3 * ((m : ℤ) - n + 2 * ν) ^ 2 + m := by simp
    have hp : (3 * ((m : ℤ) - n + 2 * ν) ^ 2 + m) % 2 = (n : ℤ) % 2 := by
      simp [Int.add_emod, Int.mul_emod, square_mod_two]
      omega
    omega
  have hsign : (-1 : QSeries) ^ (3 * ((m : ℤ) - n + 2 * ν).natAbs ^ 2 + m) = (-1) ^ n := by
    rw [neg_one_pow_eq_pow_mod_two, hs, ← neg_one_pow_eq_pow_mod_two]
  change longEven a (((m : ℤ) - n + 2 * ν), m, n) = _
  rw [longEven_expand, heven.neg_pow, hsign, he, longRowTerm]
  ring

private def negativeRow (mr : ℕ × ℕ) : ℕ × ℤ := (mr.1, -(mr.2 : ℤ))

private theorem negativeRow_injective : Function.Injective negativeRow := by
  rintro ⟨m, r⟩ ⟨n, s⟩ h
  simp only [negativeRow, Prod.mk.injEq] at h ⊢
  omega

private theorem longRows_off (a : ℕ) (p : ℕ × ℤ) (h : p ∉ Set.range negativeRow) :
    2 * (q ^ 4) ^ (a * p.1) * bInv (q ^ 4; q ^ 4)_p.1 * longRow p.1 p.2 = 0 := by
  have hp : 0 < p.2 := by
    by_contra hn
    apply h
    refine ⟨(p.1, (-p.2).toNat), ?_⟩
    have he := Int.toNat_of_nonneg (show 0 ≤ -p.2 by omega)
    apply Prod.ext
    · rfl
    · dsimp [negativeRow]; omega
  have he : p.2 = ((p.2 - 1).toNat : ℤ) + 1 := by
    have hh := Int.toNat_of_nonneg (show 0 ≤ p.2 - 1 by omega)
    omega
  rw [he, longRow_positive]
  ring

private theorem baseChange_E_three : baseChange (E 3) = (q ^ 12; q ^ 12)_∞ := by
  rw [E, map_qPochhammerInf baseChange baseChange_continuous (q ^ 3) (by simp [q])]
  simp only [map_pow, q, baseChange_X, ← pow_mul, Nat.reduceMul]

private theorem longRow_surviving (a m r : ℕ) :
    2 * (q ^ 4) ^ (a * m) * bInv (q ^ 4; q ^ 4)_m * longRow m (-(r : ℤ)) =
      2 * baseChange (E 3) * baseChange (q ^ (a * m) * reflectedTerm (m, r)) := by
  have hu : IsUnit (q; q)_m := by simpa using isUnit_qPochhammer_q 0 m
  have hv : IsUnit (q ^ 3; q ^ 3)_r := by simpa using isUnit_qPochhammer_q 2 r
  rw [longRow_negative, baseChange_E_three]
  simp only [reflectedTerm, map_mul, map_pow]
  rw [hu.map_bInv, hv.map_bInv, map_qPochhammer, map_qPochhammer]
  simp only [map_pow, q, baseChange_X, ← pow_mul, Nat.reduceMul]
  ring

set_option maxHeartbeats 800000 in
/-- Both long theta functionals at once; a = 0 gives U and a = 1 gives W. -/
theorem long_functional (a : ℕ) :
    twist (theta 3) * uAt a + theta 3 * twist (uAt a) =
      2 * baseChange (E 3 * ∑' mn : ℕ × ℕ, q ^ (a * mn.1) * reflectedTerm mn) := by
  have hraw := hasSum_longRaw a
  have he : HasSum (longEven a) (twist (theta 3) * uAt a + theta 3 * twist (uAt a)) := by
    change HasSum (fun p => longRaw a p + twist (longRaw a p)) _
    simpa only [Function.comp_def, map_mul, twist_twist] using
      hraw.add (hraw.map twist twist_continuous)
  have hlat := (longLattice_injective.hasSum_iff (longEven_off a)).mpr he
  have hrows : HasSum
      (fun p : (ℕ × ℤ) × ℕ =>
        2 * (q ^ 4) ^ (a * p.1.1) * bInv (q ^ 4; q ^ 4)_p.1.1 * longRowTerm p.1.1 p.1.2 p.2)
      (twist (theta 3) * uAt a + theta 3 * twist (uAt a)) :=
    hlat.congr_fun (fun p => (longEven_lattice a p.1.1 p.1.2 p.2).symm)
  have hr : HasSum (fun p : ℕ × ℤ =>
      2 * (q ^ 4) ^ (a * p.1) * bInv (q ^ 4; q ^ 4)_p.1 * longRow p.1 p.2)
      (twist (theta 3) * uAt a + theta 3 * twist (uAt a)) := by
    apply hrows.prod_fiberwise
    intro p
    have hp : HasSum (longRowTerm p.1 p.2) (longRow p.1 p.2) :=
      (summable_longRow p.1 p.2).hasSum
    exact hp.mul_left (2 * (q ^ 4) ^ (a * p.1) * bInv (q ^ 4; q ^ 4)_p.1)
  have hn := (negativeRow_injective.hasSum_iff (longRows_off a)).mpr hr
  have hb := ((summable_series_mul summable_reflectedTerm (fun mn => q ^ (a * mn.1))).hasSum.map
    baseChange baseChange_continuous).mul_left (2 * baseChange (E 3))
  have hh : HasSum
      ((fun p : ℕ × ℤ => 2 * (q ^ 4) ^ (a * p.1) * bInv (q ^ 4; q ^ 4)_p.1 * longRow p.1 p.2) ∘ negativeRow)
      (2 * baseChange (E 3 * ∑' mn : ℕ × ℕ, q ^ (a * mn.1) * reflectedTerm mn)) := by
    simpa only [map_mul, mul_assoc, Function.comp_def, negativeRow] using
      hb.congr_fun (fun mr => longRow_surviving a mr.1 mr.2)
  exact hn.unique hh

theorem long_functional_one :
    twist (theta 3) * uOne + theta 3 * twist uOne = 2 * baseChange (E 3 * Uval) := by
  simpa only [uAt_zero, Nat.zero_mul, pow_zero, one_mul, Uval] using long_functional 0

theorem long_functional_five :
    twist (theta 3) * uFive + theta 3 * twist uFive = 2 * baseChange (E 3 * Wval) := by
  simpa only [uAt_one, Nat.one_mul, Wval] using long_functional 1

end KanadeRussell.Source
