import KanadeRussell.Product.Defs

/-! Convergent Lambert series and the residue trace used in the product route. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Product

noncomputable def lambertTerm (k : ℕ) : PowerSeries ℤ :=
  if k = 0 then 0 else q ^ k * bInv (1 - q ^ k) ^ 2

noncomputable def lambert (d : ℕ) : PowerSeries ℤ := ∑' k : ℕ, lambertTerm (d * k)

noncomputable def lambertResidue (r : ℕ) : PowerSeries ℤ :=
  ∑' k : ℕ, if k % 9 = r ∨ k % 9 = 9 - r then lambertTerm k else 0

theorem summable_lambertTerm : Summable lambertTerm := by
  apply (summable_iff_summable_coeff _).mpr
  intro n
  apply summable_of_hasFiniteSupport
  apply (Set.finite_Iic n).subset
  intro k hk
  by_contra h
  apply hk
  simp only [lambertTerm]
  split_ifs with hk0
  · simp
  · simp [q, coeff_X_pow_mul', show ¬ k ≤ n from h]

theorem summable_lambert (d : ℕ) (hd : 0 < d) :
    Summable (fun k => lambertTerm (d * k)) := by
  exact summable_lambertTerm.comp_injective (by intro i j h; exact Nat.eq_of_mul_eq_mul_left hd h)

theorem hasSum_lambert_multiples (d : ℕ) (hd : 0 < d) :
    HasSum (fun k => if d ∣ k then lambertTerm k else 0) (lambert d) := by
  have hinj : Function.Injective (fun k : ℕ => d * k) := by
    intro i j h
    exact Nat.eq_of_mul_eq_mul_left hd h
  apply (hinj.hasSum_iff ?_).mp
  · simpa [Function.comp_def, lambert] using (summable_lambert d hd).hasSum
  · intro k hk
    have hn : ¬ d ∣ k := by
      rintro ⟨m, hm⟩
      exact hk ⟨m, hm.symm⟩
    simp [hn]

theorem hasSum_lambertResidue (r : ℕ) :
    HasSum (fun k => if k % 9 = r ∨ k % 9 = 9 - r then lambertTerm k else 0)
      (lambertResidue r) := by
  have hs := summable_lambertTerm.indicator {k | k % 9 = r ∨ k % 9 = 9 - r}
  have ht : Summable (fun k => if k % 9 = r ∨ k % 9 = 9 - r then lambertTerm k else 0) :=
    hs.congr (fun k => by simp [Set.indicator_apply])
  exact ht.hasSum

/-- The three differences of elliptic Lambert series are a divisor trace.
This theorem uses only convergent summation and residue arithmetic. -/
theorem lambert_residue_trace :
    lambertResidue 1 + lambertResidue 2 + lambertResidue 4 - 3 * lambertResidue 3 =
      lambert 1 - 4 * lambert 3 + 3 * lambert 9 := by
  have hs := (((hasSum_lambertResidue 1).add (hasSum_lambertResidue 2)).add
    (hasSum_lambertResidue 4)).sub ((hasSum_lambertResidue 3).mul_left 3)
  have ht := ((hasSum_lambert_multiples 1 (by decide)).sub
    ((hasSum_lambert_multiples 3 (by decide)).mul_left 4)).add
    ((hasSum_lambert_multiples 9 (by decide)).mul_left 3)
  apply hs.unique
  apply ht.congr_fun
  intro k
  norm_num only [Nat.reduceSub, one_dvd, ite_true]
  have h9 : k % 9 < 9 := Nat.mod_lt _ (by decide)
  have h3 : 3 ∣ k ↔ k % 3 = 0 := Nat.dvd_iff_mod_eq_zero
  have hdiv9 : 9 ∣ k ↔ k % 9 = 0 := Nat.dvd_iff_mod_eq_zero
  simp only [Nat.dvd_iff_mod_eq_zero]
  split_ifs <;> first | omega | ring

end KanadeRussell.Product
