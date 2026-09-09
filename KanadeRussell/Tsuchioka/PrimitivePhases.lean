import KanadeRussell.Tsuchioka.ScalarFactors

/-! Distinctness of the phases occurring in the rational scalar factors. -/

namespace KanadeRussell.Tsuchioka.Coefficients

variable {K : Type*} [Field K] [CharZero K]

theorem cyclotomic_twelve :
    Polynomial.cyclotomic 12 K = Polynomial.X ^ 4 - Polynomial.X ^ 2 + 1 := by
  have he := Polynomial.cyclotomic_expand_eq_cyclotomic
    (p := 2) (n := 6) Nat.prime_two (by norm_num) K
  rw [← he, Polynomial.cyclotomic_six]
  simp [map_sub, map_add, map_pow, Polynomial.expand_X] <;> ring

/-- The polynomial hypothesis really gives a primitive twelfth root. -/
theorem primitive_root (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    IsPrimitiveRoot w 12 := by
  apply (Polynomial.isRoot_cyclotomic_iff_charZero (by decide : 0 < 12)).mp
  rw [cyclotomic_twelve]
  simpa [Polynomial.IsRoot.def] using hw

/-- All twelve possible pole phases are distinct. -/
theorem phases_injective (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    Function.Injective (fun p : Fin 12 => w ^ p.val) := by
  intro p q hpq
  exact Fin.ext ((primitive_root w hw).pow_inj p.isLt q.isLt hpq)

end KanadeRussell.Tsuchioka.Coefficients
