import KanadeRussell.Product.Lambert
set_option backward.isDefEq.respectTransparency false

/-! Reindexing the residue Lambert series into its two arithmetic progressions. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Product

noncomputable def lambertProgression (r : ℕ) : PowerSeries ℤ :=
  ∑' n : ℕ, lambertTerm (r + 9*n)

theorem summable_lambertProgression (r : ℕ) :
    Summable (fun n : ℕ => lambertTerm (r + 9*n)) :=
  summable_lambertTerm.comp_injective (by intro m n h; dsimp at h; omega)

theorem hasSum_lambertProgression (r : ℕ) (hr : r < 9) :
    HasSum (fun k => if k % 9 = r then lambertTerm k else 0) (lambertProgression r) := by
  have hinj : Function.Injective (fun n : ℕ => r+9*n) := by intro m n h; dsimp at h; omega
  apply (hinj.hasSum_iff ?_).mp
  · simpa [Function.comp_def, Nat.add_mod, Nat.mod_eq_of_lt hr, lambertProgression] using
      (summable_lambertProgression r).hasSum
  · intro k hk
    have hn : k % 9 ≠ r := by
      intro heq
      apply hk
      refine ⟨k / 9, ?_⟩
      change r + 9*(k/9) = k
      omega
    simp [hn]

/-- The two progressions are disjoint because nine is odd. -/
theorem lambertResidue_eq_progressions (r : ℕ) (hr : 0 < r) (hr9 : r < 9) :
    lambertResidue r = lambertProgression r + lambertProgression (9-r) := by
  have h := (hasSum_lambertProgression r hr9).add
    (hasSum_lambertProgression (9-r) (by omega))
  apply (hasSum_lambertResidue r).unique
  apply h.congr_fun
  intro k
  split_ifs <;> first | omega | simp_all

end KanadeRussell.Product
