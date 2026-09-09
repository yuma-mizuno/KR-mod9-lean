import KanadeRussell.Representation.RankOneLocalFiniteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! In a finite-dimensional space, pointwise nilpotence gives a uniform
nilpotence bound equal to the dimension. -/
namespace KanadeRussell.Representation
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem pow_finrank_eq_zero_of_locallyNilpotent (A : Module.End K V)
    (hA : ∀ v : V, ∃ n : ℕ, (A^n) v = 0) : A^(Module.finrank K V) = 0 := by
  ext v
  obtain ⟨n, hn⟩ := hA v
  exact Module.End.ker_pow_le_ker_pow_finrank A n hn

theorem isNilpotent_of_locallyNilpotent (A : Module.End K V)
    (hA : ∀ v : V, ∃ n : ℕ, (A^n) v = 0) : IsNilpotent A :=
  ⟨Module.finrank K V, pow_finrank_eq_zero_of_locallyNilpotent A hA⟩

end KanadeRussell.Representation
