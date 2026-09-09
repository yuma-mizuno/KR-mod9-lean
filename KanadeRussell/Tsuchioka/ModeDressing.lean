import KanadeRussell.Tsuchioka.DressingCoefficients
import KanadeRussell.Tsuchioka.TensorHeisenberg
import KanadeRussell.Tsuchioka.OscillatorCyclicity

/-! Finite coefficientwise transfer between tensor root modes and Z modes,
and stability of the negative-Heisenberg span under the tensor fields. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

theorem tensorRootMode_mem_of_rootModes (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : RootData.Lattice) (S : Submodule K (Space K))
    (hS : ∀ n g, g ∈ S → heisenbergNegative n g ∈ S)
    (f : Space K) (hf : f ∈ heisenbergVacuum w)
    (hZ : ∀ j : ℤ, rootMode w β j f ∈ S) (i : ℤ) :
    tensorRootMode w β i f ∈ S := by
  change (tensorRootField w β f).coeff (-i) ∈ S
  rw [tensorRootField_on_vacuum w hw β f hf]
  apply diagonalRootCreation_mul_coeff_mem w β S hS
  intro d
  have h := hZ (-d)
  change (rootField w β f).coeff (-(-d)) ∈ S at h
  simpa only [neg_neg] using h

theorem rootMode_mem_of_tensorRootModes (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : RootData.Lattice) (S : Submodule K (Space K))
    (hS : ∀ n g, g ∈ S → heisenbergNegative n g ∈ S)
    (f : Space K) (hf : f ∈ heisenbergVacuum w)
    (hX : ∀ j : ℤ, tensorRootMode w β j f ∈ S) (i : ℤ) :
    rootMode w β i f ∈ S := by
  change (rootField w β f).coeff (-i) ∈ S
  rw [rootField_eq_inverse_tensorRootField_on_vacuum w hw β f hf]
  apply inverseDiagonalRootCreation_mul_coeff_mem w β S hS
  intro d
  have h := hX (-d)
  change (tensorRootField w β f).coeff (-(-d)) ∈ S at h
  simpa only [neg_neg] using h

/-- The transfer extends from vacuum vectors to all finite negative
Heisenberg words by the exact tensor-root commutator, at every index. -/
theorem tensorRootMode_mem_heisenbergSpan (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : RootData.Lattice) (S : Submodule K (Space K))
    (hS : S ≤ heisenbergVacuum w)
    (hZ : ∀ i f, f ∈ S → rootMode w β i f ∈ S)
    (i : ℤ) (f : Space K) (hf : f ∈ heisenbergSpan S) :
    tensorRootMode w β i f ∈ heisenbergSpan S := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨u, s⟩, rfl⟩ := hf
    dsimp only
    induction u generalizing i with
    | nil =>
      rw [heisenbergWord_nil]
      exact tensorRootMode_mem_of_rootModes w hw β (heisenbergSpan S)
        (heisenbergNegative_mem_span S) s.val (hS s.property)
        (fun j => le_heisenbergSpan S (hZ j s.val s.property)) i
    | cons n u ih =>
      rw [heisenbergWord_cons, tensorRootMode_heisenbergNegative]
      exact (heisenbergSpan S).sub_mem
        (heisenbergNegative_mem_span S n _ (ih i))
        ((heisenbergSpan S).smul_mem _ (ih (i - n.val)))
  | zero => simp
  | add f g hf hg hif hig =>
    simpa only [map_add] using (heisenbergSpan S).add_mem hif hig
  | smul c f hf hi =>
    simpa only [map_smul] using (heisenbergSpan S).smul_mem c hi

theorem tensorRootMode_mem_heisenbergSpan_zCyclicSpan (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (seed : Space K) (hseed : seed ∈ heisenbergVacuum w)
    (β : RootData.Root) (i : ℤ) (f : Space K) (hf : f ∈ heisenbergSpan (zCyclicSpan w seed)) :
    tensorRootMode w β.val i f ∈ heisenbergSpan (zCyclicSpan w seed) :=
  tensorRootMode_mem_heisenbergSpan w hw β.val (zCyclicSpan w seed)
    (zCyclicSpan_le_heisenbergVacuum w seed hseed) (rootMode_mem_zCyclicSpan w seed β) i f hf

end KanadeRussell.Tsuchioka.Fock
