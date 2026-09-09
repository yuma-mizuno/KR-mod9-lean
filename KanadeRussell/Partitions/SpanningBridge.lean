import KanadeRussell.Partitions.WordCorrespondence
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! The exact partition-count bound supplied by local operator reductions.
The concrete operator reductions and character formula remain separate obligations. -/
namespace KanadeRussell.Partitions
open Tsuchioka

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The actual homogeneous cyclic span, defined using all operator words. -/
def cyclicGrade (ρ : HighestWeightAction K V) (n : ℕ) : Submodule K V :=
  Submodule.span K (ρ.wordValue '' {w | w.sum = -(n:ℤ)})

theorem cyclicGrade_le_grade (ρ : HighestWeightAction K V) (n : ℕ) :
    cyclicGrade ρ n ≤ ρ.grade n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w,hw,rfl⟩
  change w.sum = -(n:ℤ) at hw
  have hh := ρ.wordValue_mem w
  simpa [hw] using hh

theorem cyclicGrade_eq_span_normal (ρ : HighestWeightAction K V) (minimum n : ℕ)
    (pairs : ∀ i j, ForbiddenPair i j → ρ.LocalReduction [i,j])
    (triples : ∀ i j k, ForbiddenTriple i j k → ρ.LocalReduction [i,j,k])
    (initial : ∀ i, -(minimum:ℤ) < i →
      ρ.wordValue [i] ∈ higherSpan (K := K) ρ.wordValue [i]) :
    cyclicGrade ρ n = Submodule.span K
      (Set.range (fun w : NormalWords minimum n => ρ.wordValue w.val)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    have hs := spanning_of_local_reductions ρ minimum pairs triples initial w
    have hi : ρ.wordValue '' {u | AdmissibleWord minimum u ∧ u.sum = w.sum} ⊆
        Set.range (fun u : NormalWords minimum n => ρ.wordValue u.val) := by
      rintro _ ⟨u,hu,rfl⟩
      exact ⟨⟨u,hu.1,hu.2.trans hw⟩,rfl⟩
    exact Submodule.span_mono hi hs
  · apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    exact Submodule.subset_span ⟨w.val,w.property.2,rfl⟩

/-- Finite-dimensionality is proved from spanning, rather than assumed. -/
theorem cyclicGrade_finite (ρ : HighestWeightAction K V) (minimum n : ℕ) (hm : 1 ≤ minimum)
    (pairs : ∀ i j, ForbiddenPair i j → ρ.LocalReduction [i,j])
    (triples : ∀ i j k, ForbiddenTriple i j k → ρ.LocalReduction [i,j,k])
    (initial : ∀ i, -(minimum:ℤ) < i →
      ρ.wordValue [i] ∈ higherSpan (K := K) ρ.wordValue [i]) :
    Module.Finite K (cyclicGrade ρ n) := by
  letI := normalWords_finite minimum n hm
  rw [cyclicGrade_eq_span_normal ρ minimum n pairs triples initial]
  exact Module.Finite.span_of_finite K (Set.finite_range _)

/-- Local relations yield the bound by the previously proved source partition count. -/
theorem finrank_cyclicGrade_le_count (ρ : HighestWeightAction K V) (minimum n : ℕ)
    (hm : 1 ≤ minimum)
    (pairs : ∀ i j, ForbiddenPair i j → ρ.LocalReduction [i,j])
    (triples : ∀ i j k, ForbiddenTriple i j k → ρ.LocalReduction [i,j,k])
    (initial : ∀ i, -(minimum:ℤ) < i →
      ρ.wordValue [i] ∈ higherSpan (K := K) ρ.wordValue [i]) :
    Module.finrank K (cyclicGrade ρ n) ≤ count minimum n := by
  letI := normalWords_finite minimum n hm
  letI : Fintype (NormalWords minimum n) := Fintype.ofFinite _
  rw [cyclicGrade_eq_span_normal ρ minimum n pairs triples initial]
  calc
    Module.finrank K (Submodule.span K (Set.range (fun w : NormalWords minimum n => ρ.wordValue w.val)))
      ≤ Fintype.card (NormalWords minimum n) := finrank_range_le_card _
    _ = count minimum n := by rw [← Nat.card_eq_fintype_card,normalWords_card]

end KanadeRussell.Partitions
