import KanadeRussell.Representation.ChevalleyQuotient
import KanadeRussell.Heisenberg.ShiftedTensorVacuum

/-! Degreewise vacuum lifting for every homogeneous vacuum seed in every
Chevalley-stable ambient quotient. Degrees are measured relative to the seed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Tsuchioka.Fock
open KanadeRussell.Heisenberg
variable {K : Type*} [Field K] [CharZero K]

noncomputable def shiftedQuotientCyclicGrade (w : K) (seed : Space K) (d : ℤ)
    (S : Submodule K (Space K)) (n : ℕ) : Submodule K (Space K ⧸ S) :=
  (tensorCyclicSpan w seed ⊓ grade (d+n)).map S.mkQ

/-- Vacuum vectors in the quotient lift to vacuum vectors in the same absolute degree. -/
theorem shiftedQuotientCyclicGrade_vacuum_eq (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (S : Submodule K (Space K))
    (hS : ChevalleyStable w S) (n : ℕ) :
    (((tensorCyclicSpan w seed ⊓ heisenbergVacuum w) ⊓ grade (d+n)).map S.mkQ) =
      shiftedQuotientCyclicGrade w seed d S n ⊓ vacuum (quotientAnnihilate w hw S hS) := by
  let f : tensorCyclicSpan w seed →ₗ[K] (Space K ⧸ S) :=
    S.mkQ.comp (tensorCyclicSpan w seed).subtype
  have hmap : ((tensorCyclicGrading w hw seed).grade (d+n)).map f =
      shiftedQuotientCyclicGrade w seed d S n := by
    change ((grade (d+n)).comap (tensorCyclicSpan w seed).subtype).map
      (S.mkQ.comp (tensorCyclicSpan w seed).subtype) = _
    rw [Submodule.map_comp, Submodule.map_comap_subtype]
    rfl
  have h := (tensorCyclicGrading w hw seed).vacuum_grade_map
    (quotientAnnihilate w hw S hS) (quotientCreate w hw S hS) f
    (fun _ _ => rfl) (fun _ _ => rfl) (d+n) (shiftedQuotientCyclicGrade w seed d S n) hmap
  change (shiftedTensorVacuumGrade w hw seed d n).map f = _ at h
  dsimp [f] at h
  rw [Submodule.map_comp, shiftedTensorVacuumGrade_map w hw seed d n] at h
  exact h

theorem shiftedQuotientCyclicGrade_vacuum_eq_firstWordSpan (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (hv : seed ∈ heisenbergVacuum w)
    (hd : seed ∈ grade d) (S : Submodule K (Space K))
    (hS : ChevalleyStable w S) (n : ℕ) :
    (firstWordSpan w seed (-(n:ℤ))).map S.mkQ =
      shiftedQuotientCyclicGrade w seed d S n ⊓ vacuum (quotientAnnihilate w hw S hS) := by
  rw [← shiftedQuotientCyclicGrade_vacuum_eq w hw seed d S hS n,
    tensorCyclicSpan_inf_vacuum_eq_zCyclicSpan w hw seed hv,
    zCyclicSpan_inf_grade_eq_firstWordSpan w hw seed d (d+n) hd]
  congr 2
  omega

theorem shiftedQuotientCyclicGrade_vacuum_finite (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (hv : seed ∈ heisenbergVacuum w)
    (hd : seed ∈ grade d) (S : Submodule K (Space K))
    (hS : ChevalleyStable w S) (n : ℕ)
    [Module.Finite K (firstWordSpan w seed (-(n:ℤ)))] :
    Module.Finite K (shiftedQuotientCyclicGrade w seed d S n ⊓
      vacuum (quotientAnnihilate w hw S hS) : Submodule K (Space K ⧸ S)) := by
  rw [← shiftedQuotientCyclicGrade_vacuum_eq_firstWordSpan w hw seed d hv hd S hS n]
  infer_instance

theorem shiftedQuotientCyclicGrade_vacuum_finrank_le_firstWordSpan
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K) (d : ℤ)
    (hv : seed ∈ heisenbergVacuum w) (hd : seed ∈ grade d)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : ℕ)
    [Module.Finite K (firstWordSpan w seed (-(n:ℤ)))] :
    Module.finrank K (shiftedQuotientCyclicGrade w seed d S n ⊓
      vacuum (quotientAnnihilate w hw S hS) : Submodule K (Space K ⧸ S)) ≤
      Module.finrank K (firstWordSpan w seed (-(n:ℤ))) := by
  rw [← shiftedQuotientCyclicGrade_vacuum_eq_firstWordSpan w hw seed d hv hd S hS n]
  exact Submodule.finrank_map_le _ _

theorem shiftedQuotientCyclicGrade_vacuum_finrank_le_bound
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K) (d : ℤ)
    (hv : seed ∈ heisenbergVacuum w) (hd : seed ∈ grade d)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n B : ℕ)
    [Module.Finite K (firstWordSpan w seed (-(n:ℤ)))]
    (hB : Module.finrank K (firstWordSpan w seed (-(n:ℤ))) ≤ B) :
    Module.finrank K (shiftedQuotientCyclicGrade w seed d S n ⊓
      vacuum (quotientAnnihilate w hw S hS) : Submodule K (Space K ⧸ S)) ≤ B :=
  (shiftedQuotientCyclicGrade_vacuum_finrank_le_firstWordSpan w hw seed d hv hd S hS n).trans hB

theorem shiftedQuotientCyclicGrade_principalVacuum_finrank_le_bound
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K) (d : ℤ)
    (hv : seed ∈ heisenbergVacuum w) (hd : seed ∈ grade d)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n B : ℕ)
    [Module.Finite K (firstWordSpan w seed (-(n:ℤ)))]
    (hB : Module.finrank K (firstWordSpan w seed (-(n:ℤ))) ≤ B) :
    Module.finrank K (shiftedQuotientCyclicGrade w seed d S n ⊓
      vacuum (fun m : Mode => quotientHeisenberg w hw S hS m.val) :
      Submodule K (Space K ⧸ S)) ≤ B := by
  rw [quotientHeisenberg_vacuum_eq]
  exact shiftedQuotientCyclicGrade_vacuum_finrank_le_bound w hw seed d hv hd S hS n B hB

end KanadeRussell.Tsuchioka.Fock
