import KanadeRussell.Representation.AffineCyclicity
import KanadeRussell.Heisenberg.TensorVacuumQuotient

/-! Every Chevalley-stable quotient inherits the minimum-two vacuum bound.
Only stability under the nine Chevalley operators is an input: stability under
all Heisenberg modes and surjectivity on vacuum grades are proved. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Tsuchioka.Fock
open KanadeRussell.Heisenberg
variable {K : Type*} [Field K] [CharZero K]

/-- A submodule for the concrete affine generators; no character or vacuum
surjectivity is included in this condition. -/
def ChevalleyStable (w : K) (S : Submodule K (Space K)) : Prop :=
  (∀ i f, f ∈ S → chevalleyE w i f ∈ S) ∧
  (∀ i f, f ∈ S → chevalleyF w i f ∈ S) ∧
  (∀ i f, f ∈ S → chevalleyH w i f ∈ S)

theorem ChevalleyStable.algebra_mem {w : K} {S : Submodule K (Space K)}
    (hS : ChevalleyStable w S) (a : Module.End K (Space K))
    (ha : a ∈ chevalleyOperatorAlgebra w) : ∀ f ∈ S, a f ∈ S := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩
    · exact hS.1 i
    · exact hS.2.1 i
    · exact hS.2.2 i
  | algebraMap c =>
    intro f hf
    exact S.smul_mem c hf
  | add a b ha hb hia hib =>
    intro f hf
    exact S.add_mem (hia f hf) (hib f hf)
  | mul a b ha hb hia hib =>
    intro f hf
    exact hia _ (hib f hf)

theorem ChevalleyStable.heisenberg_mem {w : K} {S : Submodule K (Space K)}
    (hS : ChevalleyStable w S) (hw : w^4-w^2+1=0) (n : ℤ) :
    ∀ f ∈ S, heisenbergMode w n f ∈ S :=
  hS.algebra_mem _ (heisenbergMode_mem_chevalley w hw n)

theorem ChevalleyStable.annihilate_mem {w : K} {S : Submodule K (Space K)}
    (hS : ChevalleyStable w S) (hw : w^4-w^2+1=0) (n : Mode) :
    ∀ f ∈ S, (polynomialGrading (K:=K)).annihilate n f ∈ S := by
  intro f hf
  change diagonalDerivative n f ∈ S
  have h := hS.heisenberg_mem hw n.val f hf
  rw [heisenbergMode_positive,heisenbergPositive_apply] at h
  have hh := S.smul_mem (n.val * contraction w n.val / 12 : K)⁻¹ h
  simpa only [smul_smul,inv_mul_cancel₀ (heisenbergPositive_scale_ne_zero w hw n),one_smul] using hh

theorem ChevalleyStable.create_mem {w : K} {S : Submodule K (Space K)}
    (hS : ChevalleyStable w S) (hw : w^4-w^2+1=0) (n : Mode) :
    ∀ f ∈ S, (polynomialGrading (K:=K)).create n f ∈ S := by
  intro f hf
  have h := hS.heisenberg_mem hw (-(n.val:ℤ)) f hf
  rw [heisenbergMode_negative] at h
  exact S.smul_mem (1/3:K) h

noncomputable def quotientAnnihilate (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : Mode) :
    Module.End K (Space K ⧸ S) :=
  S.mapQ S ((polynomialGrading (K:=K)).annihilate n) (hS.annihilate_mem hw n)

noncomputable def quotientCreate (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : Mode) :
    Module.End K (Space K ⧸ S) :=
  S.mapQ S ((polynomialGrading (K:=K)).create n) (hS.create_mem hw n)

/-- The degree-n image of the actual tensor cyclic module in the ambient quotient. -/
noncomputable def quotientCyclicGrade (w : K) (S : Submodule K (Space K)) (n : ℕ) :
    Submodule K (Space K ⧸ S) :=
  (tensorCyclicSpan w 1 ⊓ grade (n:ℤ)).map S.mkQ

/-- A standard highest-weight quotient is one possible application. The theorem
itself applies to every Chevalley-stable quotient, with no character premise. -/
theorem quotientCyclicGrade_vacuum_finrank_le_count (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : ℕ) :
    Module.finrank K (quotientCyclicGrade w S n ⊓ vacuum (quotientAnnihilate w hw S hS) : Submodule K (Space K ⧸ S)) ≤
      Partitions.count 2 n := by
  let f : tensorCyclicSpan w (1 : Space K) →ₗ[K] (Space K ⧸ S) :=
    S.mkQ.comp (tensorCyclicSpan w 1).subtype
  apply quotient_vacuum_finrank_le_count w hw (quotientAnnihilate w hw S hS)
    (quotientCreate w hw S hS) f
  · intro i v
    rfl
  · intro i v
    rfl
  · change ((grade (n:ℤ)).comap (tensorCyclicSpan w 1).subtype).map
      (S.mkQ.comp (tensorCyclicSpan w 1).subtype) = _
    rw [Submodule.map_comp,Submodule.map_comap_subtype]
    rfl

/-- Vacuum lifting identifies the quotient vacuum with the image of the concrete
cyclic vacuum in exactly the same degree. -/
theorem quotientCyclicGrade_vacuum_eq (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : ℕ) :
    (((tensorCyclicSpan w 1 ⊓ heisenbergVacuum w) ⊓ grade (n:ℤ)).map S.mkQ) =
      quotientCyclicGrade w S n ⊓ vacuum (quotientAnnihilate w hw S hS) := by
  let f : tensorCyclicSpan w (1 : Space K) →ₗ[K] (Space K ⧸ S) :=
    S.mkQ.comp (tensorCyclicSpan w 1).subtype
  have hmap : ((tensorCyclicGrading w hw 1).grade n).map f = quotientCyclicGrade w S n := by
    change ((grade (n:ℤ)).comap (tensorCyclicSpan w 1).subtype).map
      (S.mkQ.comp (tensorCyclicSpan w 1).subtype) = _
    rw [Submodule.map_comp,Submodule.map_comap_subtype]
    rfl
  have h := (tensorCyclicGrading w hw 1).vacuum_grade_map
    (quotientAnnihilate w hw S hS) (quotientCreate w hw S hS) f
    (fun _ _ => rfl) (fun _ _ => rfl) n (quotientCyclicGrade w S n) hmap
  change (tensorVacuumGrade w hw n).map f = _ at h
  dsimp [f] at h
  rw [Submodule.map_comp,tensorVacuumGrade_map w hw n] at h
  exact h

/-- The original, unnormalized principal Heisenberg modes descend as well. -/
noncomputable def quotientHeisenberg (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : ℤ) :
    Module.End K (Space K ⧸ S) :=
  S.mapQ S (heisenbergMode w n) (hS.heisenberg_mem hw n)

theorem quotientHeisenberg_positive (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : Mode) :
    quotientHeisenberg w hw S hS n.val =
      (n.val * contraction w n.val / 12 : K) • quotientAnnihilate w hw S hS n := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ f =>
    change S.mkQ (heisenbergMode w n.val f) =
      (n.val * contraction w n.val / 12 : K) • S.mkQ (diagonalDerivative n f)
    rw [heisenbergMode_positive,heisenbergPositive_apply,map_smul]

/-- Normalizing the oscillators does not change the quotient vacuum. -/
theorem quotientHeisenberg_vacuum_eq (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) :
    vacuum (fun n : Mode => quotientHeisenberg w hw S hS n.val) =
      vacuum (quotientAnnihilate w hw S hS) := by
  ext v
  simp only [mem_vacuum,quotientHeisenberg_positive,LinearMap.smul_apply]
  constructor
  · intro h n
    exact (smul_eq_zero.mp (h n)).resolve_left (heisenbergPositive_scale_ne_zero w hw n)
  · intro h n
    rw [h n,smul_zero]

theorem quotientCyclicGrade_vacuum_finite (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : ℕ) :
    Module.Finite K (quotientCyclicGrade w S n ⊓ vacuum (quotientAnnihilate w hw S hS) :
      Submodule K (Space K ⧸ S)) := by
  letI := tensorCyclicSpan_vacuum_grade_finite w hw n
  rw [← quotientCyclicGrade_vacuum_eq w hw S hS n]
  infer_instance

/-- The count bound is for the original principal Heisenberg vacuum. -/
theorem quotientCyclicGrade_principalVacuum_finrank_le_count (w : K) (hw : w^4-w^2+1=0)
    (S : Submodule K (Space K)) (hS : ChevalleyStable w S) (n : ℕ) :
    Module.finrank K (quotientCyclicGrade w S n ⊓
      vacuum (fun m : Mode => quotientHeisenberg w hw S hS m.val) :
      Submodule K (Space K ⧸ S)) ≤ Partitions.count 2 n := by
  rw [quotientHeisenberg_vacuum_eq]
  exact quotientCyclicGrade_vacuum_finrank_le_count w hw S hS n

end KanadeRussell.Tsuchioka.Fock
