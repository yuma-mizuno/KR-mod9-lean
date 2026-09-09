import KanadeRussell.Representation.WeightSpanning
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Algebra.DirectSum.Module

/-! Independence of actual joint eigenspaces and internal cyclic weight decompositions. -/
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace KanadeRussell.Representation
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Simultaneous ordinary eigenspaces are independent for any family of operators.
No commutativity or finite-dimensionality is needed for independence. -/
theorem iSupIndep_joint_eigenspaces (H : ι → Module.End K V) :
    iSupIndep (fun mu : ι → K => ⨅ i, (H i).eigenspace (mu i)) :=
  iSupIndep.iInf (fun i mu => (H i).eigenspace mu) (fun i => (H i).eigenspaces_iSupIndep)

/-- Pulling an independent family back to a submodule preserves independence. -/
theorem iSupIndep_comap_subtype {A : ι → Submodule K V} (hA : iSupIndep A)
    (S : Submodule K V) : iSupIndep (fun i => (A i).comap S.subtype) := by
  have hi : iSupIndep (fun i => S ⊓ A i) := hA.mono (fun _ => inf_le_right)
  let e : Submodule K S ≃o Set.Iic S := S.mapIic
  have he : (e ∘ fun i => (A i).comap S.subtype) =
      fun i => (⟨S ⊓ A i, show S ⊓ A i ≤ S from inf_le_left⟩ : Set.Iic S) := by
    ext i v
    change v ∈ ((A i).comap S.subtype).map S.subtype ↔ _
    rw [Submodule.map_comap_subtype]
  rw [← iSupIndep_map_orderIso_iff e, he]
  exact iSupIndep.of_coe_Iic_comp hi

end KanadeRussell.Representation

namespace KanadeRussell.Tsuchioka.Fock
open KanadeRussell.Representation
variable {K : Type*} [Field K] [CharZero K]

theorem jointWeightSpace_iSupIndep (w : K) : iSupIndep (jointWeightSpace (K := K) w) := by
  change iSupIndep (fun mu : Fin 3 → K => ⨅ i, LinearMap.ker (chevalleyH w i - mu i • 1))
  simpa only [Module.End.eigenspace_def] using
    iSupIndep_joint_eigenspaces (chevalleyH (K := K) w)

theorem jointWeightSpace_inf_iSupIndep (w : K) (S : Submodule K (Space K)) :
    iSupIndep (fun mu : Fin 3 → K => S ⊓ jointWeightSpace w mu) :=
  (jointWeightSpace_iSupIndep w).mono (fun _ => inf_le_right)

theorem jointWeightSpace_comap_iSupIndep (w : K) (S : Submodule K (Space K)) :
    iSupIndep (fun mu : Fin 3 → K => (jointWeightSpace w mu).comap S.subtype) :=
  iSupIndep_comap_subtype (jointWeightSpace_iSupIndep w) S

/-- The actual restrictions of the joint eigenspaces form an internal direct sum
whenever their intersections span S. -/
theorem jointWeightSpace_isInternal (w : K) (S : Submodule K (Space K))
    (hS : S = ⨆ mu : Fin 3 → K, S ⊓ jointWeightSpace w mu) :
    DirectSum.IsInternal (fun mu : Fin 3 → K => (jointWeightSpace w mu).comap S.subtype) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (jointWeightSpace_comap_iSupIndep w S)
  apply Submodule.map_injective_of_injective S.subtype_injective
  rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
  simpa only [Submodule.map_comap_subtype] using hS.symm

theorem chevalleyCyclicSpan_jointWeightSpace_isInternal (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (mu : Fin 3 → K) (hseed : ∀ i, chevalleyH w i seed = mu i • seed) :
    DirectSum.IsInternal (fun nu : Fin 3 → K =>
      (jointWeightSpace w nu).comap (chevalleyCyclicSpan w seed).subtype) :=
  jointWeightSpace_isInternal w _
    (chevalleyCyclicSpan_eq_iSup_jointWeightSpace w hw seed mu hseed)

theorem tensorCyclicSpan_jointWeightSpace_isInternal (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (hd : seed ∈ grade d)
    (mu : Fin 3 → K) (hseed : ∀ i, chevalleyH w i seed = mu i • seed) :
    DirectSum.IsInternal (fun nu : Fin 3 → K =>
      (jointWeightSpace w nu).comap (tensorCyclicSpan w seed).subtype) :=
  jointWeightSpace_isInternal w _
    (tensorCyclicSpan_eq_iSup_jointWeightSpace w hw seed d hd mu hseed)

theorem vacuum_tensor_weight_isInternal (w : K) (hw : w^4-w^2+1=0) :
    DirectSum.IsInternal (fun mu : Fin 3 → K =>
      (jointWeightSpace w mu).comap (tensorCyclicSpan w (1 : Space K)).subtype) :=
  jointWeightSpace_isInternal w _ (vacuum_tensor_jointWeightSpace_spanning w hw)

theorem skew_tensor_weight_isInternal (w : K) (hw : w^4-w^2+1=0) :
    DirectSum.IsInternal (fun mu : Fin 3 → K =>
      (jointWeightSpace w mu).comap (tensorCyclicSpan w (Sectors.skewSeed : Space K)).subtype) :=
  jointWeightSpace_isInternal w _ (skew_tensor_jointWeightSpace_spanning w hw)

theorem alternating_tensor_weight_isInternal (w : K) (hw : w^4-w^2+1=0) :
    DirectSum.IsInternal (fun mu : Fin 3 → K =>
      (jointWeightSpace w mu).comap (tensorCyclicSpan w (alternatingSeed : Space K)).subtype) :=
  jointWeightSpace_isInternal w _ (alternating_tensor_jointWeightSpace_spanning w hw)

end KanadeRussell.Tsuchioka.Fock
