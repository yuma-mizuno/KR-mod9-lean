import KanadeRussell.Representation.PrincipalModePairing
import KanadeRussell.Representation.AffineWeightLattice

/-! The degree-one pairing is dual to the actual Chevalley coordinates with
squared-root normalization (1,1,3). Its normal-ordering boundary is computed
from the proved EF relations, without assuming a pairing normalization. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace KanadeRussell.Representation
open Tsuchioka.Fock AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

private def boundaryPairing (w : K) : Fin 3 → K :=
  ![-Tsuchioka.Scalar.cPrime w / 18, -Tsuchioka.Scalar.cPrime (-w) / 18,
    (-w^3/6+w/3+1/2)/3]

private theorem cs0 : (0:Fin 3).castSucc = (0:Fin 4) := rfl
private theorem cs1 : (1:Fin 3).castSucc = (1:Fin 4) := rfl
private theorem cs2 : (2:Fin 3).castSucc = (2:Fin 4) := rfl

private theorem boundary_chevalley_pairing (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    (∑ r : Fin 3, boundaryPairing w r * chevalleyECoordinates w i r.castSucc *
      chevalleyFCoordinates w j r.castSucc) =
    if i=j then (symmetrizer i : K)⁻¹ else 0 := by
  simp only [Fin.sum_univ_three, cs0, cs1, cs2]
  fin_cases i <;> fin_cases j <;>
    norm_num [boundaryPairing, chevalleyECoordinates, chevalleyFCoordinates,
      symmetrizer, Tsuchioka.Scalar.cPrime, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

private theorem boundary_dual_product (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) (s : Fin 4) :
    boundaryPairing w r *
      (∑ i : Fin 3, (symmetrizer i : K) * chevalleyFCoordinates w i r.castSucc *
        chevalleyECoordinates w i s) = if r.castSucc=s then 1 else 0 := by
  fin_cases r <;> fin_cases s <;>
    norm_num [boundaryPairing, chevalleyECoordinates, chevalleyFCoordinates,
      symmetrizer, Tsuchioka.Scalar.cPrime, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

private theorem boundary_dual (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) (s : Fin 4) :
    (∑ i : Fin 3, (symmetrizer i : K) * chevalleyFCoordinates w i r.castSucc *
      chevalleyECoordinates w i s) = if r.castSucc=s then (boundaryPairing w r)⁻¹ else 0 := by
  have hn : boundaryPairing w r ≠ 0 := by
    intro hz
    have h := boundary_dual_product w hw r r.castSucc
    rw [hz, zero_mul, if_pos rfl] at h
    exact zero_ne_one h
  have h := boundary_dual_product w hw r s
  calc
    _ = (boundaryPairing w r)⁻¹ * (boundaryPairing w r *
      (∑ i : Fin 3, (symmetrizer i : K) * chevalleyFCoordinates w i r.castSucc *
        chevalleyECoordinates w i s)) := by rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ = _ := by rw [h]; split <;> simp_all

private theorem boundaryPairing_eq (w : K) (hw : w^4-w^2+1=0) :
    boundaryPairing w = modePairingCoefficient w 1 := by
  funext r
  fin_cases r <;>
    norm_num [boundaryPairing, modePairingCoefficient, tensorHeisenbergPairing,
      IsMode, contraction_one w hw]

theorem modePairing_chevalley_one (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    (∑ r : Fin 3, modePairingCoefficient w 1 r * chevalleyECoordinates w i r.castSucc *
      chevalleyFCoordinates w j r.castSucc) =
    if i=j then (symmetrizer i : K)⁻¹ else 0 := by
  rw [← boundaryPairing_eq w hw]
  exact boundary_chevalley_pairing w hw i j

private theorem principalMode_one_dual (w : K) (hw : w^4-w^2+1=0) (r : Fin 3) :
    (modePairingCoefficient w 1 r)⁻¹ • principalMode w 1 r =
      ∑ i : Fin 3, ((symmetrizer i : K) * chevalleyFCoordinates w i r.castSucc) • chevalleyE w i := by
  have hc : (∑ i : Fin 3, ((symmetrizer i : K) * chevalleyFCoordinates w i r.castSucc) •
      chevalleyECoordinates w i) = (boundaryPairing w r)⁻¹ • Pi.single r.castSucc 1 := by
    funext s
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [boundary_dual w hw r s]
    by_cases h : r.castSucc=s <;> simp [Pi.single_apply, h, Ne.symm]
  have he := congrArg (tensorModeEvaluate w 1) hc
  simp only [map_sum, map_smul] at he
  have hb : tensorModeEvaluate w 1 (Pi.single r.castSucc 1) = principalMode w 1 r := by
    simp [tensorModeEvaluate, principalMode, Pi.single_apply]
  rw [hb, boundaryPairing_eq w hw] at he
  simpa only [chevalleyE] using he.symm

private theorem principalMode_one_bracket_dual (w : K) (hw : w^4-w^2+1=0) (r i : Fin 3) :
    (modePairingCoefficient w 1 r)⁻¹ • ⁅principalMode w 1 r, chevalleyF w i⁆ =
      ((symmetrizer i : K) * chevalleyFCoordinates w i r.castSucc) • chevalleyH w i := by
  have h := congrArg (fun a : Module.End K (Space K) => ⁅a,chevalleyF w i⁆)
    (principalMode_one_dual w hw r)
  have hs (c : K) (a b : Module.End K (Space K)) : ⁅c • a,b⁆ = c • ⁅a,b⁆ := by
    simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_sub]
  simpa only [hs, sum_lie, chevalley_EF w hw, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

private theorem chevalleyF_principalModes (w : K) (i : Fin 3) :
    (∑ r : Fin 3, chevalleyFCoordinates w i r.castSucc • principalMode w (-1) r) = chevalleyF w i := by
  simp only [Fin.sum_univ_three, cs0, cs1, cs2, principalMode]
  fin_cases i <;>
    simp [chevalleyF, tensorModeEvaluate_apply, tensorModeBasis, chevalleyFCoordinates,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.castSucc, Matrix.cons_val_zero']

theorem modeCasimirLower_one (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    modeCasimirLower w 1 i = (symmetrizer i : K) • (chevalleyF w i * chevalleyH w i) := by
  unfold modeCasimirLower
  calc
    _ = ∑ r : Fin 3, principalMode w (-1) r *
        (((symmetrizer i : K) * chevalleyFCoordinates w i r.castSucc) • chevalleyH w i) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← mul_smul_comm, principalMode_one_bracket_dual w hw r i]
    _ = (symmetrizer i : K) •
        ((∑ r : Fin 3, chevalleyFCoordinates w i r.castSucc • principalMode w (-1) r) * chevalleyH w i) := by
      simp only [Finset.sum_mul, Finset.smul_sum, mul_smul_comm, smul_mul_assoc, smul_smul]
    _ = _ := by rw [chevalleyF_principalModes]

end KanadeRussell.Representation
