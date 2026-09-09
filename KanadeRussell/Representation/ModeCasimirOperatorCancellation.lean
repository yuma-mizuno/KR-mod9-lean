import KanadeRussell.Representation.ModeCasimirCancellation

/-! Lifting the finite structure-coefficient cancellation to actual operators. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem tensorModeStructure_central_zero (w : K) (a b : ℤ) (hab : a+b ≠ 0)
    (r t : Fin 3) : tensorModeStructure w a b r.castSucc t.castSucc 3 = 0 := by
  fin_cases r <;> fin_cases t <;>
    norm_num [tensorModeStructure, normalizeTensorCoordinates, tensorModeRawStructure,
      Fin.castSucc_mk, Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, hab]

theorem tensorModeEvaluate_eq_sum_principalMode (w : K) (a : ℤ)
    (v : Fin 4 → K) (hv : v 3 = 0) :
    tensorModeEvaluate w a v = ∑ r : Fin 3, v r.castSucc • principalMode w a r := by
  rw [tensorModeEvaluate_apply, hv]
  simp [Fin.sum_univ_three, principalMode, tensorModeBasis, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail]

theorem principalMode_lie_noncentral (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (hab : a+b ≠ 0) (r t : Fin 3) :
    ⁅principalMode w a r, principalMode w b t⁆ =
      ∑ s : Fin 3, tensorModeStructure w a b r.castSucc t.castSucc s.castSucc •
        principalMode w (a+b) s := by
  calc
    ⁅principalMode w a r, principalMode w b t⁆ =
      tensorModeEvaluate w (a+b) (tensorModeStructure w a b r.castSucc t.castSucc) :=
        tensorModeBasis_lie w hw a b r.castSucc t.castSucc
    _ = _ := tensorModeEvaluate_eq_sum_principalMode w (a+b) _
      (tensorModeStructure_central_zero w a b hab r t)

theorem chevalleyF_eq_sum_principalMode (w : K) (i : Fin 3) :
    chevalleyF w i = ∑ t : Fin 3, chevalleyFCoordinates w i t.castSucc •
      principalMode w (-1) t := by
  apply tensorModeEvaluate_eq_sum_principalMode
  fin_cases i <;> norm_num [chevalleyFCoordinates, Matrix.cons_val_three]

noncomputable def modeCasimirBulkLinear (w : K) (n : ℤ) :
    Module.End K (Space K) →ₗ[K] Module.End K (Space K) where
  toFun F :=
    (∑ r : Fin 3, (modePairingCoefficient w (n+1) r)⁻¹ •
      (principalMode w (-(n+1)) r * ⁅principalMode w (n+1) r, F⁆)) +
    (∑ s : Fin 3, (modePairingCoefficient w n s)⁻¹ •
      (⁅principalMode w (-n) s, F⁆ * principalMode w n s))
  map_add' F G := by
    simp only [Ring.lie_def, mul_add, add_mul, mul_sub, sub_mul, smul_sub, smul_add,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    module
  map_smul' c F := by
    simp only [Ring.lie_def, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub,
      smul_add, Finset.smul_sum, smul_smul, RingHom.id_apply, mul_comm c]

theorem modeCasimirBulkLinear_basis (w : K) (hw : w^4-w^2+1=0)
    (n : ℤ) (hn : 1 ≤ n) (t : Fin 3) :
    modeCasimirBulkLinear w n (principalMode w (-1) t) = 0 := by
  have hp (r : Fin 3) : ⁅principalMode w (n+1) r, principalMode w (-1) t⁆ =
      ∑ s : Fin 3, tensorModeStructure w (n+1) (-1) r.castSucc t.castSucc s.castSucc •
        principalMode w n s := by
    simpa only [show n+1+(-1)=n by omega] using
      principalMode_lie_noncentral w hw (n+1) (-1) (by omega) r t
  have hm (s : Fin 3) : ⁅principalMode w (-n) s, principalMode w (-1) t⁆ =
      ∑ r : Fin 3, tensorModeStructure w (-n) (-1) s.castSucc t.castSucc r.castSucc •
        principalMode w (-(n+1)) r := by
    simpa only [show -n+(-1)=-(n+1) by omega] using
      principalMode_lie_noncentral w hw (-n) (-1) (by omega) s t
  change (∑ r : Fin 3, (modePairingCoefficient w (n+1) r)⁻¹ •
      (principalMode w (-(n+1)) r * ⁅principalMode w (n+1) r, principalMode w (-1) t⁆)) +
    (∑ s : Fin 3, (modePairingCoefficient w n s)⁻¹ •
      (⁅principalMode w (-n) s, principalMode w (-1) t⁆ * principalMode w n s)) = 0
  simp only [hp, hm, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  have hswap :
      (∑ s : Fin 3, ∑ r : Fin 3,
        ((modePairingCoefficient w n s)⁻¹ *
          tensorModeStructure w (-n) (-1) s.castSucc t.castSucc r.castSucc) •
            (principalMode w (-(n+1)) r * principalMode w n s)) =
      ∑ r : Fin 3, ∑ s : Fin 3,
        ((modePairingCoefficient w n s)⁻¹ *
          tensorModeStructure w (-n) (-1) s.castSucc t.castSucc r.castSucc) •
            (principalMode w (-(n+1)) r * principalMode w n s) := Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro r hr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro s hs
  rw [← add_smul, modeBulkCoefficient w hw n r s t, zero_smul]

/-- Adjacent normal-ordered principal degrees cancel for every lowering generator. -/
theorem modeCasimir_bulk_cancellation (w : K) (hw : w^4-w^2+1=0)
    (n : ℕ) (hn : 1 ≤ n) (i : Fin 3) :
    modeCasimirLower w ((n : ℤ)+1) i + modeCasimirUpper w (n : ℤ) i = 0 := by
  change modeCasimirBulkLinear w (n : ℤ) (chevalleyF w i) = 0
  rw [chevalleyF_eq_sum_principalMode, map_sum]
  apply Finset.sum_eq_zero
  intro t ht
  rw [map_smul, modeCasimirBulkLinear_basis w hw (n : ℤ) (by omega) t, smul_zero]

end KanadeRussell.Representation
