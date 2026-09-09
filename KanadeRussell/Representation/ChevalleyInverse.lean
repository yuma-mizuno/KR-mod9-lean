import KanadeRussell.Tsuchioka.AffineChevalley

/-! Explicit inverse coordinate certificates: the six Chevalley generators
recover both root families and the Heisenberg modes in degrees 1 and -1. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace KanadeRussell.Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

def chevalleyEInverse (w : K) : Fin 3 → Fin 3 → K :=
  ![![-1/4, -w^3/2+w+1, w^3/2-w-3/4],
    ![-w^3/4+w^2/4, 3*w^3/2-2*w^2+w/2+1/2, -5*w^3/4+7*w^2/4-w/2-1/2],
    ![1/4, 1/2, 1/4]]

def chevalleyFInverse (w : K) : Fin 3 → Fin 3 → K :=
  ![![-w^3/18+w/9+1/6, 5*w^3/18-5*w/9-1/2, -3*w^3/2+3*w+5/2],
    ![-w^3/18+w^2/18-w/18-1/9, 5*w^3/18-5*w^2/18-w/18+2/9,
      -3*w^3/2+3*w^2/2+w/2-1],
    ![-w^3/18+w/9+1/6, -w^3/18+w/9+1/6, -w^3/6+w/3+1/2]]

theorem chevalleyE_inverse_coordinates (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    ∑ j : Fin 3, chevalleyEInverse w i j • chevalleyECoordinates w j =
      (fun r : Fin 4 => if r.val = i.val then (1 : K) else 0) := by
  funext r
  fin_cases i <;> fin_cases r <;>
    norm_num [chevalleyEInverse, chevalleyECoordinates, Fin.sum_univ_succ,
      Pi.add_apply, Pi.smul_apply, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

theorem chevalleyF_inverse_coordinates (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    ∑ j : Fin 3, chevalleyFInverse w i j • chevalleyFCoordinates w j =
      (fun r : Fin 4 => if r.val = i.val then (1 : K) else 0) := by
  funext r
  fin_cases i <;> fin_cases r <;>
    norm_num [chevalleyFInverse, chevalleyFCoordinates, Fin.sum_univ_succ,
      Pi.add_apply, Pi.smul_apply, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind only

theorem chevalleyE_inverse (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    ∑ j : Fin 3, chevalleyEInverse w i j • chevalleyE w j =
      tensorModeBasis w 1 i.castSucc := by
  have h := congrArg (tensorModeEvaluate w 1) (chevalleyE_inverse_coordinates w hw i)
  simp only [map_sum, map_smul] at h
  rw [show (∑ j : Fin 3, chevalleyEInverse w i j • chevalleyE w j) =
    tensorModeEvaluate w 1 (fun r : Fin 4 => if r.val = i.val then (1 : K) else 0) from h]
  fin_cases i <;> simp [tensorModeEvaluate_apply, tensorModeBasis]

theorem chevalleyF_inverse (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    ∑ j : Fin 3, chevalleyFInverse w i j • chevalleyF w j =
      tensorModeBasis w (-1) i.castSucc := by
  have h := congrArg (tensorModeEvaluate w (-1)) (chevalleyF_inverse_coordinates w hw i)
  simp only [map_sum, map_smul] at h
  rw [show (∑ j : Fin 3, chevalleyFInverse w i j • chevalleyF w j) =
    tensorModeEvaluate w (-1) (fun r : Fin 4 => if r.val = i.val then (1 : K) else 0) from h]
  fin_cases i <;> simp [tensorModeEvaluate_apply, tensorModeBasis]

end KanadeRussell.Tsuchioka.Fock
