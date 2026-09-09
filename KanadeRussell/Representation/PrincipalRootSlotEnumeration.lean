import KanadeRussell.Representation.PrincipalModeEigenframe
import KanadeRussell.Representation.PositivePrincipalModes

/-! The 28 active principal-root slots in one period, with multiplicities
retained even when two slots have the same root occupation. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
open AffineWeightLattice

def principalRootBaseResidue : Fin 28 → Fin 12 := ![0,0,0,1,1,2,2,3,3,4,4,4,5,5,6,6,6,7,7,8,8,9,9,10,10,10,11,11]
def principalRootBaseIndex : Fin 28 → Fin 3 := ![0,1,2,0,1,0,1,0,1,0,1,2,0,1,0,1,2,0,1,0,1,0,1,0,1,2,0,1]
def principalRootBase (j : Fin 28) : RootCoefficients := fun i =>
  (![principalWeightOccupation0,principalWeightOccupation1,principalWeightOccupation2,principalWeightOccupation3,principalWeightOccupation4,principalWeightOccupation5,principalWeightOccupation6,principalWeightOccupation7,principalWeightOccupation8,principalWeightOccupation9,principalWeightOccupation10,principalWeightOccupation11,principalWeightOccupation12,principalWeightOccupation13,principalWeightOccupation14,principalWeightOccupation15,principalWeightOccupation16,principalWeightOccupation17,principalWeightOccupation18,principalWeightOccupation19,principalWeightOccupation20,principalWeightOccupation21,principalWeightOccupation22,principalWeightOccupation23,principalWeightOccupation24,principalWeightOccupation25,principalWeightOccupation26,principalWeightOccupation27] j i : ℤ)

theorem principalRootBase_active (j : Fin 28) :
    principalWeightSlotActive (principalRootBaseResidue j) (principalRootBaseIndex j) := by
  revert j
  decide

noncomputable def principalRootBaseEquiv :
    Fin 28 ≃ {p : Fin 12 × Fin 3 // principalWeightSlotActive p.1 p.2} :=
  Equiv.ofBijective (fun j => ⟨(principalRootBaseResidue j,principalRootBaseIndex j),
    principalRootBase_active j⟩) (by decide)

@[simp] theorem principalRootBaseEquiv_val (j : Fin 28) :
    (principalRootBaseEquiv j).val = (principalRootBaseResidue j,principalRootBaseIndex j) := rfl

theorem principalRootBase_eq_occupation (j : Fin 28) :
    principalRootBase j = fun i =>
      (principalWeightOccupation (principalRootBaseResidue j) (principalRootBaseIndex j) i : ℤ) := by
  revert j
  decide

def principalRootSlotOccupation (p : ℕ × Fin 28) : RootCoefficients :=
  principalRootBase p.2 + (p.1:ℤ) • (![3,6,3] : RootCoefficients)

private theorem residue_period (q : ℕ) (n : Fin 12) :
    positiveModeResidue (12*q+n.val) = n := by
  apply Fin.ext
  simp only [positiveModeResidue]
  omega

private def activePeriodicEquiv :
    (ℕ × {p : Fin 12 × Fin 3 // principalWeightSlotActive p.1 p.2}) ≃
      {p : ℕ × Fin 3 // principalWeightSlotActive (positiveModeResidue p.1) p.2} where
  toFun p := ⟨(12*p.1+p.2.val.1.val,p.2.val.2), by rw [residue_period]; exact p.2.property⟩
  invFun p := (p.val.1/12,⟨(positiveModeResidue p.val.1,p.val.2),p.property⟩)
  left_inv p := by
    apply Prod.ext
    · change (12*p.1+p.2.val.1.val)/12 = p.1
      omega
    · apply Subtype.ext
      exact Prod.ext (residue_period p.1 p.2.val.1) rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change 12*(p.val.1/12)+p.val.1%12=p.val.1
      omega
    · rfl

noncomputable def principalRootSlotEquiv : (ℕ × Fin 28) ≃
    {p : ℕ × Fin 3 // principalWeightSlotActive (positiveModeResidue p.1) p.2} :=
  (Equiv.prodCongr (Equiv.refl ℕ) principalRootBaseEquiv).trans activePeriodicEquiv

@[simp] theorem principalRootSlotEquiv_val (p : ℕ × Fin 28) :
    (principalRootSlotEquiv p).val =
      (12*p.1+(principalRootBaseResidue p.2).val,principalRootBaseIndex p.2) := rfl

theorem principalRootSlotOccupation_eq_positive (p : ℕ × Fin 28) :
    principalRootSlotOccupation p =
      positiveModeOccupation (principalRootSlotEquiv p).val.1 (principalRootSlotEquiv p).val.2 := by
  rw [principalRootSlotEquiv_val]
  have hd : (12*p.1+(principalRootBaseResidue p.2).val)/12=p.1 := by
    have h := (principalRootBaseResidue p.2).isLt
    omega
  funext i
  simp only [principalRootSlotOccupation, positiveModeOccupation, principalRootBase_eq_occupation,
    residue_period, hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end KanadeRussell.Representation
