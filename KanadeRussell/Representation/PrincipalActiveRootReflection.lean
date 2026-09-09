import KanadeRussell.Representation.PrincipalModeRootReflection

/-! Reflection of actual active principal-mode indices, with the simple root removed. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
open AffineWeightLattice

abbrev PrincipalActiveRootComplement (i : Fin 3) :=
  {p : {p : ℕ × Fin 3 // principalWeightSlotActive (positiveModeResidue p.1) p.2} //
    positiveModeOccupation p.val.1 p.val.2 ≠ Pi.single i 1}

noncomputable def principalRootComplementEquiv (i : Fin 3) :
    {p : ℕ × Fin 28 // p ≠ (0, principalRootSimpleIndex i)} ≃
      PrincipalActiveRootComplement i where
  toFun p := ⟨principalRootSlotEquiv p.val, by
    rw [← principalRootSlotOccupation_eq_positive]
    exact fun h => p.property ((principalRootSlotOccupation_eq_simple_iff i p.val).mp h)⟩
  invFun p := ⟨principalRootSlotEquiv.symm p.val, by
    intro h
    apply p.property
    have hs := (principalRootSlotOccupation_eq_simple_iff i
      (principalRootSlotEquiv.symm p.val)).mpr h
    rw [principalRootSlotOccupation_eq_positive, Equiv.apply_symm_apply] at hs
    exact hs⟩
  left_inv p := Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv p := Subtype.ext (Equiv.apply_symm_apply _ _)

noncomputable def principalActiveRootReflectionEquiv (i : Fin 3) :
    PrincipalActiveRootComplement i ≃ PrincipalActiveRootComplement i :=
  (principalRootComplementEquiv i).symm.trans
    ((principalRootSlotReflectionEquiv i).trans (principalRootComplementEquiv i))

theorem principalActiveRootReflection_occupation (i : Fin 3)
    (p : PrincipalActiveRootComplement i) :
    positiveModeOccupation (principalActiveRootReflectionEquiv i p).val.val.1
      (principalActiveRootReflectionEquiv i p).val.val.2 =
      simpleReflection 0 i (positiveModeOccupation p.val.val.1 p.val.val.2) := by
  let q := (principalRootComplementEquiv i).symm p
  change positiveModeOccupation
    (principalRootSlotEquiv (principalRootSlotReflection i q.val)).val.1
    (principalRootSlotEquiv (principalRootSlotReflection i q.val)).val.2 = _
  rw [← principalRootSlotOccupation_eq_positive,
    principalRootSlotOccupation_reflection i q.val q.property,
    principalRootSlotOccupation_eq_positive]
  have hq : principalRootSlotEquiv q.val = p.val :=
    Equiv.apply_symm_apply principalRootSlotEquiv p.val
  rw [hq]

end KanadeRussell.Representation
