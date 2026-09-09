import KanadeRussell.Representation.PrincipalModeCentralStructure
import KanadeRussell.Representation.PrincipalModeRootBracket
import KanadeRussell.Representation.NegativePrincipalModes

/-! Transport of the paired root brackets to every positive degree, retaining
the mode-dependent central term. No nondegeneracy of a dummy slot is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

noncomputable def signedFrameRootBracket (w : K) (a : ℤ) (n : Fin 12) (r : Fin 3) :
    Fin 4 → K :=
  ∑ s : Fin 3, ∑ t : Fin 3,
    (principalWeightFrame w n s r * principalDualWeightCoordinates w a n r t) •
      tensorModeStructure w a (-a) s.castSucc t.castSucc

theorem principalDualWeightCoordinates_eq_of_mod (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (hab : a%12=b%12) (n : Fin 12) (r : Fin 3) :
    principalDualWeightCoordinates w a n r = principalDualWeightCoordinates w b n r := by
  funext t
  simp only [principalDualWeightCoordinates, modePairingCoefficient_eq_of_mod w hw a b hab]

theorem signedFrameRootBracket_noncentral (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (hab : a%12=b%12) (n : Fin 12) (r u : Fin 3) :
    signedFrameRootBracket w a n r u.castSucc = signedFrameRootBracket w b n r u.castSucc := by
  simp only [signedFrameRootBracket, Finset.sum_apply, Pi.smul_apply,
    principalDualWeightCoordinates_eq_of_mod w hw a b hab,
    tensorModeStructure_opposite_noncentral_eq_of_mod w hw a b hab]

theorem signedFrameRootBracket_central_scale (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (hab : a%12=b%12) (n : Fin 12) (r : Fin 3) :
    (b : K) * signedFrameRootBracket w a n r 3 =
      (a : K) * signedFrameRootBracket w b n r 3 := by
  simp only [signedFrameRootBracket, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    principalDualWeightCoordinates_eq_of_mod w hw a b hab, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have h := tensorModeStructure_opposite_central_scale w hw a b hab s t
  linear_combination (principalWeightFrame w n s r * principalDualWeightCoordinates w b n r t) * h

theorem principalFrameRootCartan_central (w : K) (n : Fin 12) (r : Fin 3) :
    principalFrameRootCartan w n r 3 =
      if principalWeightSlotActive n r then 3*((n.val : K)+1)/4 else 0 := by
  unfold principalFrameRootCartan
  split_ifs with hr
  · have h : (∑ j : Fin 3, (principalWeightOccupation n r j : K)) = (n.val : K)+1 := by
      exact_mod_cast principalWeightOccupation_degree n r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    norm_num [Fin.sum_univ_three, chevalleyHCoordinates, Matrix.cons_val_three,
      Matrix.cons_val_two] at h ⊢
    linear_combination (3/4 : K) * h
  · rfl

noncomputable def positiveRootCartanCoordinates (w : K) (n : ℕ) (r : Fin 3) : Fin 4 → K :=
  if principalWeightSlotActive (positiveModeResidue n) r then
    ∑ j : Fin 3, ((symmetrizer j : K) * (positiveModeOccupation n r j : K)) •
      chevalleyHCoordinates w j
  else 0

theorem positiveRootCartanCoordinates_noncentral (w : K) (n : ℕ) (r u : Fin 3) :
    positiveRootCartanCoordinates w n r u.castSucc =
      principalFrameRootCartan w (positiveModeResidue n) r u.castSucc := by
  unfold positiveRootCartanCoordinates principalFrameRootCartan
  split_ifs with hr
  · fin_cases u <;>
      norm_num [Finset.sum_apply, Pi.smul_apply, Fin.sum_univ_three,
        positiveModeOccupation, symmetrizer, chevalleyHCoordinates,
        Matrix.cons_val_two, Matrix.cons_val_three, Fin.castSucc_mk] <;> ring
  · rfl

theorem positiveRootCartanCoordinates_central (w : K) (n : ℕ) (r : Fin 3) :
    positiveRootCartanCoordinates w n r 3 =
      if principalWeightSlotActive (positiveModeResidue n) r then 3*((n : K)+1)/4 else 0 := by
  unfold positiveRootCartanCoordinates
  split_ifs with hr
  · have h : (∑ j : Fin 3, (positiveModeOccupation n r j : K)) = (n : K)+1 := by
      exact_mod_cast positiveModeOccupation_degree n r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    norm_num [Fin.sum_univ_three, symmetrizer, chevalleyHCoordinates,
      Matrix.cons_val_three, Matrix.cons_val_two] at h ⊢
    linear_combination (3/4 : K) * h
  · rfl

theorem signedFrameRootBracket_positive (w : K) (hw : w^4-w^2+1=0) (n : ℕ) (r : Fin 3) :
    signedFrameRootBracket w ((n : ℤ)+1) (positiveModeResidue n) r =
      positiveRootCartanCoordinates w n r := by
  let k := positiveModeResidue n
  have hcongr : ((n : ℤ)+1)%12 = ((k.val : ℤ)+1)%12 := positiveModeResidue_congr n
  have hrep : signedFrameRootBracket w ((k.val : ℤ)+1) k r = principalFrameRootCartan w k r :=
    principalFrameRootBracket_eq_cartan w hw k r
  funext u
  obtain ⟨u, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last u
  · rw [signedFrameRootBracket_noncentral w hw _ _ hcongr, hrep]
    exact (positiveRootCartanCoordinates_noncentral w n r u).symm
  · change signedFrameRootBracket w ((n : ℤ)+1) k r 3 = positiveRootCartanCoordinates w n r 3
    have hscale := signedFrameRootBracket_central_scale w hw ((n : ℤ)+1) ((k.val : ℤ)+1)
      hcongr k r
    rw [hrep, principalFrameRootCartan_central] at hscale
    rw [positiveRootCartanCoordinates_central]
    have hk : ((k.val : K)+1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k.val
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one] at hscale
    apply mul_left_cancel₀ hk
    rw [hscale]
    dsimp only [k]
    by_cases hr : principalWeightSlotActive (positiveModeResidue n) r
    · simp only [if_pos hr]
      ring
    · simp only [if_neg hr, mul_zero]

theorem signedFrameRootBracket_evaluate (w : K) (hw : w^4-w^2+1=0)
    (a : ℤ) (n : Fin 12) (r : Fin 3) :
    ⁅principalModeCombination w a (fun t => principalWeightFrame w n t r),
      principalModeCombination w (-a) (principalDualWeightCoordinates w a n r)⁆ =
      tensorModeEvaluate w 0 (signedFrameRootBracket w a n r) := by
  have hsmul (c d : K) (A B : Module.End K (Space K)) :
      ⁅c • A, d • B⁆ = (c*d) • ⁅A,B⁆ := by
    simp only [Ring.lie_def, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      smul_smul, smul_sub]
    module
  rw [principalModeCombination_apply, principalModeCombination_apply, sum_lie_sum]
  simp only [signedFrameRootBracket, map_sum, map_smul, hsmul, principalMode,
    tensorModeBasis_lie w hw, add_neg_cancel]

/-- The actual paired brackets in every positive degree, including the central
translation of the root occupation and the vanishing inactive slot. -/
theorem positive_negativePrincipalMode_bracket (w : K) (hw : w^4-w^2+1=0)
    (n : ℕ) (r : Fin 3) :
    ⁅positivePrincipalMode w n r, negativePrincipalMode w n r⁆ =
      if principalWeightSlotActive (positiveModeResidue n) r then
        ∑ j : Fin 3, ((symmetrizer j : K) * (positiveModeOccupation n r j : K)) • chevalleyH w j
      else 0 := by
  change ⁅principalModeCombination w ((n : ℤ)+1) (principalWeightCoordinates w (positiveModeResidue n) r),
    principalModeCombination w (-((n : ℤ)+1))
      (principalDualWeightCoordinates w ((n : ℤ)+1) (positiveModeResidue n) r)⁆ = _
  rw [← principalWeightFrame_combination w ((n : ℤ)+1) (positiveModeResidue n)
    (by simpa only [Nat.cast_add, Nat.cast_one] using positiveModeResidue_congr n) r,
    signedFrameRootBracket_evaluate w hw, signedFrameRootBracket_positive w hw,
    positiveRootCartanCoordinates]
  split_ifs
  · simp only [map_sum, map_smul, chevalleyH]
  · exact map_zero _

end KanadeRussell.Representation
