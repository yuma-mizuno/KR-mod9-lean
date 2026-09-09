import KanadeRussell.Representation.PrincipalRootEulerProduct

/-! The coefficient-stabilized root Euler product with one simple root omitted. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
variable {K : Type*} [Field K]

noncomputable def principalRootComplementFactor (i : Fin 3) (n : ℕ) (r : Fin 3) :
    MvPowerSeries (Fin 3) K :=
  if n = 0 ∧ r = i then 1 else principalRootEulerFactor n r

noncomputable def principalRootComplementPartial (i : Fin 3) (B : ℕ) :
    MvPowerSeries (Fin 3) K :=
  ∏ n ∈ Finset.range B, ∏ r : Fin 3, principalRootComplementFactor i n r

theorem principalRootComplementFactor_agree_one (i : Fin 3) (e : Fin 3 →₀ ℕ)
    (n : ℕ) (r : Fin 3) (hn : rootExponentDegree e ≤ n) :
    RootCoeffAgree e (principalRootComplementFactor (K := K) i n r) 1 := by
  classical
  unfold principalRootComplementFactor
  split_ifs
  · exact RootCoeffAgree.refl _
  · exact principalRootEulerFactor_agree_one e n r hn

theorem principalRootComplementPartial_agree (i : Fin 3) (e : Fin 3 →₀ ℕ) (A B : ℕ)
    (hA : rootExponentDegree e ≤ A) (hAB : A ≤ B) :
    RootCoeffAgree e (principalRootComplementPartial (K := K) i B)
      (principalRootComplementPartial i A) := by
  induction B, hAB using Nat.le_induction with
  | base => exact RootCoeffAgree.refl _
  | @succ B hAB ih =>
    unfold principalRootComplementPartial at *
    rw [Finset.prod_range_succ]
    have hblock : RootCoeffAgree e
        (∏ r : Fin 3, principalRootComplementFactor (K := K) i B r) 1 := by
      simpa using RootCoeffAgree.prod (Finset.univ : Finset (Fin 3))
        (fun r _ => principalRootComplementFactor_agree_one i e B r (hA.trans hAB))
    simpa using ih.mul hblock

noncomputable def principalRootComplementEuler (i : Fin 3) : MvPowerSeries (Fin 3) K :=
  fun e => MvPowerSeries.coeff e
    (principalRootComplementPartial (K := K) i (rootExponentDegree e))

theorem coeff_principalRootComplementEuler (i : Fin 3) (e : Fin 3 →₀ ℕ) (B : ℕ)
    (hB : rootExponentDegree e ≤ B) :
    MvPowerSeries.coeff e (principalRootComplementEuler (K := K) i) =
      MvPowerSeries.coeff e (principalRootComplementPartial i B) :=
  (principalRootComplementPartial_agree i e (rootExponentDegree e) B
    le_rfl hB e le_rfl).symm

theorem principalRootComplementEuler_agree (i : Fin 3) (e : Fin 3 →₀ ℕ) (B : ℕ)
    (hB : rootExponentDegree e ≤ B) :
    RootCoeffAgree e (principalRootComplementEuler (K := K) i)
      (principalRootComplementPartial i B) :=
  fun d hd => coeff_principalRootComplementEuler i d B ((rootExponentDegree_mono hd).trans hB)

@[simp] theorem constantCoeff_principalRootComplementEuler (i : Fin 3) :
    MvPowerSeries.constantCoeff (principalRootComplementEuler (K := K) i) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_principalRootComplementEuler i 0 0 (by simp)]
  simp [principalRootComplementPartial]

end KanadeRussell.Representation
