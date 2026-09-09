import KanadeRussell.Representation.ChevalleyInverse
import KanadeRussell.Tsuchioka.TensorCyclicity

/-! Common kernels of the three actual raising operators are killed by all
positive principal modes. Only positive-mode commutators are used. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
open RootData (simpleRoot rootWeight)
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private theorem bracket_kills {x y : Module.End K (Space K)} {v : Space K}
    (hx : x v=0) (hy : y v=0) : ⁅x,y⁆ v=0 := by
  simp [Ring.lie_def, Module.End.mul_apply, hx, hy]

theorem positive_basis_one_kills (w : K) (hw : w^4-w^2+1=0)
    (v : Space K) (hv : ∀ i, chevalleyE w i v=0) (i : Fin 3) :
    tensorModeBasis w 1 i.castSucc v=0 := by
  rw [← chevalleyE_inverse w hw i]
  simp [LinearMap.sum_apply, LinearMap.smul_apply, hv]

private theorem positive_shift_scalar_ne_zero (w : K) (hw : w^4-w^2+1=0) (r : Fin 2) :
    contraction w 1 * rootWeight (w ^ (-1:ℤ)) (simpleRoot r.castSucc.castSucc) ≠ 0 := by
  apply mul_ne_zero (contraction_ne_zero w hw ⟨1,by decide⟩)
  fin_cases r <;>
    norm_num [Scalar.zpow_phasePolynomial w hw, Scalar.phasePolynomial,
      RootData.rootWeight_second]; intro hz; grind only

theorem positive_simple_tensor_mode_kills (w : K) (hw : w^4-w^2+1=0)
    (v : Space K) (hv : ∀ i, chevalleyE w i v=0) (r : Fin 2)
    (n : ℤ) (hn : 0<n) : tensorRootMode w (simpleRoot r.castSucc.castSucc) n v=0 := by
  have hbase : tensorRootMode w (simpleRoot r.castSucc.castSucc) 1 v=0 := by
    fin_cases r
    · exact positive_basis_one_kills w hw v hv 0
    · exact positive_basis_one_kills w hw v hv 1
  have hH : heisenbergMode w 1 v=0 := positive_basis_one_kills w hw v hv 2
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0≤n)
  have hm : 1 ≤ m := by omega
  clear hn
  induction m, hm using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    have h := bracket_kills hH ih
    rw [heisenbergMode_tensorRootMode_lie] at h
    simp only [Int.natAbs_one, show IsMode 1 from by decide, if_true,
      LinearMap.smul_apply] at h
    have hz := (smul_eq_zero.mp h).resolve_left (positive_shift_scalar_ne_zero w hw r)
    simpa only [Nat.cast_add, Nat.cast_one] using hz

theorem positive_heisenberg_mode_kills (w : K) (hw : w^4-w^2+1=0)
    (v : Space K) (hv : ∀ i, chevalleyE w i v=0)
    (n : ℤ) (hn : 0<n) : heisenbergMode w n v=0 := by
  by_cases h1 : n=1
  · subst n; exact positive_basis_one_kills w hw v hv 2
  have ha : tensorRootMode w (simpleRoot 0) 1 v=0 := positive_basis_one_kills w hw v hv 0
  have hb := positive_simple_tensor_mode_kills w hw v hv 0 (n-1) (by omega)
  have h0 := positive_simple_tensor_mode_kills w hw v hv 0 n hn
  have h2 := positive_simple_tensor_mode_kills w hw v hv 1 n hn
  change tensorRootMode w (simpleRoot 0) (n-1) v=0 at hb
  change tensorRootMode w (simpleRoot 0) n v=0 at h0
  change tensorRootMode w (simpleRoot 1) n v=0 at h2
  have h := bracket_kills ha hb
  rw [tensorFirstRoot_lie w hw] at h
  have hn0 : n ≠ 0 := by omega
  have hsum : 1+(n-1)=n := by omega
  simp only [hsum, if_neg hn0, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, h0, h2, smul_zero,
    zero_sub, add_zero, neg_eq_zero] at h
  have hc : Scalar.cPrime w ≠ 0 := by
    intro hz
    simp only [Scalar.cPrime] at hz
    grind only
  exact (smul_eq_zero.mp h).resolve_left (div_ne_zero
    (mul_ne_zero hc (zpow_ne_zero _ (by norm_num))) (by norm_num))

end KanadeRussell.Tsuchioka.Fock
